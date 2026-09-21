//! Verify — which verification the check run TRUSTS without kernel-checking. Lives standalone
//! (it used to be `elaborate.Verify`; the eager Elaborator is gone). Wired from CLI flags in
//! main.zig and threaded through Context to the demand prover.
//!
//! TRUST MODEL (`--fast`): a `using` step (accelerant / model / import) may be TRUSTED — its
//! proof is NOT generated or kernel-checked; instead the word ADMITS the step (an accelerant runs
//! its own cheap acceptance; model/import α-match the cited — already-proven-elsewhere — statement
//! against the claim), the step is disclosed as accelerated, and NOTHING is cached (a later strict
//! demand redoes the full check). `by` primitives are ALWAYS kernel-checked, in every mode.
//!
//! NOT trustable: `instantiation`. `admit` is shape-only, but the whole content of a schema
//! instantiation is the body's PROOF AT THE ARGS — shape-only admit would skip the per-instance
//! proof, which is the only soundness gate (a schema need not be a universal — see #93). So
//! `[using instantiation …]` is ALWAYS strict-proved; it has no `Word` and cannot be trusted.
//!
//! `Verify.trusted` is a per-word set over the trustable `using` words; a word is trusted iff it
//! is in the set. The CLI builds it: `--fast` (all), `--fast-only W…` (allowlist), `--fast-except
//! W…` (all but). Group words (`<tactic>_all`, `engine`) expand at parse time (see `Word.parse`).

const std = @import("std");

/// A trustable `using` rule word. One variant per word (the `_quantified` variants are
/// INDEPENDENT trust units); the parser's group words (`arithmetic_all`, `engine`) expand to
/// these. Kept in sync with `InternPool.RuleStr`'s `using`-side words + the accelerant set.
pub const Word = enum {
    // engine words (`instantiation` is NOT here — it is never trustable; see the module doc)
    model,
    import,
    // accelerant tactics (base + independent _quantified)
    simplify,
    simplify_quantified,
    assoc,
    assoc_quantified,
    assoc_commut,
    assoc_commut_quantified,
    polynomial,
    polynomial_quantified,
    arithmetic,
    arithmetic_quantified,
    tautology,
    specialize,
    chain,
    extensionality,
    extensionality_quantified,

    pub const Set = std.EnumSet(Word);

    /// Every trustable word (bare `--fast` trusts all of these).
    pub fn all() Set {
        return Set.initFull();
    }

    /// The ENGINE words — the `engine` group word. (`instantiation` is NOT trustable, so the
    /// engine group is just `model` + `import`.)
    pub fn engine() Set {
        var s = Set.initEmpty();
        s.insert(.model);
        s.insert(.import);
        return s;
    }

    /// Resolve a CLI word (an individual word or a group word) into the set it names, or null if
    /// it is not a valid trust word. Group words: `engine` (the 3 engine words) and
    /// `<tactic>_all` for the six tactics that HAVE a `_quantified` variant
    /// (`arithmetic_all` == {arithmetic, arithmetic_quantified}, etc.).
    pub fn parse(name: []const u8) ?Set {
        if (std.mem.eql(u8, name, "engine")) return engine();
        // `<tactic>_all` groups a base tactic with its `_quantified` variant.
        const groups = .{ "simplify", "assoc", "assoc_commut", "polynomial", "arithmetic", "extensionality" };
        inline for (groups) |g| {
            if (std.mem.eql(u8, name, g ++ "_all")) {
                var s = Set.initEmpty();
                s.insert(@field(Word, g));
                s.insert(@field(Word, g ++ "_quantified"));
                return s;
            }
        }
        // an individual word.
        inline for (@typeInfo(Word).@"enum".fields) |f| {
            if (std.mem.eql(u8, name, f.name)) {
                var s = Set.initEmpty();
                s.insert(@field(Word, f.name));
                return s;
            }
        }
        return null;
    }
};

/// The set of `using` words TRUSTED (accelerated, cert not built). Empty = strict (the default:
/// everything kernel-checked). Populated by the CLI `--fast` parsing.
trusted: Word.Set = Word.Set.initEmpty(),
/// `--draft` mode: a WIP proof. The single coarse "work in progress" bit that author-hygiene
/// checks consult to relax — NOT rejecting a proof for a dead step (a fact it introduces but
/// never uses), etc. (Holes are allowed under `--draft` too, gated in main.) NOT a trust bypass.
draft: bool = false,
/// `--trace-facts`: print, for every fact CITATION the prover resolves, what it resolved TO —
/// the namespace (universe, or a `(model, file)` pair), the declaring site, and the statement.
/// A diagnostic for the class of bug where a citation reaches the wrong COPY of a name: two
/// theorems can share a name across theories, and a model transfer publishes a second copy of
/// its source's facts, so "which one did this step actually get?" is not answerable from the
/// source text. Written to stderr as the run proceeds; never affects the verdict.
trace_facts: bool = false,
/// `--chaos[=SEED]`: shuffle the engine's scheduling order under a fixed seed, so a run
/// explores a DIFFERENT task interleaving while staying single-threaded and reproducible.
///
/// Output is a function of (tree, roots), never of scheduling — that is the determinism
/// contract the goldens encode. This is how the contract is TESTED: check the corpus under
/// many seeds and diff. Any difference is a determinism bug (something leaked task order
/// into output), caught here without threads to confuse the diagnosis. Null = off.
chaos_seed: ?u64 = null,
/// `-j<n>`: how many worker threads prove in parallel; null = `defaultWorkers()`.
///
/// DEFAULT (user ruling 2026-09-20): `max(1, logical_cpus / 2)` — the logical CPU count
/// HALVED. The prover is compute-bound and lock-heavy, and the measured optimum sits at the
/// PHYSICAL core count: on an 8-core/16-thread box `check std` runs 0.68 s at `-j8` and
/// regresses to 0.78 s at `-j16`, consistent with SMT siblings splitting one core's
/// execution units (a spinning sibling steals cycles from the very lock holder it waits
/// on). Halving the logical count lands on physical cores wherever SMT is on.
///
/// On a machine WITHOUT SMT this undershoots by 2x. That is accepted on purpose: the
/// binary does not parse `/sys` to find physical cores. `-j<n>` always exists, and a user
/// who wants physical-core precision wraps `bpa` in a shell script that reads
/// `/sys/devices/system/cpu/*/topology` and passes `-j`. That is the documented contract.
///
/// (`-j1` was the default while a scheduling race was open — a task could park on a
/// blocker that had already finished, so `dir_ok -j4` sometimes counted 2 theorems where
/// `-j1` counted 3. That was found and fixed, and std/aata are byte-identical from `-j1`
/// to `-j16`; output is a function of (tree, roots), never of scheduling.)
workers: ?usize = null,
/// `--sync-io`: read every source file INLINE on the prover worker that demanded it — the
/// pre-loader code path — instead of handing the read to the I/O pool (`Engine/Loader.zig`).
/// Reads are asynchronous BY DEFAULT; this is the explicit opt-out and the bisection
/// baseline, and the suite pins a gate to it so the inline path stays exercised.
sync_io: bool = false,
/// `--io-threads=<n>`: use the THREAD-POOL loader backend with `n` as its ceiling (capped at
/// `max_io_threads`). Unset (the default) means: on Linux the io_uring backend — ONE ring
/// thread, no count to tune — falling back to the pool at `max_io_threads` where the ring is
/// refused; elsewhere the pool at `max_io_threads`. Naming a count therefore selects the pool
/// as well as sizing it, which is what keeps that path exercised on Linux. The pool is sized
/// separately from `-j` on purpose: a loader thread sleeps in the kernel, so SMT costs it
/// nothing and it may exceed the core count. A load the pool cannot take (ceiling reached) is
/// read inline, so a small ceiling is slower, never wrong. (See `Engine/Loader.zig`.)
io_threads: ?usize = null,

/// `--io-delay=<us>` in nanoseconds: sleep this long inside EVERY source-file read, to
/// simulate a slow filesystem (cold cache, NFS, sshfs) on a machine whose page cache cannot
/// be dropped. A measurement knob, not a tuning one: it is how the cost of a blocking read —
/// and the benefit of reads that are off-worker — is made visible and reproducible. Applied
/// by whichever path reads: the inline read, a pool thread (both sleep before the read), or
/// the ring (a linked timeout ahead of the open, so the delay itself is asynchronous). 0 = off.
io_delay_ns: u64 = 0,

pub const max_io_threads = 64;

const Verify = @This();

/// The default worker count: logical CPUs halved, never below 1. See `workers`.
pub fn defaultWorkers() usize {
    const logical = std.Thread.getCpuCount() catch 2;
    return @max(1, logical / 2);
}

/// Is the `using` word named by `rule_word` (an `InternPool.RuleStr` — but resolved by the
/// caller to a `Word`) currently trusted? Callers map their rule to a `Word` first.
pub fn trusts(self: *const Verify, word: Word) bool {
    return self.trusted.contains(word);
}

test "group words expand" {
    const testing = std.testing;
    try testing.expect(Word.parse("engine").?.contains(.model));
    try testing.expect(Word.parse("engine").?.contains(.import));
    try testing.expect(!Word.parse("engine").?.contains(.polynomial));
    const pa = Word.parse("polynomial_all").?;
    try testing.expect(pa.contains(.polynomial));
    try testing.expect(pa.contains(.polynomial_quantified));
    try testing.expect(!pa.contains(.simplify));
    try testing.expect(Word.parse("tautology").?.contains(.tautology));
    try testing.expect(Word.parse("tautology_all") == null); // no _all for a singleton
    try testing.expect(Word.parse("nonsense") == null);
    try testing.expect(Word.parse("instantiation") == null); // never trustable (see #93)
    try testing.expect(Word.all().contains(.model));
}
