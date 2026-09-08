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
//! is in the set. The CLI builds it: `--fast` (all), `--fast W…` (allowlist), `--fast --slow W…`
//! (all but). Group words (`<tactic>_all`, `engine`) expand at parse time (see `Word.parse`).

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

const Verify = @This();

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
