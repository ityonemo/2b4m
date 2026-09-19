# PERF-NOTES — execution-strategy rearchitecture (measured 2026-08-01)

Status: RECORDED, NOT SCHEDULED. This note pins the measurements, the
architecture we converged on, and the decisions already made, so that when the
work starts it starts from conclusions rather than re-derivation.

## Measurements (2026-09-16) — run `zig build bench`

**Always measure a ReleaseFast build.** `build.zig` uses
`standardOptimizeOption`, so a bare `zig build` produces a DEBUG binary that is
roughly 35x slower; the `bench` step builds its own ReleaseFast binary for
exactly this reason. Timings taken 2026-09-16 (16 cores):

| target | Debug | ReleaseFast |
|---|---|---|
| `check std` (48 files, 468 theorems) | 61.7 s | **1.82 s** |
| `check aata` (25 files, 165 theorems) | 69.9 s | **2.24 s** |
| `std/integer/divides.bpa` (547 decls) | 11.9 s | **0.34 s** |

This supersedes the 2026-08-01 numbers below, and with them the conclusion that
the suite is *"process-spawn-bound, not compute-bound"* — a single file now runs
long enough that spawn tax is not the story. It also resets the revisit
trigger recorded at the end of this note: measured against ReleaseFast, the
corpus has NOT crossed it.

## Superseded measurements (2026-08-01)

- Full `zig build test`: **~0.82 s** wall — ~137 cold `bpa` spawns at ~8 ms
  each. The suite is **process-spawn-bound**, not compute-bound.
- Largest single file (`examples/sqrt2.bpa`, 291 decls / 62 theorems):
  **~55 ms**, of which ~8 ms is spawn. Parse time is invisible everywhere.
- Redundancy: every gate re-elaborates and re-proves its **whole import
  closure** (`euclid.bpa`'s 236 decls include the entire peano chain; peano's
  theorems are re-proven dozens of times per suite run). Sum-of-closures vs.
  distinct declarations is roughly a 5–10× compute redundancy.
- The term pool is **pure append** (`Pool.add` appends and returns the index —
  no dedup, no intern map). This is the fact that makes parallel checking
  cheap: there is no shared structural-sharing table to contend on.

Implications, in order of leverage: stop spawning per file; stop re-elaborating
shared imports; stop re-proving unchanged files; only then, prove in parallel.
Parallel *parsing* is a rounding error in these numbers — we do it anyway
(decided): it is free, safe, and pays at corpus scale. See the job model.

## The architecture: one engine, three features

Work-stealing prove jobs, statement-hash caching, and dependency-narrowed
checking (DEPCHECK-PLAN.md) are the same design seen from three sides:

- "is theorem T proven?" is a **query**; prove jobs evaluate queries on demand;
- the citation DAG is **discovered during evaluation** (see suspension below);
- **parallelism** = evaluating ready queries on a work-stealing pool;
- **caching** = persistent memoization of query results, keyed by content hash;
- **narrowing** = the choice of demand *roots*: `check A t3` seeds one query,
  `check A` seeds the file's own proof-carrying theorems, `--total` seeds
  everything.

The DEPCHECK rollback conclusion ("rearchitect the execution strategy first")
lands here: this scheduler *is* the rearchitecture, and narrowing falls out of
it for free instead of being bolted onto the eager loader.

**The governing principle: the THEOREM is the unit of proving; a file is a
unit of parsing and code organization** (namespaces, imports, what a library
*is*) — not of proving. Today's loader eagerly proves every theorem in every
file of the import closure; the target engine never does that. `check` proves
the demanded closure — roots plus whatever suspension discovers — and nothing
else. "Prove all files" survives only as the explicit `--total` root set.

## THE ONE BIG WARNING

Under demand-driven proving **you can commit an incorrect theorem and never
find out, if nothing uses it.** An unracked theorem is not proven, not
kernel-checked — not even grammar-checked if its whole file goes untouched — yet
it sits in the source looking exactly like a verified result. This is the
DEPCHECK-PLAN.md narrowing consequence taken to its sharpest form, and it is
**accepted as a reasonable long-run tradeoff (user ruling)**. The mitigations
are mandatory, in the house style that silence must never imply verification:

- **Disclosure on the summary line** (the accelerated-disclosure ethos applied to
  laziness): count the undemanded, e.g.
  `OK: 12 theorems proven (closure of 3 roots); 41 declared, 29 unchecked`.
  A reader must never infer "in the file" ⇒ "checked".
- **`--total` is the audit mode** — roots = every roster of every reachable
  file. CI and finalization run it. The integration suite achieves total
  coverage a second way — every corpus file has a gate rooted at its own
  theorems — which holds exactly as long as the corpus-hygiene rule "every
  committed file gets a gate" holds.
- The existing 0-theorems-proven warning already fails the degenerate case.
- (Unused *axioms* are inert by comparison — an assumption nothing uses
  asserts nothing. The hazard is specifically unproven-but-believed theorems.)

## Job model

Two job kinds:

- **parse jobs** — `parse(file, needed)`: parse the WHOLE file once, cache the
  full AST (every proof body included), register the file's roster — its
  imports (namespace → path: a *registration*, not a demand), its axioms, and
  its theorems by NAME only — then rack prove jobs for exactly the `needed`
  list. A later demand for another theorem of the same file finds its AST
  already cached: no re-parse, just rack. Parse jobs are pure (bytes → AST, no
  shared state), run in parallel on the pool, and never wait.
  *(Considered and rejected: lazy proof-body parsing via byte-spans — parsing
  is measured-negligible, and whole-file parsing keeps every demanded file
  fully syntax-checked.)*
- **prove jobs** — one per theorem: elaborate + kernel-check the proof. May
  **suspend** — on an unproven cited theorem, or on a not-yet-ready file its
  elaboration demands.

**Laziness lives at the file and racking level (decided).** Nothing parses a
file until a needed theorem's elaboration first touches its namespace — an
`import` only registers. Statement elaboration is itself on-demand at
declaration granularity: the roster registers names, and a declaration's
statement (and any alias it resolves through) elaborates when first needed —
racked as a root, cited by a demanded proof, or validated for a cache key. So
even registering a file's roster never cascades into its imports.

**There are no phases (accepted consequence — user ruling).** Parsing can
trigger arbitrarily late: a deep import chain may be parsed for the first time
after most of the proving has finished, because demand chains unroll during
elaboration (prove T → touch namespace → parse B → elaborate → prove X →
resume T). This is fine because it is *output-invisible*: the demand set is
content-determined, all output is canonically ordered at emission, and
diagnostics are batch-rendered at the end (as today) — a syntax error
surfacing late in a deep import reads identically to one found up front, and
fails exactly its dependent cone with the usual "cites unproven theorem"
semantics. The one real cost is cold-run critical-path latency on deep chains
(each hop pays parse + elaborate serially, late). Sanctioned mitigation, if
ever felt: idle-worker **prefetch** of registered-but-undemanded imports —
parse is pure, so speculation is safe — under the strict rule that a
speculative parse's **diagnostics stay quarantined** unless the file becomes
demanded (otherwise prefetch changes what is reported and breaks the lazy
semantics).

**Slow filesystems (recorded corner case — user).** On a slow mount (NFS and
friends) it is fine — expected — to brr through theorems while a file fetch is
still in flight: the files-table waitlist doesn't care *why* a file isn't
ready, so the fetch's dependent cone parks and everything else proceeds. The
refinement this forces: **fetch and parse are different resource classes.** A
blocking read can stall a worker for seconds, and "jobs park, workers never
block" is the anti-deadlock invariant — so the file lifecycle splits into
fetch (I/O-bound, runs on a small dedicated I/O pool or oversubscribed
threads) → parse (CPU, on the work-stealing pool). The files table is
unchanged: {unfetched | fetching | parsing | ready} is one in-flight arc with
one waitlist. Determinism is untouched (latency is timing, not content), a
fetch error is a late "cannot open" failing exactly its cone, and the
quarantined-prefetch valve is *especially* valuable here — early fetches of
registered imports hide network latency without changing what is reported.

**One uniform proven-lookup table.** statement → {unknown | in-flight +
waitlist | proven | failed}. Nonschematic axioms are entries **born proven**
at registration — no job exists for them, and citing one never waits; cache
hits enter the same way. A prove job never asks *why* something is proven
(vacuously, by job, or by memo). Schemas stay out of the table entirely
(stored forms, monomorphized per use inside the citing job). The epistemic
axiom/theorem split survives everywhere it matters — kernel `axiom_ref` vs
`theorem_ref`, the `by axiom` audit, lockfile semantics (assumed vs verified)
— uniformity is a scheduler hot-path property only. The FILES table has the
same shape (path → {unparsed | in-flight | ready} + waitlist), so waits exist
on exactly two statuses — *file ready* and *theorem proven* — and one stall
detector covers import cycles and citation cycles alike.

**Suspension = explicit state machines with waitlists (decided).** A prove job
is a small state machine: the theorem being proven, its elaboration state
(the Elaborator + Lowering are already heap/arena data, owned by the job), and
a **suspend point**. When job T hits an unproven cited theorem X:

- T **create-or-finds X's prove job** in the jobs table (keyed by StatementId,
  atomically — concurrent workers hitting the same unproven X find the one
  existing job, never a duplicate) and adds itself to X's **waitlist**;
- T parks, releasing its worker back to the pool — jobs park, workers never
  block, so a bounded pool cannot deadlock on parked threads;
- when X completes, X's job racks every waiter back onto the job queue, and
  each resumes at its suspend point. If X *failed*, waiters resume and fail
  with "cites unproven theorem" — the same semantics as today.

No restarts (re-elaborating T once per dependency is wasted work) and no
language-level async: **prove jobs are the only job kind that suspends** —
parse jobs run to completion — so one bespoke state machine suffices and no
general-purpose async runtime exists anywhere. The suspend point is an
explicit position in the proof-step traversal, which requires the **lowering
driver** to walk the step tree with an explicit stack instead of native
recursion — a driver refactor; the kernel is untouched.

**New obligation introduced by waiting — the wait-for graph.** Mutually-citing
theorems (expressible via forward refs) become mutual waiters and stall, where
today's eager order simply errors on one of them. The scheduler must detect
the stall (no runnable jobs + non-empty waitlists) and report it as a
citation-cycle diagnostic, deterministically.

**Why suspension is necessary, not an optimization** (the lesson from the
failed two-pass DEPCHECK attempt): a proof cannot even be *lowered* until its
cited lemmas are proven — tactic certificates (`simplify`, `arithmetic`, …)
check `t.proven` when they resolve well-known lemmas — and those tactic-implied
dependencies are **invisible to any syntactic scan** (`[using arithmetic]` pulls
`addIsAssociative` from scope without ever naming it). No static schedule can
be complete; dependency discovery must happen inside elaboration. A syntactic
pre-scan of the explicit `[by theorem X]` refs (what `query uses` computes)
remains useful as a *scheduling hint* that makes suspensions rare.

## Concurrency ground rules

- **The kernel stays single-threaded and untouched.** Parallelism at theorem
  granularity only; a prove job runs the existing elaborator + kernel on one
  proof.
- ~~**Per-worker pool segments.**~~ RETRACTED 2026-09-16: this assumed ONE
  shared term pool that is append-only with no dedup. Neither half holds now.
  `term.Pool` is hash-consed (`term.zig`), and pools are created PER TASK as
  local scratch (`FetchTask`, `Schema`, `Elab` each `init` their own) — never
  shared. There is no cross-worker structural table to contend on, so there is
  nothing here to build.
- **Env grows under a single writer lock.** Lazy file demand means the env is
  *not* frozen during proving: a newly demanded file's (or declaration's)
  elaboration appends statements mid-run. Declaration elaboration is cheap and
  rare, so one writer lock suffices — but env storage needs **stable
  references under append** (the ArrayList-realloc aliasing hazard, now on
  `env.statements`). Internal ids become schedule-dependent, which is exactly
  why every *output* is canonicalized by content/source order, never by id.
  Prove jobs flip `proven` and record accelerated steps, published with
  release/acquire on completion (ordered by the waitlist edges).
- **The interner is the one genuinely shared mutable map** (fresh `x#N` names
  are interned mid-proof). Solvable — striped locking, or per-worker id ranges
  — but it must not be forgotten.

## Determinism (hard requirement — user ruling)

A cold `bpa check` of the same tree MUST produce byte-identical output
regardless of worker count and cache state:

- diagnostics buffered per declaration and emitted in **source order** within
  the **canonical file order** (import-declaration DFS from the root), never
  completion order;
- the **demand set is content-determined**: which files parse and which
  theorems prove is a function of (tree, roots), never of scheduling —
  elaboration walks proofs deterministically and suspension defers work but
  never skips it — so laziness cannot perturb output;
- summary counts computed from the env, never from scheduling;
- the goldens in `tests/` depend on this — it is the contract, and the
  integration suite is the enforcement.

**Cache-transparency is part of the requirement:** a warm (cached) run must be
byte-identical to a cold run of the same tree — the cache may change *when*
work happens, never *what* is printed.

**Contingent exception (user ruling):** should a resident daemon/watch process
doing live theorem reloads ever exist, it may be **path-dependent** — output
depending on the edit history, not only the final tree — with CI and
finalization always using cold runs. But see the next section: the design goal
is to never need one, which keeps byte-determinism universal.

## Caching

**INVARIANT (user ruling 2026-08-09): plain `bpa check` is ALWAYS strict** —
full kernel certificates, no imported-proof/schema trust, and NO cache. The
maximal guarantee is the default and is never silently weakened. All caching /
trust-shortcutting is OPT-IN, disclosed, and non-default. Corollaries:

- **Caching lives behind its own flag** (`--cached`, a non-strict mode like
  `--fast`) — it never activates under strict `check`. A user who runs plain
  `check` re-verifies from axioms every time; cache staleness can never ambush
  them. (The `--cold`/force-re-verify affordance below is for *within* a cached
  workflow.)
- **The cache key includes the verify-mode + taint set**, so a `--fast`/tainted
  entry is never served to a strict request (no laundering trust through the
  cache). A served-from-cache result still reports trust status / dead-step /
  accelerated-taint exactly as if freshly checked — the cache is a speed layer,
  never a correctness- or disclosure-shortcut.
- **Collapse the fast-flag ladder (user ruling — LANDED).** The old
  `--fast`/`--faster`/`--reckless` ladder folded into ONE dev-speed flag `--fast`
  with granular per-`using`-word trust: `--fast` (all), `--fast-only W…`
  (allowlist), `--fast-except W…` (denylist). Two user intents only: dev-speed
  (`--fast…`) vs the real guarantee (plain `check`, always strict). NOTE: this is
  NOT "trust imports and imported schemas" as first sketched — `#93` made
  `instantiation` never trustable (the per-instance proof is the sole soundness
  gate), and trusting the `import` word admits a citation's SHAPE only (a
  demanded imported theorem is still re-checked in its own file).

**The cache unit is the statement, matching the proving unit.** (This
supersedes the earlier "files are the permanent trust/cache boundary" ruling,
which belonged to the file-eager model; files remain the unit of parsing and
code organization.)

- **Per-statement memo entry**: key = α-normal form of the statement + the
  proof text + the full keys of its dependencies' statements, recursively — a
  Merkle DAG over the citation graph. The dependency set — *including the
  tactic-implied deps invisible to any syntactic scan* — is exactly what a
  prove job discovers during elaboration, so the scheduler produces sound
  cache entries as a byproduct of proving. Hit ⇒ the theorem is
  proven-by-cache; miss ⇒ a prove job runs.
- **File hashes are only the fast path**: H(file bytes) short-circuits
  re-parsing and re-keying an unchanged file's statements; it proves nothing
  by itself.
- **Trust/distribution story**: a content-addressed "statement hash →
  verified" table is the lockfile for third-party theories — "trusted"
  becomes "verified previously, hash unchanged", at theorem granularity.

Disclosure: under `--cached` the summary reports cache use (e.g.
`N proven (M from cache)`). (Reconciled with the INVARIANT above: caching is
opt-in via `--cached`, so plain strict `check` is already the "force full
re-verification" path — there is no separate `--cold` under strict; a
force-refresh affordance, if wanted, lives *within* a `--cached` workflow.) The
local cache is a trust surface equivalent to trusting one's own filesystem and
binary; signing is a distribution-time concern, not a local one.

## Daemon/watch mode: ~obviated by durable caching (decided)

The durable cache makes a cold process fast enough that a resident daemon has
no perf case. The arithmetic: warm-unchanged = spawn (~8 ms) + hash + cache
read ≈ ~10 ms; one-file-edited = + re-check of that file (≤55 ms for the
largest file today; with per-statement memoization, only the edited theorem +
its intra-file dependents, likely <10 ms) + ms-scale declaration
re-elaboration. All end-to-end latencies land at ~10–60 ms from a cold start —
below human perception, and irrelevant to bpa's primary author, an LLM agent
running discrete CLI commands.

What a daemon would uniquely buy, and why we decline each:

- a resident env (matters only if declaration-closure elaboration gets
  expensive at very large scale; an env-snapshot cache could cover even that);
- push-based re-check on save — workflow, not perf: a thin `bpa watch` wrapper
  (inotify → re-exec the cold cached path) delivers the UX with **zero
  resident state**;
- LSP-style editor features — a different project, not a perf plan.

What declining the daemon buys: byte-determinism stays **universal** (no
path-dependence carve-out in practice), there is no second long-lived
execution mode to keep sound, and no language-server-style state drift — the
cache is content-addressed and self-validating; a daemon is neither.

## Phasing

1. **The theorem-unit engine** — parse jobs + prove jobs + suspension, single
   process. This is the centerpiece and comes first: it delivers the DEPCHECK
   narrowing semantics (stop proving all files), kills the spawn tax and the
   import-closure redundancy as side effects (one process, each file parsed
   once, only demanded theorems proven), and can start single-threaded — the
   work-stealing pool is a knob to turn on later, not a prerequisite.
2. **Durable statement-hash memoization** — the cache layer over the same
   engine; warm runs ~free; the lockfile/trust story rides along.
3. **(optional) `bpa watch`** — a stateless wrapper: on file change, re-exec
   the cold cached path. No resident daemon; see the section above.

(A trivial multi-file batch driver could cut the suite's spawn tax even
earlier, but it must not entrench file-eager proving — the engine subsumes it,
so only build it if the suite hurts before phase 1 lands.)

## Trigger to revisit

Not scheduled. Start phase 1 (the engine) when the suite or interactive
latency is *felt* (rough thresholds: suite > 5 s, or a single-file check
> 250 ms), or when DEPCHECK narrowing is wanted — whichever comes first.

**Status 2026-09-16: not crossed.** Measured on ReleaseFast (see the top of
this note), `zig build bench` runs the whole corpus in under 6 s and the
heaviest single file in 0.34 s. Debug numbers look like the trigger is far
past — they are not the measurement to judge by.
Phase 2 (the durable cache) follows when re-proving unchanged work is the
dominant cost.
