# Dependency-narrowed checking (`2b4m check`)

## New default semantics (user-decided)

`2b4m check <file> [theorem]` verifies **only the theorems reachable from a set of
roots**, following citation edges (and alias / qualified-name / import hops to
their origin declarations). This is the DEFAULT — it changes what a bare
`2b4m check A` guarantees.

- **Roots, no theorem argument:** every theorem *declared with its own proof* in
  the queried file (`theorem t: … proof … qed`). NOT pure aliases
  (`t = other.t`), NOT axioms, NOT imported theorems — those are only verified
  if a root reaches them.
- **Roots, with a theorem argument (`check A t3`):** just `t3` (must be a
  proof-carrying theorem in the queried file; a schema target is allowed and its
  proof is a root).

Reachability follows:
- `[by theorem X]` / `[by axiom X]` / `[by instantiate S(…)]` citations,
- well-known-name lookups used by tactic certificates (`arithmetic`,
  `simplify`, `ac`, …) — the lemmas they pull from scope,
- alias hops: a cited name that is an alias resolves to its origin statement
  (possibly in another file), and THAT origin is the dependency,
- `unpack … from <step>` and `case on <step>` reference local steps only (not
  cross-declaration), so they add no cross-theorem edge.

Axioms are leaves: they must *exist* (name resolves) but have no proof to check.
Schemas: a cited/instantiated schema's proof IS checked (comptime template,
re-checked per instance as today) — reached schemas are in the closure.

### The consequence (accepted, by design)

    file B:  thm t1 (correct),  thm t2 (INCORRECT)
    file A:  t1 = B.t1;  t2 = B.t2;  thm t3 uses t1     // t2 unused

`2b4m check A` PASSES: `t2` is not reachable from A's roots (t3 → t1), so
`B.t2`'s bad proof is never kernel-verified. A vouches for the theory it
*builds*, not for everything it can see. To vouch for `t2`, `2b4m check B`.

This is a deliberate weakening of the old "verify everything reachable in the
whole import graph" default, chosen for laziness/speed. It must be understood:
an unused false theorem (local or imported) does not fail `check` on a file that
merely re-exports or ignores it.

### `--total` — the exhaustive escape hatch (reserved)

`2b4m check --total <file>` verifies **everything**: every theorem declared in the
queried file AND every theorem in every (transitive) dependency file, whether or
not it is reachable from the file's roots. This is the OLD default semantics,
kept as an explicit opt-in. Use it to vouch for a whole file + its imports
(e.g. CI over a library), where narrowing's "unused ⇒ unchecked" is exactly what
you DON'T want. In the scenario above, `2b4m check --total A` FAILS on `B.t2`.

So the check spectrum is:
- `check A t3`   — narrowest: one theorem's closure.
- `check A`      — DEFAULT: closure of A's own proof-carrying theorems.
- `check --total A` — exhaustive: every theorem in A and all its imports.

(`--total` composes with the speed flags, which defer HOW proofs are verified;
`--total` widens WHICH proofs are verified. Not yet implemented — reserved.)

## Two-pass implementation

The dependency edges are known during elaboration's **lowering** phase
(`lowerSteps` → `resolveStatementRef` and the well-known/instantiate lookups
resolve each cite to a `StatementId`). Kernel *verification* (`k.check`) is
separate and is the expensive part we want to skip for unreached proofs.

**Pass 1 — resolve + graph, no kernel verify.**
Elaborate every file as today for NAME RESOLUTION and edge recording, but do NOT
run `k.check` on proof bodies (treat every theorem's lowering as
resolution-only). Record, per theorem/schema `StatementId`, the set of
`StatementId`s it cites (a new `deps: []StatementId` recorder threaded into the
elaborator; append at each `resolveStatementRef` / well-known / instantiate
resolution while a "current statement" is set). Result: a cross-file citation
graph keyed by `StatementId`, plus each proof's lowered kernel program cached
for pass 2 (or re-lowered — decide by cost).

**Closure.**
Seed with the roots (above), BFS the graph → the set `to_verify`.

**Pass 2 — verify the closure, memoized.**
Kernel-check the proof of every `StatementId` in `to_verify` exactly once
(memoize by id). Whole-file case: roots = all local proof-carrying theorems, so
the closure is "everything they reach"; each proof verified once (no redundant
re-verification — the memoized-whole-file guarantee).

Open implementation questions to resolve while building:
- Cache the pass-1 `Lowering` per theorem, or re-lower in pass 2? Re-lowering is
  simpler and correctness-obvious; caching is faster. Start by re-lowering.
- Schema instances: a schema reached in the closure re-checks its proof per
  instance as today. Edge recording must capture schema→cited-lemmas.
- Acceleration must still propagate correctly to the ROOTS' facts (the
  summary counts accelerated steps over what was actually verified).

## Summary / counts

The `OK: N declarations, M theorems proven` line reports over the theorems
actually VERIFIED (the closure), not all declared. Unreached theorems are not
counted as proven. (Confirm exact wording with the zero-theorem warning: a file
whose roots verify nothing still warns + exits nonzero.)

## Interaction with the zero-theorem warning (already shipped)

`theorems_proven == 0` → warn + exit 1. Under narrowing, "proven" = "verified in
the closure". A file with only aliases/axioms/imports (no local proof-carrying
theorem) has no roots → 0 verified → warns, as intended.
