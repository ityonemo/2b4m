# `fact` — one keyword for re-exporting a proved-or-assumed name

**Status: BUILT, 2026-10-09.** 2331 aliases migrated; `axiom X = …` / `theorem X = …` are now
hard errors naming `fact`. Kept as the rationale record — the three findings below (it goes
stale, nothing checks it, `--axioms` already reports the truth) are why the keyword exists.

Two things the implementation turned up that the sketch did not predict:

- **`fmt` has its own declaration-keyword list** (`src/fmt.zig:76`). Until `fact` was added to
  it, `fmt` indented every `fact` line by two spaces as though it were inside a block — which
  looked like a mass formatting regression across 149 files and was really one missing enum
  arm. Any new top-level keyword needs that list.
- **The blast-radius report changed, for the better.** `tests/cases/hole_transitive.b4m` used
  to list `restsOnHole, transitiveHole` as resting on the hole; under `fact` it lists only
  `transitiveHole`. A re-export does not itself rest on anything — its origin does — so the
  shorter answer is the right one. The golden now records that reasoning.

## The problem

A fact alias today must restate the target's declaration KIND:

```2b4m
axiom   unionMember        = set.unionMember
theorem lessThanAddRight   = real.lessThanAddRight
```

That kind is **the target's property, not the alias's** — and the alias has no way to know it.
So the field carries no information the reader can't get better elsewhere, and it can be
wrong. Three ways it goes wrong:

1. **It goes stale.** During the openai-wiles work `aMarkedAlgebraicClassExistsAtSomeGoodPeriod`
   moved hole → axiom → theorem as it was decomposed; every transition silently invalidated
   its alias in `architecture.md`, which still said `axiom`.
2. **Nothing checks it.** `2b4m check` is happy either way. The two errors in openai-wiles were
   found by hand-comparing aliases against their targets, not by the checker.
3. **It is redundant with the thing you should actually read.** `--axioms` resolves every fact
   to its ORIGIN and reports the true kind there (`— CITED HOLE` at `traces.b4m:44` even when
   the local re-export says `axiom`). So the disclosure was never at risk; only the source text
   misleads.

The AST already agrees the distinction is fake: `ast.Axiom`, `ast.Theorem` and `ast.Decl.hole`
all carry the SAME `Alias` struct. The three spellings are one node.

## Measured scope

Counted 2026-10-09:

| | fact aliases |
|---|---|
| `axiom X = …` | 829 |
| `theorem X = …` | 1516 |
| **total** | **2345** |

Kind mismatches found by scanning `std/` against origin declarations: **10** (~0.4%). Nine are
`theorem` where the origin is `axiom` — the conservative direction, claiming less than is true.
One goes the other way:

```
std/primes/classes.b4m:48   addSuccRight declared 'axiom', origin is 'theorem'
```

(The scan is name-based, so a same-named declaration in another namespace could inflate this;
re-verify during implementation.) No soundness consequence in any case — the report resolves
to origin — but all ten are documentation that is simply false.

## The change

```2b4m
fact unionMember      = set.unionMember
fact lessThanAddRight = real.lessThanAddRight
fact aStabilizationIsLoose = traces.aStabilizationIsLoose   // target is a CITED HOLE
```

One keyword for every re-export of a named fact, whatever its origin kind. `fact` is **only**
an alias form — there is no `fact X: <formula>` local declaration, because a local claim always
has a kind (`axiom` = theory primitive, `theorem` = proved, `hole` = unproved, `hole … cites`
= assumed on external authority).

### Why not keep the kinds and just lint the mismatch

Considered and rejected as the primary fix, though it is a good fallback if `fact` stalls. A
lint would catch the 10, cost one function and zero file changes — but it keeps a field whose
only job is to be checked against something that already knows the answer. Deleting the field
beats validating it.

A middle option also exists and is strictly worse than `fact`: let the alias INHERIT the
origin's kind and reject a disagreeing explicit kind. Same effect, no migration, but it leaves
2,345 lines of redundant-and-now-load-bearing-looking text in place.

## Implementation sketch

1. **Lexer**: `fact` keyword (`.keyword_fact`), beside `axiom`/`hole`/`theorem`.
2. **Parser**: one arm. `fact NAME = <qualified>` → the existing alias node. Decide which
   `ast.Decl` variant carries it — likely a new `.fact: Alias` rather than reusing
   `.axiom = .{ .alias }`, so the old spellings can be rejected cleanly.
3. **Deprecate the old spellings.** `axiom X = …` / `theorem X = …` / (hole has no alias form
   today) become hard errors naming `fact`. Do this in the SAME commit as the migration so the
   tree is never half-converted.
4. **Alias-collapse is unchanged.** Identity-by-origin already does the real work
   (`[[alias-collapse]]`, `namespace-semantics-spec`); this only changes the surface word.
5. **Migration**: scripted. `s/^axiom (\w+) = /fact \1 = /` and the `theorem` twin across
   `std/`, `aata/`, `examples/`, `tests/`, `drafts/`, `openai-wiles/`. The 10 mismatches
   disappear by construction — there is no kind to get wrong.
6. **Gates**: `zig build test` (several CLI goldens quote alias lines — grep the expectations),
   `check --library std` (100 files / 1244 theorems), `check aata` (38 files / 293 theorems),
   `fmt --check`. Plus a new fixture: `fact` to each of an axiom, a theorem, and a cited hole,
   with `--axioms` showing the origin's true kind in all three.

## Notes for whoever builds it

- `hole` has **no alias form** today (the parser's hole arm never calls `parseAliasTail`), which
  is why re-exporting a cited hole must currently be spelled `axiom X = …`. That is fine as-is
  (user ruling 2026-10-09) and `fact` removes the awkwardness entirely.
- **Fact aliases are not prover-supported**: `ProveTask` has an explicit
  `"fact aliases are not yet supported by the demand prover"` diagnostic on the `.alias` arm for
  both axiom and theorem. Aliases work because collapse resolves them *before* proving; the
  error only fires if a proof cites the alias by its LOCAL name in a way that reaches the prover.
  Adding `fact` must not change that — and a brief attempt to add a `hole` alias form hit this
  immediately (three cite sites in `stabilization-traces.md` broke).
- Keep the `^axiom` grep useful: after this change, every `^axiom` line outside `std/` is a
  LOCAL declaration, so `grep -rn '^axiom ' <dir>` becomes a clean audit for non-fundamental
  assumptions rather than a list mostly full of re-exports. That is a real secondary win — it is
  how the two openai-wiles errors were eventually caught.

## Related, separately pinned

**`axiom` is doing a third job nobody named.** Measured while considering a rule that axioms
must live in `std/`: the `aata/` chapters use `axiom` for **scoped local hypotheses** — "let `H`
be a subgroup", `mInH`, `orderPositive`, `subgroupHasIdentity` (14 of them). Those are neither
theory primitives nor borrowed results; they are *givens* for the span of a section. A
location-based rule would wrongly condemn all 14, which is why that rule was NOT adopted. The
honest fix is a keyword for a scoped given — its own design conversation.
