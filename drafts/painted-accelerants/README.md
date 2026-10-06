# drafts/painted-accelerants — accelerants should produce in the AMBIENT namespace

Banked 2026-10-04, NOT applied. `painted-production.patch` is a 2-change WIP against
`src/Engine/ProveTask/Prove.zig`; applying it takes `check --library std` from green to ONE red
file. Kept because the diagnosis is solid and the remaining error is a known blocker.

## The design question (user, 2026-10-03/04)

> "An accelerant is running in whatever namespace it's running in, and that's that. It should
> not matter whether it's in universe or in a model."

Today `demandUsing` does the opposite: `if (source_mode) self.model = .universe` — it turns the
ambient model OFF, runs the producer in SOURCE space, and lets the instance `ProveTask` re-paint
the result afterwards. I defended that as "namespace-neutral, therefore one synthetic serves
every transfer." That defence is wrong.

## Why neutrality is wrong — the decisive example

The user's framing: two models that create a `SOME_NEG_NUMBER` and a `POS_NUMBER` and use them
in the same arithmetic call will need DIFFERENT theorems. The producer, running unpainted, sees
an opaque source symbol with no sign information and emits one skeleton.

`std/set.b4m` confirms it concretely, with no arithmetic needed. The step
`[using specialize unionMember(b, c)]` cites `unionMember`, an AXIOM the model discharges
(`set.unionMember <- unionCollectionContains` in `std/collection.b4m`). The two differ in the
binder sort:

    axiom unionMember:              forall a, b: Set;        …   (source)
    axiom unionCollectionContains:  forall a, b: Collection; …   (the discharging fact)

So the producer reads a **different theorem** depending on whether it is painted. That is the
consumer contributing the fact, which is exactly what unpainted production cannot see.

Corroborating: `arithmetic` is documented as receiving its domain facts FROM THE THEORY — memory
`arithmetic-pure-integer-engine`, "ℕ nonnegativity is theory-supplied via a well-known `nonneg`
predicate injected per variable", and `ARITHMETIC-SORT-AGNOSTIC-DESIGN.md`'s "integrality is a
declared capability, not a sort". A neutral producer asks the WRONG THEORY for those facts.

## What the patch does, and what it fixes

1. `source_mode = false` — produce with the ambient model ON.
2. A `Prove.painted_production` flag that SUPPRESSES the source-space arg twin. Under painting
   the synthetic is already target-space text, so a source twin is meaningless — and harmful.
   Instrumentation at the failing check showed exactly that: `src_space=true`, wanting
   `Collection` (the painted param) while elaborating the arg at `Set`.

Result: `check --library std` goes from 3 errors to 1.

## The one remaining error is a DOCUMENTED BLOCKER

```
std/group.b4m:433: AffineGroup@assoc{…}: step claims
  'forall b1: Real; notMinusOne(b1) -> … star(star(starInverse(a), b1), b2) = …'
but forall_elim derives
  'notMinusOne(starInverse(a)) -> forall b1: Real; notMinusOne(b1) -> …'
```

A GUARD PREMISE appearing where the claim is unguarded — verbatim the symptom pinned in
the then-open `ACCELERANT-ON-GUARDED-SETS.md` (since deleted; it listed three candidate
root-cause readings and stated none
is established. Painted production arrives at that blocker from the opposite side, which is
evidence it and the accelerant-namespace question are one issue rather than two.

Also unresolved and likely the same: `group.invProduct` is omitted from
`tests/cases/model_subgroup_transfer.b4m` because its proof cites the `assoc` accelerant (the
fixture calls it "a known separate boundary"), and the month-old memory note
`accelerants-not-model-aware`.

## Sequencing (user, 2026-10-04)

Bank this → items 1–3 of `~/.claude/plans/mighty-whistling-shannon.md` (demote `Prop`, the
schema-parameter union, the syntax) → then the documented blocker, with this patch as the
starting point.

## A process note worth keeping

Four wrong conclusions about this subsystem in one session, each from reading code rather than
running it: a correct diagnosis retracted on a misread comment, a deliberate mode switch called
"conceptually wrong", a transfer failure reported as a plain-case failure (the diagnostic names
the SOURCE file, which is misleading), and `source_mode` described as the only asymmetry when
the arg twin was another. Every one was settled in a single step by `std.debug.print` at the
failing comparison. In this subsystem, instrument first.

## ROOT CAUSE FOUND (2026-10-05) — abstracted params lose their guards

Pinned by instrumentation (not by reading), at the `RealUnitsGroup@assoc` failure in
`std/group.b4m:433`, reached from `std/real/units.b4m`. The chain, with the print that
established each link:

1. `cancelLeft`'s `[using assoc(opAssoc)]` is produced under `RealUnitsGroup` with
   `painted_production = true`.
2. `prepareRule` (`Prove.zig:3832`) strips `opAssoc`'s relativization guard to reach the
   equation — `[PR] skip 'opAssoc' model=4264 painted=true`. Its own doc comment says this
   is sound only because "the instance ProveTask runs under the model so the forall_elim
   discharge machinery strips them".
3. The synthetic's `forall_elim` at `recip(a)` leaks `nonzero(recip(a))`. `stripGuards`
   (`Prove.zig:8941`) DOES detect it — `[SG] impl=true eqg=false` — and calls
   `emitDischargeStep`.
4. `setupClosure` (`Prove.zig:1402`) DOES find the nomination
   `group.inverse: recip -| recipOfNonzeroIsNonzero` — `[SC] nfacts=1` — and pushes the
   closure's premise `nonzero(a)` as a sub-goal.
5. **`nonzero(a)` is undischargeable** — `[FAIL] undischargeable g=nonzero(a)` (and
   `nonzero(b)`).

So every piece of the guard machinery works; the environment it needs is what's missing.

**Why.** `a` and `b` are `cancelLeft`'s own statement binders. In the relativized theorem
they are `fix a: Grp` under guard `nonzero(a)`, dischargeable via `[by predicate]` (source 2
of `emitDischargeStep`). But `buildAssoc` calls `abstractGoal`, which abstracts the goal's
free caller-locals into schema params — so inside the synthetic `a` is a bare param with no
enclosing guarded `fix`. Source 2 cannot fire, and source 3's recursion dead-ends on it.

**Not a bug in `assoc`.** It is the structural consequence this README predicted: painting
production moves the goal into the guarded target space, but the facts that make that space
inhabited live in the CITING proof's binders, which abstraction discards.

**The fix shape.** The synthetic must carry the guards of its abstracted params as
ANTECEDENTS — the same treatment local premises already get via `prepareRule`'s `local_pf`
/ `producerPremiseFormula` path. Under a guarded model, `abstractGoal` should emit
`good(p_i) ->` for each abstracted param whose sort is refined, and the instance's call
site discharges it, where the original binder's guard IS in scope. Contained, and it reuses
an existing mechanism rather than adding one.

## THE SECOND BLOCKER — `std/set.b4m` / `std/collection.b4m` two-level remap

With the param-guard fix in, `--library std` has ONE remaining failure:
`std/set.b4m:597: expected sort 'Set', got 'Collection'`, reached from `std/collection.b4m`.
It is a DIFFERENT defect — a sort double-map, not a guard leak — and it is NOT fixed.

**The shape.** `model CollectionIsSet` maps `set.Element: Set` and `set.Set: Collection`.
`Set` is therefore BOTH a source sort and a target sort, so applying the model twice is
observable: `Element → Set → Collection`. The failing step is
`[using specialize unionMember(a, b)]`, whose synthetic calls `contains` — correctly remapped
from `set.member`, with signature `contains(Set, Collection)` — and supplies a `Collection`
where slot 0 wants `Set`. Instrumentation at `Elab.zig:548` gave
`callee='contains' want=Set got=Collection`, and at `Prove.zig:1779`
`want=Set(461) got=Collection(92) raw=461 mapped=92` — i.e. the param's raw sort IS `Set` and
the model maps it to `Collection`.

**Why `Delaborate.runExact` is not the answer** (and this is the useful negative result —
it is the same `runExact` that was recorded earlier as "broke std/sequence.b4m and
std/set.b4m"): `Accelerant.Builder.termExpr` uses non-exact tokens, so the ambient model
RE-APPLIES on re-elaboration. Flipping it to `runExact` under painted production trades one
failure for three:

| `termExpr` | failures in `std/collection.b4m` |
|---|---|
| non-exact (today) | 1 — `set.b4m:597` |
| `runExact` when painted | 3 — `set.b4m:431`, `:617`, `:1010` |

So a painted synthetic genuinely MIXES the two spaces: some of its symbols are already
target-space (must not re-map) and others are source-space (must re-map). One global
exactness flag cannot be right for both, which is why `sortTok` also had to be reverted —
making IT exact broke the param sorts, whose raw values are deliberately source-space.

**What this says about the design.** Painted production needs per-symbol provenance, not a
per-production mode — exactly the "per-symbol predicate" the user asked about earlier in this
work. That is a larger change than the guard fix and is deliberately NOT attempted here.

### Tried and rejected: a per-symbol "is it already a target?" predicate

The obvious refinement of the global flag is to decide provenance per SYMBOL: a symbol
already in the model's image is final, anything else still maps. Implemented as
`InternPool.isModelImage` (scan `m.overlay` for `e.tgt == symbol`, mirroring `applyModel`'s
`e.src` scan) and applied at the single mapping point, `Elab.resolveSymbolTok`.

It produces the SAME 1→3 regression as `runExact` (`set.b4m:431`, `:617`, `:1010`).

**Why, and this is the useful part.** Under `set.Element: Set` / `set.Set: Collection`, the
sort `Set` is simultaneously:
  - a TARGET (the image of `set.Element`), so an occurrence that came from `Element` is final;
  - a SOURCE (mapping to `Collection`), so an occurrence that came from `set.Set` must map.

Both occurrences are the same InternPool Index. So no predicate ON THE SYMBOL can separate
them — the information needed is the symbol's PROVENANCE (which side of the overlay it
arrived from), which is exactly what delaboration erases when it stamps a resolved Index.

### Also tried and rejected: per-TOKEN stamping at delaboration

The next hypothesis was that provenance is known at DELABORATION time even if not at
re-elaboration, so `Delaborate` could stamp each symbol token exact-or-mappable
individually (`runPainted` + `painted_model`, threaded through `Accelerant.Builder`, with
`resolveSymbolTok` left untouched). The `exact` flag is the all-or-nothing version of this,
so per-token looked strictly better.

It gives the SAME 1→3 regression (`:431`, `:617`, `:1010`).

**Why — the thing I had wrong.** Stamping per token still has to DECIDE per token, and the
only predicate available is `isModelImage(sym)`, which is a property of the SYMBOL, not of
the occurrence. `isModelImage(Set)` is true for every occurrence of `Set`, whichever side it
came from, so deciding per token with it is the same decision as deciding per production —
hence byte-identical behaviour. Delaboration does not know the provenance either; by the
time it sees a term, both occurrences are the same Index.

**Where the information actually lives.** Provenance is fixed when the TERM is built — when
the producer substitutes a target sort for a source one. To fix this properly the painted
term itself must carry, per occurrence, which side of the overlay it came from (or the
producer must build in source space and let exactly one mapping happen, which is what
UNPAINTED production did and why it never hit this). Both are real redesigns of the
production path, not a flag. That is the open question; three cheap hypotheses are now
eliminated, which is the useful content of this note.

## STILL OWED: a regression fixture for the guard fix

The fix is verified by the CORPUS (six guarded models red→green) but has no fixture. Two
attempts failed, both A/B-tested with the fix disabled and passing either way — recorded so
the next attempt does not repeat them:

1. **`assoc_quantified` with a free local.** Every variable becomes an EIGENVARIABLE
   (`fix`-bound by the synthetic's own wrapper), so `abstractGoal` abstracts nothing, no
   param exists, and no guard is owed. `nparam=0`.
2. **Plain `assoc` on a ground equation inside nested `fix`es** (the shape of
   `std/group.b4m:433` `cancelLeft`), guard an opaque `pred good`, closure nominations for
   both `op` and `inv`. This DOES abstract params and DOES emit guards — instrumented
   `[PG] nparam=2 nguard=2` three times, matching the real case — and the guards discharge
   at the call site (`[DS] g=good(a) ok=true`). But it passes WITHOUT the fix too, because
   `stripGuards` never fires: `[SG]` showed ZERO leaked guards.

**What is actually going on** (two of my earlier guesses here were wrong; instrumented):

The toy fixture DOES reach the relativized form. `[PR]` on the cited lemma printed
`forall a: Tgt; good(a) -> forall b: Tgt; good(b) -> forall c: Tgt; good(c) -> …` — exactly
the guard-interleaved shape that leaks. So "the fixture never relativizes" was WRONG, as was
"the guard predicate must be a DEFINED pred rather than an opaque one".

The real distinction is narrower: in the toy model the leaked guard is still dischargeable
WITHOUT the pre-emitted param antecedents, because `good` is opaque and `dischargeGoal`
closes it from the call-site `fix a: GoodTgt` via the `goodClosed` / `goodInverse`
nominations (`[DS] g=good(a) ok=true`). The fix changes nothing observable there — which
makes that configuration a correct pass, not a missed counterexample.

The fix bites only where that call-site discharge is NOT available — i.e. where the guard
premise bottoms out on a bare PARAM with no enclosing guarded `fix`, as in `cancelLeft`
proved inside `std/group.b4m` under the model (binders at `Grp`, not at the refined cut).
Reproducing that in a 50-line fixture means reproducing "the theorem is proved in the SOURCE
file under the model", not "the theorem is cited from the target file" — which is the one
structural feature every toy attempt so far has gotten backwards.

Verify any candidate by A/B: stub `paramGuards` to return `&.{}`, rebuild, and confirm the
fixture FAILS. Three attempts have passed that test in the wrong direction (passing either
way); do not trust a candidate that has not been A/B'd.

### Tried and rejected: the "every mapping RHS is already-target" rule

A better-motivated version of the per-symbol idea, and worth recording because the REASONING
is sound and only the SCOPE is wrong.

Observation (verified across the corpus): every model mapping's right-hand side is a bare
LOCAL symbol of the declaring file — `Set`, `Collection`, `contains`, `RStar`, `recip`,
`unitsAssoc`. A grep for a namespace-QUALIFIED RHS anywhere in std returns nothing. That is
structural, not accidental: a model interprets the source theory's vocabulary in your own
terms. So a mapping target is final by construction, and no author annotation is needed —
the elaborator can know it from POSITION. (This is why the `^Set` pin syntax we sketched
turned out to be unnecessary.)

Implemented as `InternPool.isModelImage` (scan the overlay for `e.tgt == symbol`) applied in
`Elab.resolveSymbolTok` but SCOPED to `no_relativize` — i.e. only while elaborating a
synthetic, whose formulas were delaborated from already-target terms. Strictly narrower than
the earlier global attempt.

Result: the same 1→3 trade (`set.b4m:431`, `:617`, `:1010`).

**Why — the measurement that settles it.** Instrumentation showed the rule firing exactly
TWICE, both on `Set`, and those two pins are what break the three theorems. So inside a
synthetic an occurrence of `Set` can still be a SOURCE needing the shift. Concretely, under
`CollectionIsSet` both of these live inside synthetics under the same model:
  - `unionCommutative: forall a, b: Set; …` — binders are SOURCES, must map to `Collection`;
  - the `specialize` synthetic's `x: Element` — becomes a `Set` that is a TARGET, must not
    map again.
Both are the symbol `Set`; `isModelImage` answers yes to both.

Note the three breakages are all `tautology` steps, while the original failure is a
`specialize` step — the two accelerants need OPPOSITE answers for the same symbol.

**Conclusion.** The RHS rule is right about the MODEL BLOCK and gives no purchase inside
SYNTHETICS, because synthetic terms are not mapping RHSs — their `Set` occurrences have mixed
provenance. Together with the earlier three attempts this is now five independent ways of
asking "which occurrences are already-target?" after the fact, all defeated by the same
thing: provenance is per-occurrence, fixed when the term is built, and erased before any
later pass can ask. The fix has to record it AT CONSTRUCTION (or keep production unpainted,
where exactly one mapping ever happens).


## RESOLVED (2026-10-05) — a model is applied once per `using model(M)` citation

The five rejected attempts above all shared one wrong premise: that the engine must
DECIDE, per occurrence, whether a stamped symbol has already been mapped. It never has to.
The distinction is not a property to recover — it is a property of how the symbol got
there, and the token already records it:

| stamped `.symbol` | qualifier | meaning |
|---|---|---|
| from a TERM (a synthetic, a guard term) | `.universe` | FINAL — already in the space the proof runs in |
| from a NAME resolved early (`Expand`'s hygienic define bodies) | `.none` | source text — the ambient model interprets it, once |

`Elab.resolveSymbolTok` already honoured that split. The defect was that painted production
emitted its target-space terms through `Delaborate.run` (`.none`) instead of `runExact`
(`.universe`), and one site re-mapped an fvar's sort read off a term
(`demandUsing`'s `fvar_binds`). Each earlier attempt fixed ONE of the three producers
(`termExpr`, `sortTok`, the fvar bind) and read the resulting 1→3 as "the approach is
wrong"; the approach was right and incomplete. The complete set, applied together:

- `Accelerant.Builder.termExpr` → `Delaborate.runExact`; `symTok`/`sortTok` always final.
- `fvar_binds`: bind at the term's own sort; no `applyModel`.
- `no_relativize` / `pre_relativized` DELETED. They suppressed guard re-injection on a
  synthetic's binders — the guard-flavoured face of the same double application. With
  stamped symbols final, a synthetic's binder sort is its carrier and never re-refines, so
  there is nothing to suppress. (On the PRISTINE, unpainted tree the flag was already
  unnecessary — I only ever "proved" it necessary with the painted patch applied.)

What the user's framing got right that mine did not: "`model` is dead simple" — it IS.
`[using model(M) src.thm]` applies M to src.thm's proof ONCE (lazily, on demand; cached under
`(M, src_file).thm`). M's mapping table is origin → origin, built once by ModelTask and
independent of the model-space part of any namespace — which is why composition is DERIVED
(`composeModel`) rather than re-resolved, and why moving the table into `(M, src_file)`-keyed
IdentKV entries (an idea rejected along the way) would have been wrong. Every complication
here came from the unpainted accelerant path applying M a SECOND time inside one of those
applications and relying on the two agreeing.

Verified: `std/collection.b4m` green under painted production; every file the
stamped-everything-final attempt broke (`divisibility`, `field/order`, `group/{order,
generated,listing,counting,coset}`) green; all guarded-model fixtures green; two new
regression fixtures (`model_overlap_refinement`, `model_overlap_shift`) that fail without
this change. Full gates recorded in the commit.
