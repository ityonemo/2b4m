# Polynomial genericization — what is left

**Recommendations 1 and 2 are DONE** (2026-11-25). All six of ℚ[x]'s misplaced-but-generic
theorems now live at the ring layer and transfer back in one line each; ℚ[x] shrank 365 lines,
6618 → 6253. The right-hand companion lemmas exist. Two recommendations remain.

## THE TEST, which is the reusable part

**What the proof CITES, not what the statement mentions.** A statement over `qcoeff` and
`rational.mul` looks ℚ-specific; if its proof only ever cites ring axioms, it is generic.
`check --axioms <file> <theorem>` answers it in one command, and the naming never reveals it.

**Its limit, measured:** `--axioms` sees what a proof cites, not how much unported scaffolding
sits beneath. `negationPreservesTheDegree` read as generic and was — but porting it meant
first porting a 75-line helper. Survey the dependency chain, not just the axiom list.

**And a survey goes stale from your own work.** An agent surveying six dependencies up front
ported one of them mid-run, then reported the original count — concluding wrongly that a
three-deep chain blocked it, when five of six were by then already in place. Re-check
immediately before acting.

## THE HARD CONSTRAINT: `polynomial` is a SCALAR-layer tactic

`polynomial` binds `add`/`mul`/`ZERO`/`succ` by **well-known name**, so over a carrier whose
operations are `addP`/`mulP` it reports `the goal has no add/mul structure`. All 176
`using polynomial(...)` sites pass `field` or `rational` — the **coefficient** ring — and not
one is over polynomial operations.

So a polynomial ring identity cannot be discharged by a tactic. `std/field/polynomial.b4m`'s
`polyMulIsAssociative` is a double-sum reindexing nothing automates.

**The cost is step-specific, not uniform.** Porting `theNegationIsTheMinusOneScaling` turned
one `[using polynomial(rational)]` into two explicit steps; the last two ports needed none,
being pure coefficientwise reasoning. Budget per scalar-tactic step in the proof being moved,
not per proof. (PAINPOINTS 22 carries this, with the parked idea of letting `polynomial`
synthesize over a MODEL — which would read ring structure through the model's own `:` map, so
a misbound operator becomes a model error rather than a silently wrong normalization.)

## Remaining recommendations

1. **Introduce `std/domain.b4m` + `std/domain/polynomial.b4m`** (neither exists). An
   integral-domain layer between `ring` (has `mulZeroLeft`/`Right`, no cancellation) and
   `field` (adds inverses) would carry degree additivity, cancellation, and the
   scaling-reflects-a-degree-bound family. ℤ[x] and ℤ_n[x] for prime n get them free.

   **The real cost, which is why this ranks last.** Several F[x] theorems *state* domain facts
   (`aNonzeroMultipleHasAtLeastTheDegree`, `aSmallDegreeMultipleIsTheZeroMultiple`,
   `anEqualDegreeCofactorIsConstant`) while `--axioms` shows the first resting on
   **`fieldInverse`**, not `noZeroDivisors` — inverses were available and were the shortest
   route. Moving it down is a **re-proof from the weaker axiom**, not a relocation. Degree
   additivity is where the content is.

2. **Decide the `polynomial`-tactic question deliberately.** Either accept that polynomial
   identities are hand-written and say so in `GUIDE.md` (where it still is not), or cost the
   model-synthesis idea against the `--fast` boundary, where `model` already drops the
   per-axiom obligation-coverage check.

## The process rule worth keeping regardless

*Before inducting over a polynomial recursion, check whether the fact belongs one layer down.*
One `--axioms` call and a grep of the layer below.

**And when adding a directional lemma, add both directions.** The gap mechanism is
predictable: a layer gets built to satisfy one consumer, that consumer's proofs happen to be
left-handed, and the right forms are never written — invisible until something blocks. Found
three times in this work alone (`std/ring.b4m` had no `neg(ZERO) = ZERO`, hence no
nonzero-negation fact; and `negationOfZeroIsZero` was never re-exported into
`ring/polynomial.b4m`). The same gap at the scalar layer still leaves `Ring` without an
additive left-swap, which `assoc_commut`'s explicit form needs.

See `[[generic-polynomial-negation-algebra]]`, `[[sort-parameterization-via-model]]`,
`[[std-file-layout-principle]]`.
