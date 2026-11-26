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

1. **`std/domain.b4m` EXISTS (2026-11-25); `std/domain/polynomial.b4m` does not.** The scalar
   layer landed: commutative ring + `noZeroDivisors` (an AXIOM here, a THEOREM in `field.b4m`)
   + `oneNotZero` (needed, since the zero ring satisfies `noZeroDivisors` vacuously), modelling
   `ring.b4m` so the ring corpus transfers in. Carries `aProductOfNonzerosIsNonzero` and
   `cancelMulLeft`, the multiplicative cancellation a ring lacks. A FIELD now models it
   (`DomainIsField`, `field.b4m:489`), discharging the domain's axiom with the field's own
   theorem — so the layer pays off above a field too, not only below.

   **THE ARCHITECTURAL FINDING, measured: the degree facts never needed inverses.** All three
   F[x] targets rest on `fieldInverse`, but tracing where it ENTERS shows a single step:

   ```
   aNonzeroMultipleHasAtLeastTheDegree (96 ln)
     -> degreeOfAProduct (83 ln)                      degree additivity
          -> aProductOfNonzerosIsNonzero (68 ln)
               -> field.noZeroDivisors                <-- the ONLY field use
          -> theProductsLeadingCoefficient            already generic, at ring layer
          -> theProductVanishesAboveTheDegreeSum      already generic, at ring layer
          -> theDegreeSumBoundsTheProduct             generic; now ported
   ```

   The source itself comments that step *"a field has no zero divisors"*. So the re-proof is
   confined to one lemma, not spread through the chain.

   **WHAT REMAINS is a ~700-line project, not a port.** 2b4m has no sort subsumption, so D[x]
   must be a third independent polynomial sort mirroring F[x]'s ~250-line primitive block (11
   axioms, `coeff`/`ZEROP`/`degree`/`degreeAtMost`, `convolution`, `mulP`/`addP`/`negP`), plus
   `DomainPolyModelsRingPoly` and `FieldPolyModelsDomainPoly` models, then
   `aProductOfNonzerosIsNonzero` and `degreeOfAProduct` re-proved, then the three targets
   (`anEqualDegreeCofactorIsConstant` is in `std/field/monic.b4m:338`, not `polynomial.b4m`).
   About 150 lines of new mathematics and 550 of structural mirroring.

   **THEN CLOSE IT OUT (user, 2026-11-25): wire ℤ[x] and ℤ_n[x].** Both already declare a ring
   model (`IntegerPolynomials` at `std/integer/polynomial.b4m:107`, `ModNPolynomials` at
   `std/integer/mod-n-polynomial.b4m:95`), so each needs the domain model beside it.
   **ℤ_p is READY**: `std/integer/mod-n-domain.b4m:64` already proves
   `is_prime(N) -> mul(x, y) = ZERO -> (x = ZERO or y = ZERO)`, built for Gauss's Lemma (AATA
   §17.3), which needed exactly "ℤ_p[x] is an integral domain". **ℤ is NOT**: no zero-divisor
   fact exists in `std/integer*`, so proving it is a prerequisite, reachable from the sign
   trichotomy at `std/integer/order.b4m:1141`.

2. **Decide the `polynomial`-tactic question deliberately.** Either accept that polynomial
   identities are hand-written and say so in `GUIDE.md` (where it still is not), or cost the
   model-synthesis idea against the `--fast` boundary, where `model` already drops the
   per-axiom obligation-coverage check. PAINPOINTS 22 carries the idea.

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
