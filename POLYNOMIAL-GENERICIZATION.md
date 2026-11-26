# Polynomial genericization — what to move down, and the constraint on doing it

**Re-probed 2026-11-25.** The analysis holds. Recommendation 2 has LANDED; the rest are open.
Verified this round: `std/domain.b4m` and `std/domain/polynomial.b4m` still absent, and all 8
of ℚ[x]'s generic theorems are still in `std/rational/polynomial.b4m`. One figure corrected —
`using polynomial(` is now **176** sites, not 164; the substantive claim (not one is over
polynomial operations) is unchanged.

Each polynomial carrier re-declares the same primitives — `coeff`, `ZEROP`, `addP`, `negP`,
`mulP`, a `convolution` with its two recursion clauses, `degreeAtMost`, extensionality.
**That repetition is forced** and is not the problem: there are no parameterized sorts, so
`Poly` over a mapped coefficient ring is a different sort from `QPoly`, and a model maps
symbols rather than instantiating a functor.

The problem is the *theorems*. ℚ[x] hand-proves what `std/ring/polynomial.b4m` could carry
and transfer back in one line each — verified by probe: a `probeTransfer` citing
`ring_poly.negationPullsOutOfTheProduct` through `RationalPolynomialsOverARing` checks
strict. ℚ[x] is now 65 theorems with 7 model transfers.

**The cost of a missing generic theorem is not "someone proves it twice."** It is that the
second proof is written at the *wrong layer*, by induction, and then every later carrier
faces the same choice again.

## THE TEST: what the proof CITES, not what the statement mentions

A statement over `qcoeff` and `rational.mul` looks ℚ-specific; if its proof only ever cites
ring axioms, it is generic. `check --axioms <file> <theorem>` answers this in one command,
and should be the test, because the naming does not reveal it.

By that test ℚ[x] holds **8 misplaced-but-generic theorems**: `theTwoNegationsCancelInAProduct`,
`theNegationPullsOutOfTheProduct`, `qMulIsCommutative`, `theNegationsCoefficientFlips`,
`theNegationIsTheMinusOneScaling`, `scalingByAConstantScalesTheCoefficients`,
`theConstantMonomialProductAgreesCoefficientwise`, `negationPreservesTheDegree`.
(A ninth, `theNegationPullsOutOfTheConvolution`, is gone.) Running `--axioms` on each
returns **zero** field, domain, or ℚ-cut axioms — every ℚ-side axiom cited is a ring axiom
(`addIsAssociative`, `addZeroLeft`, `addNegLeft`, `addIsCommutative`, `mulAddDistribLeft`/
`Right`, `mulIsCommutative`, `mulOneLeft`) plus ℚ[x]'s own definitions and polynomial
axioms. Three of the eight already route one step through a model; the other five are
hand-written inductions of 46-90 lines.

Genuinely carrier-specific, and staying put: `everyCoefficientIsARatioOfIntegers` (rests on
`everyRationalIsAQuotientOfIntegers`), `aPowerCancelsTheReciprocalsPower` (rests on
`fieldInverse`), the `isInteger` cut theorems, and the `clearedSum` family.

## THE HARD CONSTRAINT: `polynomial` is a SCALAR-layer tactic

Know this before planning any polynomial work. `polynomial` binds `add`/`mul`/`ZERO`/`succ`
by **well-known name**, so over a carrier whose operations are `addP`/`mulP` it reports
`the goal has no add/mul structure`. All 176 `using polynomial(...)` sites in the corpus
pass `field` or `rational` — the **coefficient** ring — and not one is over polynomial
operations.

**So a polynomial ring identity cannot be discharged by a tactic.** Judson's one-line
`b = p − ad = p(1 − ar) + q(−as)` becomes four lemmas and about a dozen explicit steps.
Budget for stating distributivity, identity, associativity and negation lemmas by hand —
`std/field/polynomial.b4m`'s `polyMulIsAssociative` is a double-sum reindexing nothing
automates.

A tempting fix is to let `polynomial` accept an operation-name mapping. Uncosted, and it
interacts with the `--fast` trust boundary: the tactic binds vocabulary by name precisely so
a misbound operator is caught by the certificate rather than the decision (see
`design/acceleration.md`). Flagged, not proposed.

## Recommendations, in priority order

1. **Move ℚ[x]'s 8 generic theorems down and transfer them back.** The counterfactual
   transfer is verified to work. Mechanical, low risk, and it shrinks the largest offender.
2. **DONE — the right-hand companions exist.** `polyAddNegRight`, `polyAddZeroRight` and
   `polyMulAddDistribRight` are in both `std/ring/polynomial.b4m` and
   `std/field/polynomial.b4m`; `aSumCancelsItsRightSummand` is in `std/ring.b4m` and
   `std/ring/polynomial.b4m`.

   **Keep the rule that closed the gap: when adding a directional lemma, add both
   directions.** The mechanism is predictable — a layer gets built to satisfy one consumer,
   that consumer's proofs happen to be left-handed, and the right forms are never written;
   the absence is invisible until it blocks something. (The same gap at the scalar layer
   left `Ring` without an additive left-swap, which is the third argument `assoc_commut`'s
   explicit form needs, making the AC tactic unusable over `Ring` addition. Still open.)
3. **Introduce `std/domain.b4m` + `std/domain/polynomial.b4m`** (neither exists). An
   integral-domain layer between `ring` (has `mulZeroLeft`/`Right`, no cancellation) and
   `field` (adds inverses) would carry degree additivity, cancellation, and the
   scaling-reflects-a-degree-bound family. ℤ[x] and ℤ_n[x] for prime n get them free.

   **But note the real cost.** Several F[x] theorems *state* domain facts
   (`aNonzeroMultipleHasAtLeastTheDegree`, `aSmallDegreeMultipleIsTheZeroMultiple`,
   `anEqualDegreeCofactorIsConstant`) while `--axioms` shows the first resting on
   **`fieldInverse`**, not `noZeroDivisors` — inverses were available and were the shortest
   route. Moving it down is a **re-proof from the weaker axiom**, not a relocation. That is
   why this ranks below the mechanical moves: degree additivity is where the content is.
4. **Decide the `polynomial`-tactic question deliberately.** Either accept that polynomial
   identities are hand-written and say so in `GUIDE.md` (where it currently is not), or cost
   the operation-name mapping against the `--fast` boundary. Right now the limitation is
   folklore discovered by hitting it.

**The process rule worth keeping regardless:** *before inducting over a polynomial
recursion, check whether the fact belongs one layer down.* That is one `--axioms` call and a
grep of the layer below.

See `[[generic-polynomial-negation-algebra]]`, `[[sort-parameterization-via-model]]`,
`[[std-file-layout-principle]]`.
