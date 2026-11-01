# ℤ[x] as a sub-ring of ℚ[x] — the route that closes 17.15's packaging

**User's suggestion, 2026-11-01, and it works.** Instead of bridging two unrelated polynomial
SORTS (`IntPoly` and `QPoly`), cut ℤ[x] out of ℚ[x] with `hasIntegerCoefficients` and transfer
`std/ring/polynomial.b4m`'s corpus onto the cut. Then "no factorization in ℤ[x]" and
"irreducible over ℚ" are statements about *the same objects*, and the vocabulary gap that
blocked Theorem 17.15's packaging is simply gone.

This is strictly better than what I had built. My `std/integer/polynomial.b4m` route needed an
embedding between sorts that does not exist; the cut needs none.

## State

- `closure.b4m` — the cut is a SUB-RING. Six closure theorems, strict-green:
  `theZeroPolynomialIsIntegral`, `theUnitPolynomialIsIntegral`, `theSumIsIntegral`,
  `theNegationIsIntegral`, `theConvolutionIsIntegral`, `theProductIsIntegral`.
  Only the product is nontrivial — a coefficient of a product is a CONVOLUTION, so
  integrality rides the convolution's own recursion (induction on the convolution index with
  the output index fixed, the §17.1 reindexing shape).
- `probe.b4m` — the guarded model `ZPolyInQPoly` maps BOTH `ring` (onto ℚ's integer cut) and
  `ring_poly` (onto the polynomial cut) in one block, and `polyMulIsCommutative` transfers.
  Strict-green.

## What the probe established

1. **A doubly-cut model works here.** `ring.Ring: Integer` (ℚ where `isInteger`) *and*
   `ring_poly.Poly: ZPolyCut` (QPoly where `hasIntegerCoefficients`) in the same block. This
   is NOT the nested-transfer wall — both cuts live in ℚ's space, so nothing needs ℕ to be two
   sorts at once.
2. **Relativization interleaves guards with binders.** A transferred
   `forall p, q; … = …` arrives as `forall p; guard(p) -> forall q; guard(q) -> …`, not with
   the guards hoisted. The consuming statement must be written in that shape.
3. **Going DOWN a layer again pays.** `ring_poly` is the source, not `fieldpoly` — same lesson
   as ℚ[x]'s leading-coefficient law. Cost is the same: the cut must declare every helper the
   source proof inducts on, which ℚ[x] already has (`qtailConvolution`, `qsegment`).

## Remaining to finish 17.15

- **Eisenstein's engine on the cut.** `theDenominatorCannotExceedOne` is the key fact and it
  rests on ℤ_N[x] + the `cls` reduction (47 axioms — mod-p machinery IS load-bearing in that
  proof, whatever Judson's own argument does). Transferring it needs ℤ_N[x] mapped too, or the
  argument reproved against the cut.
- **The sign bookkeeping.** Judson's `p ∤ a_n` and `p² ∤ a_0` are what PRODUCE "p misses a
  coefficient of each factor"; my `eisensteinForcesTheFullDegree` takes that conclusion as two
  hypotheses instead of deriving it.
- **A fixed example polynomial**, then irreducibility of it.

## DONE 2026-11-01 — landed as `std/rational/integer-polynomial.b4m`

12 theorems, strict-green, 60 axioms, no holes. The probes that established the route are
deleted; the file supersedes them.

**What the measurement changed.** My first estimate was ~400 lines. It came out at ~230,
because two of the four pieces needed no reproving at all:

- `modNPolynomialsHaveNoZeroDivisors` **cites directly** — a fact about ℤ_N[x] with no ℚ in
  it, so no transfer is involved.
- `is_prime(N)` is **not needed on the cut**. Keeping the modulus a ℚ-cut element `QN` means
  ℤ_N[x] is untouched and only `qcls`'s laws cross between them.

**The axiom trade, as landed.** `qcls` is a new primitive with four axioms mirroring `mod_n`'s
`cls`. Not a new mathematical assumption, but four new axioms. Both alternatives were closed:
a `Q → Int` embedding was dropped on purpose by the number-tower refactor, and `cls` cannot be
re-pointed because transferring `mod_n` hits the nested-transfer wall.

**Two engine/discipline lessons worth carrying:**

1. **A `requires` guard cannot sit on a func that appears under a quantifier binding what the
   guard is about.** `forall k; … qcls(conv(p,q,i,k)) …` owes `isInteger` at a `k` not yet
   fixed, and no proof step can discharge it there — not even inside an `assume`'s formula,
   where the obligation lands before any step runs. The fix is to drop the guard and put the
   integrality hypotheses on the axioms, which is how the rest of `std/` handles a partial
   operation. The dead-step lint then located every step that existed only to feed the removed
   guards.
2. **`check --library` earns its keep on speculative axioms.** I posited `isInteger(QN)`
   because it looked like something a modulus should satisfy. `dividesIntegrally` constrains
   only the quotient, never the divisor, so it was never used — and the gate rejected the
   commit rather than letting a dead axiom sit in the corpus looking load-bearing.

## Still open for 17.15

The cut now has the reduction engine, so what remains is Eisenstein's own bookkeeping:

- **the sign argument.** Judson's `p ∤ a_n` and `p² ∤ a_0` are what PRODUCE "p misses a
  coefficient of each factor" — `p | a_0 = b_0 c_0` with `p² ∤ a_0` forces p to divide exactly
  one of them, and `p ∤ a_n` forces `p ∤ b_m`. `eisensteinForcesTheFullDegree` takes that
  conclusion as two hypotheses instead of deriving it.
- **a fixed example polynomial**, then its irreducibility — the user's steps 3 and 4.
