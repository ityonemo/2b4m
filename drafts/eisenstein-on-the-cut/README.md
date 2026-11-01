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

## The reproof plan, after measuring (2026-11-01)

**The reproof is about half what I first estimated**, because two of the four pieces do not
need reproving at all:

| piece | verdict |
|---|---|
| `modNPolynomialsHaveNoZeroDivisors` | **cite directly.** It is a fact about ℤ_N[x] ALONE — no ℚ anywhere in it — so no transfer is involved. Probed: `reduce-probe.b4m` cites it green. |
| `is_prime(N)` on the cut | **not needed.** `N` is a fixed `Int` constant of `mod_n`, so Eisenstein's prime never has to live on ℚ's cut. Only the DIVISIBILITY of a ℚ-cut coefficient by N must cross. |
| `reduce` + its 3 theorems | **must be rebuilt** against the cut (~230 lines: `reduceCommutesWithTheConvolution` is the bulk at 132). |
| `theDenominatorCannotExceedOne` | **must be rebuilt** (~115 lines), but its shape is unchanged. |

### The design decision, stated because it is load-bearing

The cut needs its own class map `qcls: Q → Zn requires isInteger(a)`, axiomatised DIRECTLY on
ℚ's integers rather than by composing with a `Q → Int` conversion. That is deliberate:

- the number-tower refactor **dropped the `from*` functions on purpose**
  ([[number-tower-fromis-refactor]]), keeping `is*` as primitive-closure predicates. Adding a
  `Q → Int` embedding to make this work would cut against a standing design decision.
- `cls: Int → Zn` cannot be re-pointed at the cut, because `mod_n` keys it to
  `std/integer.b4m`'s `Int` and transferring `mod_n` hits the nested-transfer wall
  (`std/peano.b4m` is in its axiom base).

**The cost of that choice, named honestly:** `qcls` is a NEW primitive with three new axioms
(`qclsZero`, `qclsAdd`, `qclsMul`). They are the same homomorphism laws `cls` has, so they are
not a new mathematical assumption — but they ARE new axioms, and `--axioms` will show them.
The alternative (an embedding) trades three axioms for a function the refactor removed.
Recording the trade rather than making it silently.

### Still to settle

`qclsCongruent` — "qcls(a) = qcls(b) iff N divides a − b" — is what links the cut's class map
to divisibility, and it is what `aSurvivingCoefficientSurvivesReduction` needs. Its right-hand
side mixes an `Int` modulus with ℚ-cut operands, so the divisibility notion has to be stated
carefully. This is the one place the design could still fail.
