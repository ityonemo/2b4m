# ℤ_p[x] — the coefficient half is done, and a bad justification found upstream

## Done and committed

`std/integer/mod-n-domain.b4m` (`d787dcc`) proves **ℤ_p is an integral domain**:

    aClassIsZeroWhenTheModulusDivides   cls(a) = ZERO iff N | a
    aPrimeModulusHasNoZeroDivisors      prime N, x·y = 0  ->  x = 0 or y = 0

via `clsCongruent` against `cls(0)`, `mulHom` down to ℤ, then Euclid's lemma. ℤ_n already
had full ring structure (`mul`, `ONE`, `mulHom` at `mod-n.b4m:645`).

## The blocker for the polynomial half, and it is upstream

ℤ_p[x] having no zero divisors needs the **leading-product step**: for nonzero `p`, `q` of
degrees `m`, `n`,

    coeff(p·q, m+n) = p_m · q_n

because every other term of the convolution vanishes — `j < m` forces `m+n-j > n` so
`q_{m+n-j} = 0`, and `j > m` forces `p_j = 0`. With ℤ_p a domain, `p_m q_n ≠ 0`, so
`p·q ≠ 0`.

**That step is not proved anywhere.** `std/ring/polynomial.b4m` has 19 theorems; the only
degree-related one is `degreeIsUnique`. There is no leading-product lemma.

And `std/field/polynomial.b4m` **assumes** the consequence, twice:

    axiom aProductOfNonzerosIsNonzero   (:111)
    axiom degreeOfAProduct              (:114)

with this justification at `:106-108`:

> Stated as an axiom here rather than re-derived: its proof is the §17.1 convolution
> argument over a different coefficient sort, and `std/ring/polynomial.b4m` already carries
> the leading-term step it turns on.

**The second clause is false.** `ring/polynomial.b4m` carries no such step — checked
exhaustively (19 theorems, one mentions `degree`). So two axioms of F[x] rest on a stated
dependency that does not exist. They may well be *true* and standard, but the comment
misdescribes where they come from, and anyone reading it would believe the work was done
one layer down.

This matters beyond tidiness: `degreeOfAProduct` is load-bearing all over §17.2 and §17.3 —
the division algorithm, the cofactor degree bound, `theCofactorIsBounded`,
`anEqualDegreeCofactorIsConstant`, Theorem 17.17's degree contradiction. All of that rests
on an axiom whose justification is wrong about its own provenance.

## What finishing ℤ_p[x] actually costs

1. **The leading-product lemma** in `std/ring/polynomial.b4m` — a convolution collapse. The
   file's own `segmentPeelsAtTheBase` / `theTailIsASegmentBasedBelow` machinery is the right
   shape, so this is a fourth induction of the kind §17.1 already contains, not a new idea.
2. **ℤ_p[x] as a sort**, mapping `ring/polynomial.b4m`'s layer — now a known quantity after
   ℚ[x].
3. **Its domain property**, from (1) + `aPrimeModulusHasNoZeroDivisors`.
4. **Coefficient reduction ℤ[x] → ℤ_p[x]**, applying `cls` coefficientwise.

Doing (1) also lets `field/polynomial.b4m` **discharge** its two axioms instead of
asserting them, which is worth more than ℤ_p[x] is: it would remove an assumption from
under the whole of §17.2 and §17.3.

**Recommendation:** do (1) first and promote it to a theorem in both polynomial layers,
independently of Gauss. That is a real soundness improvement with a clear statement, and it
makes ℤ_p[x] mechanical afterwards.
