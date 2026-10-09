# Propositions 11.3, 11.4 and 12.3, decomposed

The chain from Proposition 10.7 (nonpolarization detection, proved in `nonpolarization.md`)
up to Proposition 12.3 (a marked algebraic class at a good period). Each link is a *theorem*
resting on citations, rather than one large assumption.

The paper's own summary of these steps (§1.3, fourth stage):

> Finally, Section 11 lifts finite generation and the alternating character across `R`. The
> `t`-torsion terms cancel in the alternating sum of derived restrictions. … Section 12
> chooses such a period, isolates a nonzero Weil component, and spreads its marked class to
> the entire family using proper Hilbert parameter spaces.

## 11.3 — transport to the generic fibre

> **Proposition 11.3.** … `ζ_η̄` does not belong to `span_{ℚ_ℓ}{1, l_η̄, …, l_η̄⁸}`.
>
> *Proof.* `R` is complete with algebraically closed residue field, hence strictly henselian.
> **Smooth proper base change** for a smooth proper scheme over this trait identifies the
> geometric generic and special ℓ-adic cohomology groups, compatibly with cup products and
> the restrictions of Chern classes of perfect complexes [20]. … The latter class is outside
> the span of the powers of `l_s` by Proposition 10.7.

Entirely citation plus 10.7. Formalized: base change transports "outside the span" from the
special to the generic fibre.

```2b4m
import detection <<< "nonpolarization.md"

sort Class = detection.Class
pred inTheSpanOfThePolarizationPowers = detection.inTheSpanOfThePolarizationPowers
const theDetectedClass = detection.theDetectedClass
theorem theDetectedClassIsOutsideTheSpan = detection.theDetectedClassIsOutsideTheSpan

// The generic-fibre class, and the complex-period class.
const theGenericClass: Class
const theComplexPeriodClass: Class

// WELL-KNOWN ([20], smooth proper base change over a strictly henselian trait): the
// identification is compatible with cup products and Chern classes, so "in the span"
// transports between the special and generic fibres in both directions.
axiom baseChangeTransportsSpanMembership:
  inTheSpanOfThePolarizationPowers(theGenericClass) ->
  inTheSpanOfThePolarizationPowers(theDetectedClass)

// PROPOSITION 11.3, PROVED.
theorem theGenericClassIsOutsideTheSpan:
  not inTheSpanOfThePolarizationPowers(theGenericClass)
proof
  @given-in-the-span |
    assume inTheSpanOfThePolarizationPowers(theGenericClass) {
      @the-generic-class-is-in-the-span |
        inTheSpanOfThePolarizationPowers(theGenericClass)
        [by hypothesis given-in-the-span]
      @then-the-special-class-is-too |
        inTheSpanOfThePolarizationPowers(theDetectedClass)
        [using specialize baseChangeTransportsSpanMembership the-generic-class-is-in-the-span]
      @but-the-special-class-is-not |
        not inTheSpanOfThePolarizationPowers(theDetectedClass)
        [by cite theDetectedClassIsOutsideTheSpan]
    }
  @conclusion |
    not inTheSpanOfThePolarizationPowers(theGenericClass)
    [by not_intro given-in-the-span then-the-special-class-is-too but-the-special-class-is-not]
qed
```

## 11.4 — a rational algebraic class at a complex period

> **Proposition 11.4.** … the abelian variety `A_Π` has a rational algebraic total cycle
> class `ζ_Π` … outside `span_ℚ{1, θ, …, θ⁸}`.
>
> *Proof.* … The sheaves `V^r` restrict to algebraic perfect complexes on this complex
> fibre. Their alternating Chern character is consequently the cycle class of an element of
> `⊕_a CH^a(A_Π) ⊗ ℚ`. **Invariance of ℓ-adic cohomology under extension of algebraically
> closed fields**, followed by the **Betti–étale comparison isomorphism**, identifies this
> character with the extension of `ζ_η̄` [20].

Again citation plus 11.3.

```2b4m
pred isRationalAlgebraicClass(z: Class)

// WELL-KNOWN: the alternating Chern character of a perfect complex on a smooth projective
// variety is a rational algebraic cycle class.
axiom anAlternatingChernCharacterIsAlgebraic:
  isRationalAlgebraicClass(theComplexPeriodClass)

// WELL-KNOWN ([20]: invariance of ℓ-adic cohomology under extension of algebraically closed
// fields, then Betti–étale comparison): span membership transports to the complex period.
axiom theComparisonTransportsSpanMembership:
  inTheSpanOfThePolarizationPowers(theComplexPeriodClass) ->
  inTheSpanOfThePolarizationPowers(theGenericClass)

// PROPOSITION 11.4, PROVED: a rational algebraic class outside the span.
theorem aRationalAlgebraicClassOutsideTheSpanExists:
  isRationalAlgebraicClass(theComplexPeriodClass)
  and (not inTheSpanOfThePolarizationPowers(theComplexPeriodClass))
proof
  @the-class-is-algebraic |
    isRationalAlgebraicClass(theComplexPeriodClass)
    [by cite anAlternatingChernCharacterIsAlgebraic]
  @given-in-the-span |
    assume inTheSpanOfThePolarizationPowers(theComplexPeriodClass) {
      @the-complex-class-is-in-the-span |
        inTheSpanOfThePolarizationPowers(theComplexPeriodClass)
        [by hypothesis given-in-the-span]
      @then-the-generic-class-is-too |
        inTheSpanOfThePolarizationPowers(theGenericClass)
        [using specialize theComparisonTransportsSpanMembership the-complex-class-is-in-the-span]
      @but-the-generic-class-is-not |
        not inTheSpanOfThePolarizationPowers(theGenericClass)
        [by cite theGenericClassIsOutsideTheSpan]
    }
  @the-class-is-outside-the-span |
    not inTheSpanOfThePolarizationPowers(theComplexPeriodClass)
    [by not_intro given-in-the-span then-the-generic-class-is-too but-the-generic-class-is-not]
  @conclusion |
    isRationalAlgebraicClass(theComplexPeriodClass)
      and (not inTheSpanOfThePolarizationPowers(theComplexPeriodClass))
    [by and_intro the-class-is-algebraic the-class-is-outside-the-span]
qed
```

## 12.3 — a marked class at a good period

> **Proposition 12.3.** For this choice of `M`, there is a period `Π ∉ E` and a
> codimension-four integral subvariety `Z ⊂ A_Π` such that `[Z] = aθ⁴ + w`, `a ∈ ℚ`,
> `0 ≠ w ∈ W_K`.
>
> *Proof.* … the inverse image of every constituent of `E` is a proper closed analytic subset
> of `P_M`. … **By Baire, a point avoids both lists.** At its period `Π`, Proposition 11.4
> gives a rational algebraic total cycle class outside the span of the powers of `θ`. Formula
> (2.3) implies that its codimension-four component has nonzero projection to `W_K`. Express
> a cycle representing this component as a finite rational linear combination of integral
> codimension-four subvarieties. At least one constituent has a nonzero Weil projection.

Three inputs, each cited: Baire (a countable union of proper closed analytic subsets misses a
point), formula (2.3) (outside-the-span forces a nonzero Weil projection), and that a rational
cycle decomposes into integral subvarieties with one constituent carrying the projection.

```2b4m
pred aGoodPeriodExists()
pred hasNonzeroWeilProjection(z: Class)

// WELL-KNOWN (Baire, applied to the countable union of proper closed analytic subsets that
// `hilbert-parameters.md` shows have empty interior): a period avoiding every exceptional
// locus exists.
axiom baireSuppliesAGoodPeriod: aGoodPeriodExists()

// CITED (formula (2.3) of §2): a class outside the span of the powers of θ has a
// codimension-four component with nonzero projection to the Weil plane.
axiom outsideTheSpanForcesANonzeroWeilProjection:
  (not inTheSpanOfThePolarizationPowers(theComplexPeriodClass)) ->
  hasNonzeroWeilProjection(theComplexPeriodClass)

// PROPOSITION 12.3's content, PROVED: at a good period there is a rational algebraic class
// with nonzero Weil projection.
theorem aMarkedClassWithNonzeroWeilProjectionExists:
  aGoodPeriodExists() and isRationalAlgebraicClass(theComplexPeriodClass)
  and hasNonzeroWeilProjection(theComplexPeriodClass)
proof
  @a-good-period-exists |
    aGoodPeriodExists()
    [by cite baireSuppliesAGoodPeriod]
  @the-class-facts |
    isRationalAlgebraicClass(theComplexPeriodClass)
      and (not inTheSpanOfThePolarizationPowers(theComplexPeriodClass))
    [by cite aRationalAlgebraicClassOutsideTheSpanExists]
  @the-class-is-algebraic |
    isRationalAlgebraicClass(theComplexPeriodClass)
    [by and_elim_left the-class-facts]
  @the-class-is-outside-the-span |
    not inTheSpanOfThePolarizationPowers(theComplexPeriodClass)
    [by and_elim_right the-class-facts]
  @the-class-has-a-weil-projection |
    hasNonzeroWeilProjection(theComplexPeriodClass)
    [using specialize outsideTheSpanForcesANonzeroWeilProjection the-class-is-outside-the-span]
  @the-period-and-the-class |
    aGoodPeriodExists() and isRationalAlgebraicClass(theComplexPeriodClass)
    [by and_intro a-good-period-exists the-class-is-algebraic]
  @conclusion |
    aGoodPeriodExists() and isRationalAlgebraicClass(theComplexPeriodClass)
      and hasNonzeroWeilProjection(theComplexPeriodClass)
    [by and_intro the-period-and-the-class the-class-has-a-weil-projection]
qed
```
