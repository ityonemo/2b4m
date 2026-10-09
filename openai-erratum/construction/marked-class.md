# Proposition 12.3, decomposed

The output of Sections 2 through 11 of the withdrawn manuscript. It began as a single
assumed existential; it is now **proved**, from the detection chain of `../detection/` and
two citations for §12.3's last move.

## What it says

> **Proposition 12.3.** For this choice of `M`, there is a period `Π ∉ E` and a
> codimension-four integral subvariety `Z ⊂ A_Π` such that
> `[Z] = aθ⁴ + w`, `a ∈ ℚ`, `0 ≠ w ∈ W_K`.

## Why it still lives in its own file

Its dependency chain is the entire construction:

    Prop 12.3  <-  Prop 11.4  <-  Prop 11.3  <-  Prop 10.7
               <-  Sections 8-10 (theta section ring, mirror symmetry)
               <-  Sections 4-7  (weighted Floer module, sign bookkeeping)
               <-  Section 3     (the Lagrangian L)
               <-  §3.4          (stabilization traces of [6])  <-- THE ERROR IS HERE

`openai-erratum/signs.md` checks the sign identities of Section 6 and finds them valid; the
withdrawal points instead at §3.4's traces, whose *internal* arithmetic is also consistent
(`φ → φ₁ : −1`, `φ₁ → φ : +1` at k = 4) but which depends on the convention imported from
reference [6]. A formalization that *axiomatized* this proposition could not see any of
that — which is the reason it is not axiomatized. The chain is wired through Lemma 3.6, so
checking Theorem 1.1 in `openai-erratum/` reaches §3.4 and fails there.

```2b4m
import legendrian <<< "../legendrian/stabilization-traces.md"
import transport <<< "../detection/transport.md"

sort Period
sort CycleClass

pred inParameterSet(p: Period)
pred avoidsExceptional(p: Period)
pred isAlgebraic(p: Period, z: CycleClass)
pred inWeilPlane(p: Period, z: CycleClass)
pred isZeroClass(z: CycleClass)
pred representedByIntegralSubvarietiesAt(p: Period, z: transport.Class)
const polarizationPower: CycleClass
func scale(q: CycleClass, z: CycleClass) => CycleClass
func add(z: CycleClass, w: CycleClass) => CycleClass

// PROPOSITION 12.3, now wired end to end rather than assumed. It is CONDITIONAL on Lemma 3.6
// (`../legendrian/stabilization-traces.md`), whose outermost stabilization trace is the
// defect, so an error at §3.4 surfaces when checking Theorem 1.1.
//
// The chain 10.7 -> 11.3 -> 11.4 -> 12.3 is PROVED, in `../detection/nonpolarization.md` and
// `../detection/transport.md`: nonpolarization detection, transport to the generic fibre by
// smooth proper base change, transport to a complex period by Betti-étale comparison, and the
// Baire choice with the Weil-projection extraction. Each rests on citations.
//
// §12.3's LAST MOVE, decomposed into its two cited pieces rather than asserted whole. The
// move is: a rational algebraic class with nonzero Weil projection becomes an INTEGRAL
// subvariety in the marked form a*theta^4 + w. The paper does it in two steps, and each is
// standard:
//
//   (a) A rational algebraic class is a finite rational combination of classes of integral
//       subvarieties. That is the DEFINITION of the image of CH^4 ⊗ Q, nothing more.
//   (b) Since the Weil projection of the combination is nonzero, some constituent has nonzero
//       Weil projection; clearing the denominator and splitting off the polarization component
//       gives a*theta^4 + w with w the Weil part. Linear algebra on the decomposition
//       H^8 = <theta^4> ⊕ W_K ⊕ (rest) of §2.
//
// Neither step is particular to this paper, and both are cited in §12.3.
axiom aRationalAlgebraicClassIsACombinationOfSubvarieties:
  transport.isRationalAlgebraicClass(transport.theComplexPeriodClass) ->
  (exists p: Period; inParameterSet(p) and avoidsExceptional(p) and
  representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass))

axiom aNonzeroWeilProjectionSelectsAMarkedConstituent: forall p: Period;
  transport.aGoodPeriodExists() ->
  inParameterSet(p) -> avoidsExceptional(p) ->
  representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass) ->
  transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
  (exists a: CycleClass; exists w: CycleClass;
  inWeilPlane(p, w) and (not isZeroClass(w)) and
  isAlgebraic(p, add(scale(a, polarizationPower), w)))

// §12.3's last move, PROVED from (a) and (b).
theorem aCycleClassDecomposesIntoIntegralSubvarieties:
  transport.aGoodPeriodExists() ->
  transport.isRationalAlgebraicClass(transport.theComplexPeriodClass) ->
  transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
  (exists p: Period;
  inParameterSet(p) and avoidsExceptional(p) and
  (exists a: CycleClass; exists w: CycleClass;
  inWeilPlane(p, w) and (not isZeroClass(w)) and
  isAlgebraic(p, add(scale(a, polarizationPower), w))))
proof
  @given-a-good-period |
    assume transport.aGoodPeriodExists() {
      @a-good-period-exists |
        transport.aGoodPeriodExists()
        [by hypothesis given-a-good-period]
      @given-the-class-is-rational-algebraic |
        assume transport.isRationalAlgebraicClass(transport.theComplexPeriodClass) {
          @the-class-is-rational-algebraic |
            transport.isRationalAlgebraicClass(transport.theComplexPeriodClass)
            [by hypothesis given-the-class-is-rational-algebraic]
          @given-a-nonzero-weil-projection |
            assume transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) {
              @the-weil-projection-is-nonzero |
                transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass)
                [by hypothesis given-a-nonzero-weil-projection]
              @a-representing-period-exists |
                exists p: Period; inParameterSet(p) and avoidsExceptional(p) and
                  representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass)
                [using specialize aRationalAlgebraicClassIsACombinationOfSubvarieties the-class-is-rational-algebraic]
              @with-the-representing-period |
                unpack p: Period from a-representing-period-exists {
                  @the-period-facts |
                    inParameterSet(p) and avoidsExceptional(p) and
                      representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass)
                    [by hypothesis with-the-representing-period]
                  @the-period-is-in-the-parameter-set |
                    inParameterSet(p)
                    [using tautology the-period-facts]
                  @the-period-avoids-the-exceptional-loci |
                    avoidsExceptional(p)
                    [using tautology the-period-facts]
                  @the-class-is-represented-there |
                    representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass)
                    [using tautology the-period-facts]
                  @a-marked-constituent-exists |
                    exists a: CycleClass; exists w: CycleClass;
                      inWeilPlane(p, w) and (not isZeroClass(w)) and
                      isAlgebraic(p, add(scale(a, polarizationPower), w))
                    [using specialize aNonzeroWeilProjectionSelectsAMarkedConstituent(p) a-good-period-exists the-period-is-in-the-parameter-set the-period-avoids-the-exceptional-loci the-class-is-represented-there the-weil-projection-is-nonzero]
                  @the-period-is-good |
                    inParameterSet(p) and avoidsExceptional(p)
                    [by and_intro the-period-is-in-the-parameter-set the-period-avoids-the-exceptional-loci]
                  @the-period-works |
                    inParameterSet(p) and avoidsExceptional(p) and
                      (exists a: CycleClass; exists w: CycleClass;
                      inWeilPlane(p, w) and (not isZeroClass(w)) and
                      isAlgebraic(p, add(scale(a, polarizationPower), w)))
                    [by and_intro the-period-is-good a-marked-constituent-exists]
                  @conclusion-a-marked-period-exists |
                    exists q: Period;
                      inParameterSet(q) and avoidsExceptional(q) and
                      (exists a: CycleClass; exists w: CycleClass;
                      inWeilPlane(q, w) and (not isZeroClass(w)) and
                      isAlgebraic(q, add(scale(a, polarizationPower), w)))
                    [by exists_intro(p) the-period-works]
                }
              @conclusion-a-marked-period |
                exists q: Period;
                  inParameterSet(q) and avoidsExceptional(q) and
                  (exists a: CycleClass; exists w: CycleClass;
                  inWeilPlane(q, w) and (not isZeroClass(w)) and
                  isAlgebraic(q, add(scale(a, polarizationPower), w)))
                [by exists_elim with-the-representing-period]
            }
          @conclusion-weil-projection-gives |
            transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
              (exists q: Period;
              inParameterSet(q) and avoidsExceptional(q) and
              (exists a: CycleClass; exists w: CycleClass;
              inWeilPlane(q, w) and (not isZeroClass(w)) and
              isAlgebraic(q, add(scale(a, polarizationPower), w))))
            [by implies_intro given-a-nonzero-weil-projection]
        }
      @conclusion-rational-algebraic-gives |
        transport.isRationalAlgebraicClass(transport.theComplexPeriodClass) ->
          transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
          (exists q: Period;
          inParameterSet(q) and avoidsExceptional(q) and
          (exists a: CycleClass; exists w: CycleClass;
          inWeilPlane(q, w) and (not isZeroClass(w)) and
          isAlgebraic(q, add(scale(a, polarizationPower), w))))
        [by implies_intro given-the-class-is-rational-algebraic]
    }
  @conclusion |
    transport.aGoodPeriodExists() ->
      transport.isRationalAlgebraicClass(transport.theComplexPeriodClass) ->
      transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
      (exists p: Period;
      inParameterSet(p) and avoidsExceptional(p) and
      (exists a: CycleClass; exists w: CycleClass;
      inWeilPlane(p, w) and (not isZeroClass(w)) and
      isAlgebraic(p, add(scale(a, polarizationPower), w))))
    [by implies_intro given-a-good-period]
qed

theorem theConstructionDeliversAMarkedClass:
  legendrian.anEmbeddedLagrangianExists() ->
  (exists p: Period;
  inParameterSet(p) and avoidsExceptional(p) and
  (exists a: CycleClass; exists w: CycleClass;
  inWeilPlane(p, w) and (not isZeroClass(w)) and
  isAlgebraic(p, add(scale(a, polarizationPower), w))))
proof
  @given-an-embedded-lagrangian |
    assume legendrian.anEmbeddedLagrangianExists() {
      @the-detection-chain |
        transport.aGoodPeriodExists()
          and transport.isRationalAlgebraicClass(transport.theComplexPeriodClass)
          and transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass)
        [by cite transport.aMarkedClassWithNonzeroWeilProjectionExists]
      @the-period-and-the-class |
        transport.aGoodPeriodExists()
          and transport.isRationalAlgebraicClass(transport.theComplexPeriodClass)
        [by and_elim_left the-detection-chain]
      @a-good-period-exists |
        transport.aGoodPeriodExists()
        [by and_elim_left the-period-and-the-class]
      @the-class-is-algebraic |
        transport.isRationalAlgebraicClass(transport.theComplexPeriodClass)
        [by and_elim_right the-period-and-the-class]
      @the-class-has-a-weil-projection |
        transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass)
        [by and_elim_right the-detection-chain]
      @conclusion-a-marked-class-exists |
        exists p: Period;
          inParameterSet(p) and avoidsExceptional(p) and
          (exists a: CycleClass; exists w: CycleClass;
          inWeilPlane(p, w) and (not isZeroClass(w)) and
          isAlgebraic(p, add(scale(a, polarizationPower), w)))
        [using specialize aCycleClassDecomposesIntoIntegralSubvarieties a-good-period-exists the-class-is-algebraic the-class-has-a-weil-projection]
    }
  @conclusion |
    legendrian.anEmbeddedLagrangianExists() ->
      (exists p: Period;
      inParameterSet(p) and avoidsExceptional(p) and
      (exists a: CycleClass; exists w: CycleClass;
      inWeilPlane(p, w) and (not isZeroClass(w)) and
      isAlgebraic(p, add(scale(a, polarizationPower), w))))
    [by implies_intro given-an-embedded-lagrangian]
qed

theorem aMarkedAlgebraicClassExistsAtSomeGoodPeriod: exists p: Period;
  inParameterSet(p) and avoidsExceptional(p) and
  (exists a: CycleClass; exists w: CycleClass;
  inWeilPlane(p, w) and (not isZeroClass(w)) and
  isAlgebraic(p, add(scale(a, polarizationPower), w)))
proof
  @lemma-three-six-gives-an-embedded-lagrangian |
    legendrian.anEmbeddedLagrangianExists()
    [by cite legendrian.anEmbeddedSpinLagrangianExists]
  @conclusion |
    exists p: Period;
      inParameterSet(p) and avoidsExceptional(p) and
      (exists a: CycleClass; exists w: CycleClass;
      inWeilPlane(p, w) and (not isZeroClass(w)) and
      isAlgebraic(p, add(scale(a, polarizationPower), w)))
    [using specialize theConstructionDeliversAMarkedClass lemma-three-six-gives-an-embedded-lagrangian]
qed
```
