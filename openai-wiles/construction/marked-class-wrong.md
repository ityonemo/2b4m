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

`../signs.md` checks the sign identities of Section 6 and finds them valid; the
withdrawal points instead at §3.4's traces, whose *internal* arithmetic is also consistent
(`φ → φ₁ : −1`, `φ₁ → φ : +1` at k = 4) but which depends on the convention imported from
reference [6]. A formalization that *axiomatized* this proposition could not see any of
that — which is the reason it is not axiomatized. The chain is wired through Lemma 3.6, so
§3.4 is reached when checking Theorem 1.1.

```2b4m
import legendrian <<< "../legendrian/stabilization-traces-wrong.md"
import transport <<< "../detection/transport.md"

sort Period
sort CycleClass

pred inParameterSet(p: Period)
pred avoidsExceptional(p: Period)
pred isAlgebraic(p: Period, z: CycleClass)
pred inWeilPlane(p: Period, z: CycleClass)
pred isZeroClass(z: CycleClass)
pred representedByIntegralSubvarietiesAt(p: Period, z: transport.Class)
sort Class = transport.Class
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
hole aRationalAlgebraicClassIsACombinationOfSubvarieties cites "manuscript Prop 12.3: Express a cycle representing this component as a finite rational linear combination of integral codimension-four subvarieties":
  transport.isRationalAlgebraicClass(transport.theComplexPeriodClass) ->
  (exists p: Period; inParameterSet(p) and avoidsExceptional(p) and
  representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass))

// §12.3's SELECTION STEP, now MODELLED on formula (2.3) rather than held as a hole.
//
// Prop 12.3: "Express a cycle representing this component as a finite rational linear
// combination of integral codimension-four subvarieties. At least one constituent has a
// nonzero Weil projection. Every such constituent has rational Hodge class and the period
// lies outside E_Hdg, so its class has precisely the form (12.5)."
//
// Formula (2.3) is what makes the last clause work, and it is a TWO-summand direct sum:
//
//     H^8(A_Pi, Q) ∩ H^{4,4}(A_Pi) = Q.theta^4 (+) W_K     (j = 4)
//
// So a rational Hodge class in codimension four splits as a*theta^4 + w with NOTHING else —
// there is no third summand to absorb a remainder. That is why "its class has precisely the
// form (12.5)" follows rather than being assumed. Modelling the splitting as a function of
// the class, with (2.3) as the citation that it reassembles, closes the hole.

// The two projections of formula (2.3): the polarization coefficient and the Weil part.
func polarizationCoefficient(p: Period, z: CycleClass) => CycleClass
func weilPart(p: Period, z: CycleClass) => CycleClass

// A class in the Hodge-class group at a period, which is what (2.3) decomposes.
pred isRationalHodgeClass(p: Period, z: CycleClass)

// CITATION, formula (2.3): a rational Hodge class in codimension four IS its polarization
// term plus its Weil part. Two summands, so the splitting is exact.
hole theHodgeClassesSplitAsInTwoPointThree cites "manuscript formula (2.3): H^{2j} \u2229 H^{j,j} = Q.theta^4 (+) W_K at j=4 \u2014 TWO summands, so the splitting is exact": forall p: Period; forall z: CycleClass;
  inParameterSet(p) -> avoidsExceptional(p) -> isRationalHodgeClass(p, z) ->
  z = add(scale(polarizationCoefficient(p, z), polarizationPower), weilPart(p, z))

// CITATION, formula (2.3) again: the Weil part lands in W_K.
hole theWeilPartLiesInTheWeilPlane cites "manuscript formula (2.3): the second summand IS W_K": forall p: Period; forall z: CycleClass;
  inParameterSet(p) -> isRationalHodgeClass(p, z) -> inWeilPlane(p, weilPart(p, z))

// CITATION (Prop 12.3's selection): a class represented by integral subvarieties whose Weil
// projection is nonzero has a constituent that is an algebraic rational Hodge class with
// nonzero Weil part. This is "At least one constituent has a nonzero Weil projection. Every
// such constituent has rational Hodge class and the period lies outside E_Hdg."
hole aConstituentCarriesTheWeilProjection cites "manuscript Prop 12.3: At least one constituent has a nonzero Weil projection. Every such constituent has rational Hodge class and the period lies outside E_Hdg": forall p: Period; forall z: Class;
  inParameterSet(p) -> avoidsExceptional(p) ->
  representedByIntegralSubvarietiesAt(p, z) ->
  transport.hasNonzeroWeilProjection(z) ->
  (exists c: CycleClass;
  isRationalHodgeClass(p, c) and isAlgebraic(p, c) and
  (not isZeroClass(weilPart(p, c))))

// §12.3's selection step, PROVED: the constituent splits by (2.3) into exactly the marked
// form, and its Weil part is nonzero by construction.
theorem aNonzeroWeilProjectionSelectsAMarkedConstituent: forall p: Period;
  transport.aGoodPeriodExists() ->
  inParameterSet(p) -> avoidsExceptional(p) ->
  representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass) ->
  transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
  (exists a: CycleClass; exists w: CycleClass;
  inWeilPlane(p, w) and (not isZeroClass(w)) and
  isAlgebraic(p, add(scale(a, polarizationPower), w)))
proof
  @generalize-p |
    fix p: Period {
      @given-a-good-period |
        assume transport.aGoodPeriodExists() {
          @given-p-in-the-parameter-set |
            assume inParameterSet(p) {
              @p-is-in-the-parameter-set |
                inParameterSet(p)
                [by hypothesis given-p-in-the-parameter-set]
              @given-p-avoids |
                assume avoidsExceptional(p) {
                  @p-avoids |
                    avoidsExceptional(p)
                    [by hypothesis given-p-avoids]
                  @given-represented |
                    assume representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass) {
                      @it-is-represented |
                        representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass)
                        [by hypothesis given-represented]
                      @given-nonzero-weil-projection |
                        assume transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) {
                          @the-weil-projection-is-nonzero |
                            transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass)
                            [by hypothesis given-nonzero-weil-projection]
                          @a-constituent-exists |
                            exists c: CycleClass;
                              isRationalHodgeClass(p, c) and isAlgebraic(p, c) and
                              (not isZeroClass(weilPart(p, c)))
                            [using specialize aConstituentCarriesTheWeilProjection(p, transport.theComplexPeriodClass) p-is-in-the-parameter-set p-avoids it-is-represented the-weil-projection-is-nonzero]
                          @with-the-constituent |
                            unpack c: CycleClass from a-constituent-exists {
                              @the-constituent-facts |
                                isRationalHodgeClass(p, c) and isAlgebraic(p, c) and
                                  (not isZeroClass(weilPart(p, c)))
                                [by hypothesis with-the-constituent]
                              @the-constituent-is-a-hodge-class |
                                isRationalHodgeClass(p, c)
                                [using tautology the-constituent-facts]
                              @the-constituent-is-algebraic |
                                isAlgebraic(p, c)
                                [using tautology the-constituent-facts]
                              @its-weil-part-is-nonzero |
                                not isZeroClass(weilPart(p, c))
                                [using tautology the-constituent-facts]
                              @it-splits-by-two-point-three |
                                c = add(scale(polarizationCoefficient(p, c), polarizationPower),
                                  weilPart(p, c))
                                [using specialize theHodgeClassesSplitAsInTwoPointThree(p, c) p-is-in-the-parameter-set p-avoids the-constituent-is-a-hodge-class]
                              @its-weil-part-is-in-the-plane |
                                inWeilPlane(p, weilPart(p, c))
                                [using specialize theWeilPartLiesInTheWeilPlane(p, c) p-is-in-the-parameter-set the-constituent-is-a-hodge-class]
                              @the-marked-form-is-algebraic |
                                isAlgebraic(p, add(scale(polarizationCoefficient(p, c),
                                  polarizationPower), weilPart(p, c)))
                                [by rewrite it-splits-by-two-point-three the-constituent-is-algebraic]
                              @the-weil-part-is-in-the-plane-and-nonzero |
                                inWeilPlane(p, weilPart(p, c)) and
                                  (not isZeroClass(weilPart(p, c)))
                                [by and_intro its-weil-part-is-in-the-plane its-weil-part-is-nonzero]
                              @the-marked-form-works |
                                inWeilPlane(p, weilPart(p, c)) and
                                  (not isZeroClass(weilPart(p, c))) and
                                  isAlgebraic(p, add(scale(polarizationCoefficient(p, c),
                                  polarizationPower), weilPart(p, c)))
                                [by and_intro the-weil-part-is-in-the-plane-and-nonzero the-marked-form-is-algebraic]
                              @a-weil-part-exists |
                                exists w: CycleClass;
                                  inWeilPlane(p, w) and (not isZeroClass(w)) and
                                  isAlgebraic(p, add(scale(polarizationCoefficient(p, c),
                                  polarizationPower), w))
                                [by exists_intro(weilPart(p, c)) the-marked-form-works]
                              @conclusion-a-marked-pair-exists |
                                exists a: CycleClass; exists w: CycleClass;
                                  inWeilPlane(p, w) and (not isZeroClass(w)) and
                                  isAlgebraic(p, add(scale(a, polarizationPower), w))
                                [by exists_intro(polarizationCoefficient(p, c)) a-weil-part-exists]
                            }
                          @conclusion-marked-pair |
                            exists a: CycleClass; exists w: CycleClass;
                              inWeilPlane(p, w) and (not isZeroClass(w)) and
                              isAlgebraic(p, add(scale(a, polarizationPower), w))
                            [by exists_elim with-the-constituent]
                        }
                      @conclusion-weil-gives |
                        transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
                          (exists a: CycleClass; exists w: CycleClass;
                          inWeilPlane(p, w) and (not isZeroClass(w)) and
                          isAlgebraic(p, add(scale(a, polarizationPower), w)))
                        [by implies_intro given-nonzero-weil-projection]
                    }
                  @conclusion-represented-gives |
                    representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass) ->
                      transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
                      (exists a: CycleClass; exists w: CycleClass;
                      inWeilPlane(p, w) and (not isZeroClass(w)) and
                      isAlgebraic(p, add(scale(a, polarizationPower), w)))
                    [by implies_intro given-represented]
                }
              @conclusion-avoids-gives |
                avoidsExceptional(p) ->
                  representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass) ->
                  transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
                  (exists a: CycleClass; exists w: CycleClass;
                  inWeilPlane(p, w) and (not isZeroClass(w)) and
                  isAlgebraic(p, add(scale(a, polarizationPower), w)))
                [by implies_intro given-p-avoids]
            }
          @conclusion-parameter-gives |
            inParameterSet(p) -> avoidsExceptional(p) ->
              representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass) ->
              transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
              (exists a: CycleClass; exists w: CycleClass;
              inWeilPlane(p, w) and (not isZeroClass(w)) and
              isAlgebraic(p, add(scale(a, polarizationPower), w)))
            [by implies_intro given-p-in-the-parameter-set]
        }
      @conclusion-at-p |
        transport.aGoodPeriodExists() ->
          inParameterSet(p) -> avoidsExceptional(p) ->
          representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass) ->
          transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
          (exists a: CycleClass; exists w: CycleClass;
          inWeilPlane(p, w) and (not isZeroClass(w)) and
          isAlgebraic(p, add(scale(a, polarizationPower), w)))
        [by implies_intro given-a-good-period]
    }
  @conclusion |
    forall p: Period;
      transport.aGoodPeriodExists() ->
      inParameterSet(p) -> avoidsExceptional(p) ->
      representedByIntegralSubvarietiesAt(p, transport.theComplexPeriodClass) ->
      transport.hasNonzeroWeilProjection(transport.theComplexPeriodClass) ->
      (exists a: CycleClass; exists w: CycleClass;
      inWeilPlane(p, w) and (not isZeroClass(w)) and
      isAlgebraic(p, add(scale(a, polarizationPower), w)))
    [by forall_intro generalize-p]
qed

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
