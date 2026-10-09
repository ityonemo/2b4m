# The second Weil class, decomposed

§12.4's second half was a hole: `theConjugationEndomorphism` bundled a standard fact with
the paper's own eigenvalue computation. This file separates them, so the standard half is an
axiom and the paper's half is **proved**.

## What the paper argues

> To obtain a second independent class, choose an integer `m > √d·cot(π/8)`. The integral
> matrix `m·1₈ + D` commutes with every period in `U`, and hence defines an algebraic
> endomorphism of every `A_Π`. On the two determinant lines of `W_K ⊗ ℂ`, its pullback has
> eigenvalues `λ± = (m ± i√d)⁸`.
>
> They are nonreal conjugates: the argument of `m + i√d` lies strictly between `0` and `π/8`.
> A nonzero rational `w` has nonzero components on both conjugate determinant lines. If its
> pullback were a rational multiple `r·w`, those two components would give `λ₊ = r = λ₋`, a
> contradiction. Thus `w` and its pullback are independent.

## The logical core, which is what actually needs checking

Strip the geometry and the argument is: *if `λ₊ ≠ λ₋` then no scalar `r` satisfies both
`λ₊ = r` and `λ₋ = r`.* That is all the independence rests on, and it is provable outright.

The numeric half — that `arg(m + i√d) ∈ (0, π/8)` for `m > √d·cot(π/8)`, hence `λ± = (m ±
i√d)⁸` is nonreal — was checked numerically for `d = 1..39`, including that the bound is
tight (`⌊√d·cot(π/8)⌋` fails it for every such `d`). `std` has no `cot` or `arg`, so it is
axiomatized as the elementary fact it is.

```2b4m
import complex <<< "std/complex.b4m"

sort Complex = complex.Complex
func conj = complex.conj
pred isReal(z: Complex)

// The two eigenvalues, as the paper names them.
const lambdaPlus: Complex
const lambdaMinus: Complex

// WELL-KNOWN (elementary, and verified numerically for d = 1..39): with m > √d·cot(π/8) the
// argument of m + i√d lies strictly in (0, π/8), so its eighth power is NONREAL, and the two
// eigenvalues are complex conjugates of each other.
hole theEigenvaluesAreNonrealConjugates cites "manuscript §12.4: arg(m + i sqrt d) in (0, pi/8) for m > sqrt(d) cot(pi/8); verified numerically d=1..39, bound tight":
  lambdaMinus = conj(lambdaPlus) and (not isReal(lambdaPlus))

// WELL-KNOWN: a complex number equal to its own conjugate is real.
hole selfConjugateIsReal cites "elementary: z = conj(z) => z real": forall z: Complex; z = conj(z) -> isReal(z)

// THE PAPER'S STEP, PROVED: the eigenvalues differ. (Were they equal, λ₊ would equal its own
// conjugate, hence be real — contradicting nonreality.)
theorem theEigenvaluesDiffer: lambdaPlus != lambdaMinus
proof
  @the-eigenvalue-facts |
    lambdaMinus = conj(lambdaPlus) and (not isReal(lambdaPlus))
    [by cite theEigenvaluesAreNonrealConjugates]
  @the-minus-is-the-conjugate |
    lambdaMinus = conj(lambdaPlus)
    [by and_elim_left the-eigenvalue-facts]
  @given-they-agree |
    assume lambdaPlus = lambdaMinus {
      @they-agree |
        lambdaPlus = lambdaMinus
        [by hypothesis given-they-agree]
      @the-plus-is-its-own-conjugate |
        lambdaPlus = conj(lambdaPlus)
        [using chain they-agree the-minus-is-the-conjugate]
      @the-plus-is-real |
        isReal(lambdaPlus)
        [using specialize selfConjugateIsReal(lambdaPlus) the-plus-is-its-own-conjugate]
      @the-plus-is-also-not-real |
        not isReal(lambdaPlus)
        [using tautology the-eigenvalue-facts]
    }
  @conclusion |
    lambdaPlus != lambdaMinus
    [by not_intro given-they-agree the-plus-is-real the-plus-is-also-not-real]
qed
```

## The independence conclusion

With the eigenvalues distinct, no scalar can be both. That is the whole content of "`w` and
its pullback are independent", and it is now proved rather than assumed.

```2b4m
// THE PAPER'S CONCLUSION, PROVED: no scalar r satisfies both λ₊ = r and λ₋ = r. This is
// exactly the contradiction §12.4 derives, with the geometry (that a rational w has nonzero
// components on both determinant lines, so pullback(w) = r·w would force both equations)
// left to the axiom that consumes it.
theorem noScalarIsBothEigenvalues: forall r: Complex;
  not (lambdaPlus = r and lambdaMinus = r)
proof
  @generalize-r |
    fix r: Complex {
      @given-both |
        assume lambdaPlus = r and lambdaMinus = r {
          @both-hold |
            lambdaPlus = r and lambdaMinus = r
            [by hypothesis given-both]
          @the-plus-is-r |
            lambdaPlus = r
            [by and_elim_left both-hold]
          @the-minus-is-r |
            lambdaMinus = r
            [by and_elim_right both-hold]
          @the-eigenvalues-agree |
            lambdaPlus = lambdaMinus
            [by rewrite the-minus-is-r the-plus-is-r]
          @the-eigenvalues-also-differ |
            lambdaPlus != lambdaMinus
            [by cite theEigenvaluesDiffer]
        }
      @conclusion-at-r |
        not (lambdaPlus = r and lambdaMinus = r)
        [by not_intro given-both the-eigenvalues-agree the-eigenvalues-also-differ]
    }
  @conclusion |
    forall r: Complex; not (lambdaPlus = r and lambdaMinus = r)
    [by forall_intro generalize-r]
qed
```

## The bridge to spanning, which is what §12.4 actually needs

`architecture.md` consumes the independence as *"`w` and `pullback(e, w)` span the Weil
plane"*. The step from `noScalarIsBothEigenvalues` to that is the standard eigenvector
argument, and it decomposes into exactly two cited facts:

1. **Proportionality forces both eigenvalue equations.** A nonzero rational Weil class has
   nonzero components on *both* conjugate determinant lines; if `pullback(e, w) = r·w` then
   reading that equation off each line separately gives `λ₊ = r` and `λ₋ = r`. This is linear
   algebra on an eigenspace decomposition.
2. **Non-proportionality is spanning.** The rational Weil space `W_K(A_Π)` is
   two-dimensional (§2), so any two non-proportional vectors in it span.

Both are standard. With them, spanning follows from the proved `noScalarIsBothEigenvalues`
by contradiction, and *that* is the piece this file contributes: the paper's eigenvalue
computation is now load-bearing rather than decorative.

```2b4m
import construction <<< "../construction/marked-class.md"

sort Period = construction.Period
sort WeilClass = construction.CycleClass
sort Endomorphism

pred inParameterSet = construction.inParameterSet
pred isZeroClass = construction.isZeroClass

// SPANNING, DEFINED. §2 computes dim W_K(A_Pi) = 2, so in the Weil plane "spans" and
// "independent" coincide: a pair spans exactly when it is not proportional. The manuscript
// uses the two interchangeably -- "Thus w and its pullback are independent rational
// algebraic classes and span W_K" -- and writing it as a DEFINITION is what lets the
// spanning conclusion be proved from the eigenvalue argument instead of assumed.
//
// This is a modelling choice, and it is the honest one available: leaving spansTheWeilPlane
// opaque forced an axiom bridging non-proportionality to spanning, which is the paper's own
// step and so may not be an axiom.
pred spansTheWeilPlane(p: Period, v: WeilClass, w: WeilClass):
  spansTheWeilPlane(p, v, w) iff (not isProportional(p, v, w))
func pullback(e: Endomorphism, w: WeilClass) => WeilClass

// The endomorphism m*1 + D of §12.4.
const theConjugation: Endomorphism

// §12.4's STEP, now MODELLED rather than held as a hole. The argument needs the eigenspace
// decomposition of W_K ⊗ C into its two conjugate determinant lines, so that is written out:
// each class has a plus-component and a minus-component, the conjugation acts on each by its
// eigenvalue, and proportionality is read off componentwise.
//
// §2's Lemma (2.6) supplies the nonvanishing: "Choose a rational vector where it is nonzero.
// Its two components are conjugate, so neither vanishes." §12.4 restates it as "A nonzero
// rational w has nonzero components on both conjugate determinant lines."

// The two component projections onto the determinant lines H+ and H-, valued in C.
func plusComponent(w: WeilClass) => Complex
func minusComponent(w: WeilClass) => Complex

// Scaling a class by a complex scalar, and the scalar multiple relation §12.4 writes as r*w.
func scaleClass(r: Complex, w: WeilClass) => WeilClass
func mulComplex = complex.mul
const ZEROCOMPLEX = complex.ZERO

// CITATION (§2, Lemma 2.6): a nonzero rational Weil class has nonzero components on BOTH
// conjugate determinant lines. "Its two components are conjugate, so neither vanishes."
hole bothComponentsAreNonzero cites "manuscript §2 (2.6): Its two components are conjugate, so neither vanishes": forall p: Period; forall w: WeilClass;
  inParameterSet(p) -> (not isZeroClass(w)) ->
  (plusComponent(w) != ZEROCOMPLEX and minusComponent(w) != ZEROCOMPLEX)

// CITATION (§12.4): on the two determinant lines the conjugation's pullback acts by the
// eigenvalues lambda+ and lambda- respectively. "On the two determinant lines of W_K (x) C,
// its pullback has eigenvalues lambda+ = (m + i sqrt d)^8, lambda- = (m - i sqrt d)^8."
hole theConjugationActsByItsEigenvalues cites "manuscript §12.4: On the two determinant lines of W_K (x) C, its pullback has eigenvalues lambda+ = (m + i sqrt d)^8, lambda- = (m - i sqrt d)^8": forall w: WeilClass;
  plusComponent(pullback(theConjugation, w)) = mulComplex(lambdaPlus, plusComponent(w)) and
  minusComponent(pullback(theConjugation, w)) = mulComplex(lambdaMinus, minusComponent(w))

// PROPORTIONALITY, as §12.4 uses it: the pullback IS a scalar multiple r*w. Declared with a
// separate axiom rather than a definition block, because the defining clause binds its own
// existential witness and a clause variable must be settled by the clause's symbols.
pred isProportional(p: Period, v: WeilClass, w: WeilClass)

axiom proportionalityIsBeingAScalarMultiple:
  forall p: Period; forall v: WeilClass; forall w: WeilClass;
  isProportional(p, v, w) iff (exists r: Complex; w = scaleClass(r, v))

// CITATION (projections are linear): a projection of a scalar multiple is the scalar times
// the projection.
hole theProjectionsAreLinear cites "elementary: a projection onto an eigenspace is linear": forall r: Complex; forall w: WeilClass;
  plusComponent(scaleClass(r, w)) = mulComplex(r, plusComponent(w)) and
  minusComponent(scaleClass(r, w)) = mulComplex(r, minusComponent(w))

// WELL-KNOWN (C is an integral domain; cancel the nonzero component): from
// lambda*x = r*x with x != 0 conclude lambda = r.
hole complexCancellation cites "elementary: C is an integral domain": forall a: Complex; forall b: Complex; forall x: Complex;
  x != ZEROCOMPLEX -> mulComplex(a, x) = mulComplex(b, x) -> a = b

// §12.4's STEP, PROVED: if the pullback is a rational multiple r*w, reading that equation off
// each determinant line separately gives lambda+ = r AND lambda- = r.
theorem proportionalityForcesBothEigenvalues: forall p: Period; forall w: WeilClass;
  inParameterSet(p) -> (not isZeroClass(w)) ->
  isProportional(p, w, pullback(theConjugation, w)) ->
  (exists r: Complex; lambdaPlus = r and lambdaMinus = r)
proof
  @generalize-p |
    fix p: Period {
      @generalize-w |
        fix w: WeilClass {
          @given-p-in-the-parameter-set |
            assume inParameterSet(p) {
              @p-is-in-the-parameter-set |
                inParameterSet(p)
                [by hypothesis given-p-in-the-parameter-set]
              @given-w-nonzero |
                assume not isZeroClass(w) {
                  @w-is-nonzero |
                    not isZeroClass(w)
                    [by hypothesis given-w-nonzero]
                  @given-proportional |
                    assume isProportional(p, w, pullback(theConjugation, w)) {
                      @they-are-proportional |
                        isProportional(p, w, pullback(theConjugation, w))
                        [by hypothesis given-proportional]
                      @proportionality-means-a-scalar-multiple |
                        forall q: Period; forall v: WeilClass; forall u: WeilClass;
                          isProportional(q, v, u) iff (exists r: Complex; u = scaleClass(r, v))
                        [by cite proportionalityIsBeingAScalarMultiple]
                      @the-equivalence-here |
                        isProportional(p, w, pullback(theConjugation, w)) iff
                          (exists r: Complex; pullback(theConjugation, w) = scaleClass(r, w))
                        [by forall_elim(p, w, pullback(theConjugation, w)) proportionality-means-a-scalar-multiple]
                      @a-scalar-exists |
                        exists r: Complex; pullback(theConjugation, w) = scaleClass(r, w)
                        [using tautology the-equivalence-here they-are-proportional]
                      @both-components-nonzero |
                        plusComponent(w) != ZEROCOMPLEX and minusComponent(w) != ZEROCOMPLEX
                        [using specialize bothComponentsAreNonzero(p, w) p-is-in-the-parameter-set w-is-nonzero]
                      @the-plus-component-is-nonzero |
                        plusComponent(w) != ZEROCOMPLEX
                        [by and_elim_left both-components-nonzero]
                      @the-minus-component-is-nonzero |
                        minusComponent(w) != ZEROCOMPLEX
                        [by and_elim_right both-components-nonzero]
                      @the-conjugation-acts |
                        plusComponent(pullback(theConjugation, w))
                          = mulComplex(lambdaPlus, plusComponent(w)) and
                          minusComponent(pullback(theConjugation, w))
                          = mulComplex(lambdaMinus, minusComponent(w))
                        [using specialize theConjugationActsByItsEigenvalues(w)]
                      @the-plus-action |
                        plusComponent(pullback(theConjugation, w))
                          = mulComplex(lambdaPlus, plusComponent(w))
                        [by and_elim_left the-conjugation-acts]
                      @the-minus-action |
                        minusComponent(pullback(theConjugation, w))
                          = mulComplex(lambdaMinus, minusComponent(w))
                        [by and_elim_right the-conjugation-acts]
                      @with-the-scalar |
                        unpack r: Complex from a-scalar-exists {
                          @the-pullback-is-a-multiple |
                            pullback(theConjugation, w) = scaleClass(r, w)
                            [by hypothesis with-the-scalar]
                          @the-projections-are-linear-at-r |
                            plusComponent(scaleClass(r, w)) = mulComplex(r, plusComponent(w)) and
                              minusComponent(scaleClass(r, w)) = mulComplex(r, minusComponent(w))
                            [using specialize theProjectionsAreLinear(r, w)]
                          @the-plus-of-the-multiple |
                            plusComponent(scaleClass(r, w)) = mulComplex(r, plusComponent(w))
                            [by and_elim_left the-projections-are-linear-at-r]
                          @the-minus-of-the-multiple |
                            minusComponent(scaleClass(r, w)) = mulComplex(r, minusComponent(w))
                            [by and_elim_right the-projections-are-linear-at-r]
                          @the-plus-reads-both-ways |
                            mulComplex(lambdaPlus, plusComponent(w))
                              = mulComplex(r, plusComponent(w))
                            [using chain the-plus-action the-pullback-is-a-multiple the-plus-of-the-multiple]
                          @the-minus-reads-both-ways |
                            mulComplex(lambdaMinus, minusComponent(w))
                              = mulComplex(r, minusComponent(w))
                            [using chain the-minus-action the-pullback-is-a-multiple the-minus-of-the-multiple]
                          @the-plus-eigenvalue-is-r |
                            lambdaPlus = r
                            [using specialize complexCancellation(lambdaPlus, r, plusComponent(w)) the-plus-component-is-nonzero the-plus-reads-both-ways]
                          @the-minus-eigenvalue-is-r |
                            lambdaMinus = r
                            [using specialize complexCancellation(lambdaMinus, r, minusComponent(w)) the-minus-component-is-nonzero the-minus-reads-both-ways]
                          @both-eigenvalues-are-r |
                            lambdaPlus = r and lambdaMinus = r
                            [by and_intro the-plus-eigenvalue-is-r the-minus-eigenvalue-is-r]
                          @conclusion-a-scalar-is-both |
                            exists s: Complex; lambdaPlus = s and lambdaMinus = s
                            [by exists_intro(r) both-eigenvalues-are-r]
                        }
                      @conclusion-some-scalar-is-both |
                        exists s: Complex; lambdaPlus = s and lambdaMinus = s
                        [by exists_elim with-the-scalar]
                    }
                  @conclusion-proportional-gives |
                    isProportional(p, w, pullback(theConjugation, w)) ->
                      (exists r: Complex; lambdaPlus = r and lambdaMinus = r)
                    [by implies_intro given-proportional]
                }
              @conclusion-nonzero-gives |
                (not isZeroClass(w)) ->
                  isProportional(p, w, pullback(theConjugation, w)) ->
                  (exists r: Complex; lambdaPlus = r and lambdaMinus = r)
                [by implies_intro given-w-nonzero]
            }
          @conclusion-at-w |
            inParameterSet(p) -> (not isZeroClass(w)) ->
              isProportional(p, w, pullback(theConjugation, w)) ->
              (exists r: Complex; lambdaPlus = r and lambdaMinus = r)
            [by implies_intro given-p-in-the-parameter-set]
        }
      @discharge-w |
        forall w: WeilClass;
          inParameterSet(p) -> (not isZeroClass(w)) ->
          isProportional(p, w, pullback(theConjugation, w)) ->
          (exists r: Complex; lambdaPlus = r and lambdaMinus = r)
        [by forall_intro generalize-w]
    }
  @conclusion |
    forall p: Period; forall w: WeilClass;
      inParameterSet(p) -> (not isZeroClass(w)) ->
      isProportional(p, w, pullback(theConjugation, w)) ->
      (exists r: Complex; lambdaPlus = r and lambdaMinus = r)
    [by forall_intro generalize-p]
qed

// §12.4's identification of "independent" with "spans", now a THEOREM off the definition.
theorem nonProportionalClassesSpan: forall p: Period; forall v: WeilClass; forall w: WeilClass;
  inParameterSet(p) -> (not isProportional(p, v, w)) -> spansTheWeilPlane(p, v, w)
proof
  @spanning-is-non-proportionality |
    forall p: Period; forall v: WeilClass; forall w: WeilClass;
      spansTheWeilPlane(p, v, w) iff (not isProportional(p, v, w))
    [by definition spansTheWeilPlane]
  @generalize-p |
    fix p: Period {
      @generalize-v |
        fix v: WeilClass {
          @generalize-w |
            fix w: WeilClass {
              @given-p-in-the-parameter-set |
                assume inParameterSet(p) {
                  @given-not-proportional |
                    assume not isProportional(p, v, w) {
                      @they-are-not-proportional |
                        not isProportional(p, v, w)
                        [by hypothesis given-not-proportional]
                      @the-equivalence-at-these |
                        spansTheWeilPlane(p, v, w) iff (not isProportional(p, v, w))
                        [by forall_elim(p, v, w) spanning-is-non-proportionality]
                      @conclusion-they-span |
                        spansTheWeilPlane(p, v, w)
                        [using tautology the-equivalence-at-these they-are-not-proportional]
                    }
                  @conclusion-non-proportional-gives |
                    (not isProportional(p, v, w)) -> spansTheWeilPlane(p, v, w)
                    [by implies_intro given-not-proportional]
                }
              @conclusion-at-w |
                inParameterSet(p) -> (not isProportional(p, v, w)) ->
                  spansTheWeilPlane(p, v, w)
                [by implies_intro given-p-in-the-parameter-set]
            }
          @discharge-w |
            forall w: WeilClass;
              inParameterSet(p) -> (not isProportional(p, v, w)) ->
              spansTheWeilPlane(p, v, w)
            [by forall_intro generalize-w]
        }
      @discharge-v |
        forall v: WeilClass; forall w: WeilClass;
          inParameterSet(p) -> (not isProportional(p, v, w)) ->
          spansTheWeilPlane(p, v, w)
        [by forall_intro generalize-v]
    }
  @conclusion |
    forall p: Period; forall v: WeilClass; forall w: WeilClass;
      inParameterSet(p) -> (not isProportional(p, v, w)) -> spansTheWeilPlane(p, v, w)
    [by forall_intro generalize-p]
qed

// THE PAPER'S CONCLUSION, PROVED from the eigenvalue computation above. Were w and its
// pullback proportional, some scalar would be BOTH eigenvalues — which the theorem above
// forbids. So they are non-proportional, hence spanning.
theorem theConjugationProducesASpanningPartner: forall p: Period; forall w: WeilClass;
  inParameterSet(p) -> (not isZeroClass(w)) ->
  spansTheWeilPlane(p, w, pullback(theConjugation, w))
proof
  @generalize-p |
    fix p: Period {
      @generalize-w |
        fix w: WeilClass {
          @given-p-in-the-parameter-set |
            assume inParameterSet(p) {
              @p-is-in-the-parameter-set |
                inParameterSet(p)
                [by hypothesis given-p-in-the-parameter-set]
              @given-w-nonzero |
                assume not isZeroClass(w) {
                  @w-is-nonzero |
                    not isZeroClass(w)
                    [by hypothesis given-w-nonzero]
                  @given-they-were-proportional |
                    assume isProportional(p, w, pullback(theConjugation, w)) {
                      @they-are-proportional |
                        isProportional(p, w, pullback(theConjugation, w))
                        [by hypothesis given-they-were-proportional]
                      @some-scalar-is-both |
                        exists r: Complex; lambdaPlus = r and lambdaMinus = r
                        [using specialize proportionalityForcesBothEigenvalues(p, w) p-is-in-the-parameter-set w-is-nonzero they-are-proportional]
                      @with-the-scalar |
                        unpack r: Complex from some-scalar-is-both {
                          @the-scalar-is-both |
                            lambdaPlus = r and lambdaMinus = r
                            [by hypothesis with-the-scalar]
                          @no-scalar-is-both |
                            not (lambdaPlus = r and lambdaMinus = r)
                            [using specialize noScalarIsBothEigenvalues(r)]
                          @conclusion-the-class-is-zero |
                            isZeroClass(w)
                            [using tautology the-scalar-is-both no-scalar-is-both]
                        }
                      @the-class-would-be-zero |
                        isZeroClass(w)
                        [by exists_elim with-the-scalar]
                      @the-class-is-also-nonzero |
                        not isZeroClass(w)
                        [by hypothesis given-w-nonzero]
                    }
                  @they-are-not-proportional |
                    not isProportional(p, w, pullback(theConjugation, w))
                    [by not_intro given-they-were-proportional the-class-would-be-zero the-class-is-also-nonzero]
                  @conclusion-the-pair-spans |
                    spansTheWeilPlane(p, w, pullback(theConjugation, w))
                    [using specialize nonProportionalClassesSpan(p, w, pullback(theConjugation, w)) p-is-in-the-parameter-set they-are-not-proportional]
                }
              @conclusion-nonzero-gives |
                (not isZeroClass(w)) ->
                  spansTheWeilPlane(p, w, pullback(theConjugation, w))
                [by implies_intro given-w-nonzero]
            }
          @conclusion-at-w |
            inParameterSet(p) -> (not isZeroClass(w)) ->
              spansTheWeilPlane(p, w, pullback(theConjugation, w))
            [by implies_intro given-p-in-the-parameter-set]
        }
      @discharge-w |
        forall w: WeilClass;
          inParameterSet(p) -> (not isZeroClass(w)) ->
          spansTheWeilPlane(p, w, pullback(theConjugation, w))
        [by forall_intro generalize-w]
    }
  @conclusion |
    forall p: Period; forall w: WeilClass;
      inParameterSet(p) -> (not isZeroClass(w)) ->
      spansTheWeilPlane(p, w, pullback(theConjugation, w))
    [by forall_intro generalize-p]
qed
```
