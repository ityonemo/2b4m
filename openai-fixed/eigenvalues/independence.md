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
axiom theEigenvaluesAreNonrealConjugates:
  lambdaMinus = conj(lambdaPlus) and (not isReal(lambdaPlus))

// WELL-KNOWN: a complex number equal to its own conjugate is real.
axiom selfConjugateIsReal: forall z: Complex; z = conj(z) -> isReal(z)

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
pred spansTheWeilPlane(p: Period, v: WeilClass, w: WeilClass)
pred isProportional(p: Period, v: WeilClass, w: WeilClass)
func pullback(e: Endomorphism, w: WeilClass) => WeilClass

// The endomorphism m*1 + D of §12.4.
const theConjugation: Endomorphism

// WELL-KNOWN (linear algebra on the eigenspace decomposition): a nonzero rational Weil class
// has nonzero components on both conjugate determinant lines, so if its pullback under the
// conjugation is a rational multiple r*w, reading that equation off each line separately
// gives lambdaPlus = r AND lambdaMinus = r.
axiom proportionalityForcesBothEigenvalues: forall p: Period; forall w: WeilClass;
  inParameterSet(p) -> (not isZeroClass(w)) ->
  isProportional(p, w, pullback(theConjugation, w)) ->
  (exists r: Complex; lambdaPlus = r and lambdaMinus = r)

// WELL-KNOWN (dim W_K(A_Pi) = 2, §2): two non-proportional classes in a two-dimensional
// space span it.
axiom nonProportionalClassesSpan: forall p: Period; forall v: WeilClass; forall w: WeilClass;
  inParameterSet(p) -> (not isProportional(p, v, w)) -> spansTheWeilPlane(p, v, w)

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
