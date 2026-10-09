# The proof architecture, top-down

A `2b4m` formalization of the **main thrust** of OpenAI's withdrawn manuscript
*"Algebraicity of Weil classes on split abelian eightfolds"*, built **top-down with `hole`s**.

## Scope

This file is §12.4: Theorem 1.1 from a spanning pair of algebraic Weil classes. The
construction below it — Proposition 12.3 and the detection chain — lives in
`construction/` and `detection/`; §3.4's stabilization-trace count, which is where the two
chains diverge, lives in `legendrian/`.

Every unproved step is a `hole` with a citation, so `2b4m check --axioms` prints the full
assumption set. See the top-level `README.md`.

## The objects

Shared objects come from `construction/marked-class-right.md`.

```2b4m
import construction <<< "construction/marked-class-right.md"
import eigenvalues <<< "eigenvalues/independence-right.md"
import chern <<< "construction/chern-constancy-right.md"

sort Period = construction.Period
sort CycleClass = construction.CycleClass
sort Endomorphism = eigenvalues.Endomorphism
sort ParameterPoint = chern.ParameterPoint

// U is the parameter set of §2; `avoidsExceptional` is "Π ∉ E", the union of the countably
// many proper closed analytic loci removed by Propositions 2.2, 8.4 and Lemma 12.1.
pred inParameterSet = construction.inParameterSet
pred avoidsExceptional = construction.avoidsExceptional

// theta^4 — a single class, NOT indexed by the period: §2 fixes the marking ("The principal
// polarization has class θ, identified with ψ₀ in the fixed torus marking") and §12.4 spreads
// "the FIXED marked class aθ⁴ + w" across the family.
const polarizationPower = construction.polarizationPower

func scale = construction.scale
func add = construction.add
func pullback = eigenvalues.pullback

pred isAlgebraic = construction.isAlgebraic
pred inWeilPlane = construction.inWeilPlane
pred isZeroClass = construction.isZeroClass
pred isAlgebraicEndomorphism(p: Period, e: Endomorphism)

// v and w are independent and span the two-dimensional rational Weil space W_K(A_Π).
pred spansTheWeilPlane = eigenvalues.spansTheWeilPlane
```

## Theorem 1.1, stated first

The paper's conclusion is `W_K(A) ⊂ im(CH⁴(A) ⊗ ℚ → H⁸(A, ℚ))`: every class in the Weil
plane is algebraic. Since the plane is two-dimensional, the paper reaches this by exhibiting
a spanning *pair* of algebraic classes — so that is the statement.

Two holes. The first says some nonzero Weil class is algebraic on every fiber; the second
says an endomorphism turns it into an independent one.

Both are proved in the sections below (`theFirstWeilClassIsAlgebraicEverywhere` and
`theSecondClassIsAlgebraic`), so they are cited directly rather than left as holes — the
`hole` stage of each has been discharged.

```2b4m
theorem theWeilPlaneIsSpannedByAlgebraicClasses:
  forall p: Period; inParameterSet(p) ->
  exists v: CycleClass; exists w: CycleClass;
  spansTheWeilPlane(p, v, w) and isAlgebraic(p, v) and isAlgebraic(p, w)
proof
  @a-weil-class-is-algebraic-everywhere |
    exists w: CycleClass;
      (not isZeroClass(w)) and
      (forall q: Period; inParameterSet(q) -> isAlgebraic(q, w))
    [by cite theFirstWeilClassIsAlgebraicEverywhere]
  @a-second-class-follows |
    forall p: Period; forall w: CycleClass;
      inParameterSet(p) -> (not isZeroClass(w)) -> isAlgebraic(p, w) ->
      (exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v))
    [by cite theSecondClassIsAlgebraic]
  @with-the-weil-class |
    unpack w: CycleClass from a-weil-class-is-algebraic-everywhere {
      @the-class-facts |
        (not isZeroClass(w)) and
          (forall q: Period; inParameterSet(q) -> isAlgebraic(q, w))
        [by hypothesis with-the-weil-class]
      @the-class-is-nonzero |
        not isZeroClass(w)
        [using tautology the-class-facts]
      @the-class-is-algebraic-everywhere |
        forall q: Period; inParameterSet(q) -> isAlgebraic(q, w)
        [using tautology the-class-facts]
      @generalize-p |
        fix p: Period {
          @given-p-in-the-parameter-set |
            assume inParameterSet(p) {
              @p-is-in-the-parameter-set |
                inParameterSet(p)
                [by hypothesis given-p-in-the-parameter-set]
              @the-class-is-algebraic-at-p |
                isAlgebraic(p, w)
                [using specialize the-class-is-algebraic-everywhere(p) p-is-in-the-parameter-set]
              @a-partner-exists |
                exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v)
                [using specialize a-second-class-follows(p, w) p-is-in-the-parameter-set the-class-is-nonzero the-class-is-algebraic-at-p]
              @with-the-partner |
                unpack v: CycleClass from a-partner-exists {
                  @the-partner-facts |
                    spansTheWeilPlane(p, w, v) and isAlgebraic(p, v)
                    [by hypothesis with-the-partner]
                  @the-pair-spans |
                    spansTheWeilPlane(p, w, v)
                    [by and_elim_left the-partner-facts]
                  @the-partner-is-algebraic |
                    isAlgebraic(p, v)
                    [by and_elim_right the-partner-facts]
                  @the-pair-works |
                    spansTheWeilPlane(p, w, v) and isAlgebraic(p, w) and isAlgebraic(p, v)
                    [using tautology the-pair-spans the-class-is-algebraic-at-p the-partner-is-algebraic]
                  @a-second-coordinate-exists |
                    exists w2: CycleClass;
                      spansTheWeilPlane(p, w, w2) and isAlgebraic(p, w) and isAlgebraic(p, w2)
                    [by exists_intro(v) the-pair-works]
                  @conclusion-at-the-partner |
                    exists v2: CycleClass; exists w2: CycleClass;
                      spansTheWeilPlane(p, v2, w2) and isAlgebraic(p, v2) and isAlgebraic(p, w2)
                    [by exists_intro(w) a-second-coordinate-exists]
                }
              @conclusion-a-spanning-pair-exists |
                exists v2: CycleClass; exists w2: CycleClass;
                  spansTheWeilPlane(p, v2, w2) and isAlgebraic(p, v2) and isAlgebraic(p, w2)
                [by exists_elim with-the-partner]
            }
          @conclusion-p-gives |
            inParameterSet(p) ->
              (exists v2: CycleClass; exists w2: CycleClass;
              spansTheWeilPlane(p, v2, w2) and isAlgebraic(p, v2) and isAlgebraic(p, w2))
            [by implies_intro given-p-in-the-parameter-set]
        }
      @conclusion-at-the-weil-class |
        forall p: Period; inParameterSet(p) ->
          (exists v2: CycleClass; exists w2: CycleClass;
          spansTheWeilPlane(p, v2, w2) and isAlgebraic(p, v2) and isAlgebraic(p, w2))
        [by forall_intro generalize-p]
    }
  @conclusion |
    forall p: Period; inParameterSet(p) ->
      (exists v: CycleClass; exists w: CycleClass;
      spansTheWeilPlane(p, v, w) and isAlgebraic(p, v) and isAlgebraic(p, w))
    [by exists_elim with-the-weil-class]
qed
```

## Hole 1: a nonzero Weil class, algebraic on every fiber

This is §12.4's first half. The structure: Proposition 12.3 gives *one* period with an
algebraic class `a·θ⁴ + w`; the Hilbert parameter space spreads that fixed class to *every*
fiber; subtracting the algebraic `a·θ⁴` leaves `w`. Three new holes, and note the quantifier
move from one period to all — that is the step worth checking.

```2b4m
theorem theFirstWeilClassIsAlgebraicEverywhere:
  exists w: CycleClass;
  (not isZeroClass(w)) and
  (forall q: Period; inParameterSet(q) -> isAlgebraic(q, w))
proof
  @a-marked-period-exists |
    exists p: Period;
      inParameterSet(p) and avoidsExceptional(p) and
      (exists a: CycleClass; exists w: CycleClass;
      inWeilPlane(p, w) and (not isZeroClass(w)) and
      isAlgebraic(p, add(scale(a, polarizationPower), w)))
    [by cite aMarkedAlgebraicClassExistsAtSomeGoodPeriod]
  @the-spreading-principle |
    forall p: Period; forall z: CycleClass;
      inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
      forall q: Period; inParameterSet(q) -> isAlgebraic(q, z)
    [by cite theMarkedClassIsConstantAcrossTheFamily]
  @the-polarization-is-algebraic |
    forall p: Period; forall a: CycleClass;
      inParameterSet(p) -> isAlgebraic(p, scale(a, polarizationPower))
    [by cite aPowerOfThePolarizationIsAlgebraic]
  @subtraction-preserves-algebraicity |
    forall p: Period; forall z: CycleClass; forall w: CycleClass;
      isAlgebraic(p, add(z, w)) -> isAlgebraic(p, z) -> isAlgebraic(p, w)
    [by cite theAlgebraicClassesFormASubspace]
  @with-the-marked-period |
    unpack p: Period from a-marked-period-exists {
      @the-period-facts |
        inParameterSet(p) and avoidsExceptional(p) and
          (exists a: CycleClass; exists w: CycleClass;
          inWeilPlane(p, w) and (not isZeroClass(w)) and
          isAlgebraic(p, add(scale(a, polarizationPower), w)))
        [by hypothesis with-the-marked-period]
      @the-period-is-in-the-parameter-set |
        inParameterSet(p)
        [using tautology the-period-facts]
      @the-period-avoids-the-exceptional-loci |
        avoidsExceptional(p)
        [using tautology the-period-facts]
      @a-marked-class-exists |
        exists a: CycleClass; exists w: CycleClass;
          inWeilPlane(p, w) and (not isZeroClass(w)) and
          isAlgebraic(p, add(scale(a, polarizationPower), w))
        [using tautology the-period-facts]
      @with-the-coefficient |
        unpack a: CycleClass from a-marked-class-exists {
          @a-weil-part-exists |
            exists w: CycleClass;
              inWeilPlane(p, w) and (not isZeroClass(w)) and
              isAlgebraic(p, add(scale(a, polarizationPower), w))
            [by hypothesis with-the-coefficient]
          @with-the-weil-part |
            unpack w: CycleClass from a-weil-part-exists {
              @the-class-facts |
                inWeilPlane(p, w) and (not isZeroClass(w)) and
                  isAlgebraic(p, add(scale(a, polarizationPower), w))
                [by hypothesis with-the-weil-part]
              @the-weil-part-is-nonzero |
                not isZeroClass(w)
                [using tautology the-class-facts]
              @the-marked-class-is-algebraic |
                isAlgebraic(p, add(scale(a, polarizationPower), w))
                [using tautology the-class-facts]
              // THE QUANTIFIER MOVE: spread the MARKED class — not w — to every fiber.
              // Spreading w directly would be assuming what is to be proved; the paper
              // spreads aθ⁴ + w and subtracts afterwards, and so does this.
              @the-marked-class-is-algebraic-everywhere |
                forall q: Period; inParameterSet(q) ->
                  isAlgebraic(q, add(scale(a, polarizationPower), w))
                [using specialize the-spreading-principle(p, add(scale(a, polarizationPower), w)) the-period-is-in-the-parameter-set the-period-avoids-the-exceptional-loci the-marked-class-is-algebraic]
              @generalize-q |
                fix q: Period {
                  @given-q-in-the-parameter-set |
                    assume inParameterSet(q) {
                      @q-is-in-the-parameter-set |
                        inParameterSet(q)
                        [by hypothesis given-q-in-the-parameter-set]
                      @the-marked-class-is-algebraic-at-q |
                        isAlgebraic(q, add(scale(a, polarizationPower), w))
                        [using specialize the-marked-class-is-algebraic-everywhere(q) q-is-in-the-parameter-set]
                      @the-polarization-term-is-algebraic-at-q |
                        isAlgebraic(q, scale(a, polarizationPower))
                        [using specialize the-polarization-is-algebraic(q, a) q-is-in-the-parameter-set]
                      @conclusion-weil-part-is-algebraic-at-q |
                        isAlgebraic(q, w)
                        [using specialize subtraction-preserves-algebraicity(q, scale(a, polarizationPower), w) the-marked-class-is-algebraic-at-q the-polarization-term-is-algebraic-at-q]
                    }
                  @conclusion-q-gives |
                    inParameterSet(q) -> isAlgebraic(q, w)
                    [by implies_intro given-q-in-the-parameter-set]
                }
              @the-weil-part-is-algebraic-everywhere |
                forall q: Period; inParameterSet(q) -> isAlgebraic(q, w)
                [by forall_intro generalize-q]
              @the-witness-works |
                (not isZeroClass(w)) and
                  (forall q: Period; inParameterSet(q) -> isAlgebraic(q, w))
                [by and_intro the-weil-part-is-nonzero the-weil-part-is-algebraic-everywhere]
              @conclusion-at-the-weil-part |
                exists w2: CycleClass;
                  (not isZeroClass(w2)) and
                  (forall q: Period; inParameterSet(q) -> isAlgebraic(q, w2))
                [by exists_intro(w) the-witness-works]
            }
          @conclusion-at-the-coefficient |
            exists w2: CycleClass;
              (not isZeroClass(w2)) and
              (forall q: Period; inParameterSet(q) -> isAlgebraic(q, w2))
            [by exists_elim with-the-weil-part]
        }
      @conclusion-at-the-period |
        exists w2: CycleClass;
          (not isZeroClass(w2)) and
          (forall q: Period; inParameterSet(q) -> isAlgebraic(q, w2))
        [by exists_elim with-the-coefficient]
    }
  @conclusion |
    exists w: CycleClass;
      (not isZeroClass(w)) and
      (forall q: Period; inParameterSet(q) -> isAlgebraic(q, w))
    [by exists_elim with-the-marked-period]
qed
```


## Hole 2: the second independent class

§12.4's second half. The paper chooses an integer `m > √d·cot(π/8)`; then `m·1₈ + D`
commutes with every period in `U`, so it is an algebraic endomorphism of every `A_Π`, and on
the two determinant lines of `W_K ⊗ ℂ` its pullback has eigenvalues `λ± = (m ± i√d)⁸`. Those
are nonreal conjugates, so a rational `w` with nonzero components on both lines cannot
satisfy `pullback(w) = r·w` — whence independence.

```2b4m
theorem theSecondClassIsAlgebraic:
  forall p: Period; forall w: CycleClass;
  inParameterSet(p) -> (not isZeroClass(w)) -> isAlgebraic(p, w) ->
  (exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v))
proof
  @an-endomorphism-exists |
    exists e: Endomorphism;
      (forall p: Period; inParameterSet(p) -> isAlgebraicEndomorphism(p, e)) and
      (forall p: Period; forall w: CycleClass;
      inParameterSet(p) -> (not isZeroClass(w)) -> spansTheWeilPlane(p, w, pullback(e, w)))
    [by cite theConjugationEndomorphism]
  @pullback-preserves-algebraicity |
    forall p: Period; forall e: Endomorphism; forall z: CycleClass;
      isAlgebraicEndomorphism(p, e) -> isAlgebraic(p, z) -> isAlgebraic(p, pullback(e, z))
    [by cite theCycleClassMapIsFunctorial]
  @with-the-endomorphism |
    unpack e: Endomorphism from an-endomorphism-exists {
      @the-endomorphism-facts |
        (forall p: Period; inParameterSet(p) -> isAlgebraicEndomorphism(p, e)) and
          (forall p: Period; forall w: CycleClass;
          inParameterSet(p) -> (not isZeroClass(w)) -> spansTheWeilPlane(p, w, pullback(e, w)))
        [by hypothesis with-the-endomorphism]
      @the-endomorphism-is-algebraic |
        forall p: Period; inParameterSet(p) -> isAlgebraicEndomorphism(p, e)
        [using tautology the-endomorphism-facts]
      @the-endomorphism-spans |
        forall p: Period; forall w: CycleClass;
          inParameterSet(p) -> (not isZeroClass(w)) -> spansTheWeilPlane(p, w, pullback(e, w))
        [using tautology the-endomorphism-facts]
      @generalize-p |
        fix p: Period {
          @generalize-w |
            fix w: CycleClass {
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
                      @given-w-algebraic |
                        assume isAlgebraic(p, w) {
                          @w-is-algebraic |
                            isAlgebraic(p, w)
                            [by hypothesis given-w-algebraic]
                          @the-endomorphism-is-algebraic-at-p |
                            isAlgebraicEndomorphism(p, e)
                            [using specialize the-endomorphism-is-algebraic(p) p-is-in-the-parameter-set]
                          @the-pullback-is-algebraic |
                            isAlgebraic(p, pullback(e, w))
                            [using specialize pullback-preserves-algebraicity(p, e, w) the-endomorphism-is-algebraic-at-p w-is-algebraic]
                          @the-pair-spans |
                            spansTheWeilPlane(p, w, pullback(e, w))
                            [using specialize the-endomorphism-spans(p, w) p-is-in-the-parameter-set w-is-nonzero]
                          @the-partner-works |
                            spansTheWeilPlane(p, w, pullback(e, w)) and isAlgebraic(p, pullback(e, w))
                            [by and_intro the-pair-spans the-pullback-is-algebraic]
                          @conclusion-a-partner-exists |
                            exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v)
                            [by exists_intro(pullback(e, w)) the-partner-works]
                        }
                      @conclusion-algebraic-gives |
                        isAlgebraic(p, w) ->
                          (exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v))
                        [by implies_intro given-w-algebraic]
                    }
                  @conclusion-nonzero-gives |
                    (not isZeroClass(w)) -> isAlgebraic(p, w) ->
                      (exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v))
                    [by implies_intro given-w-nonzero]
                }
              @conclusion-at-w |
                inParameterSet(p) -> (not isZeroClass(w)) -> isAlgebraic(p, w) ->
                  (exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v))
                [by implies_intro given-p-in-the-parameter-set]
            }
          @discharge-w |
            forall w: CycleClass;
              inParameterSet(p) -> (not isZeroClass(w)) -> isAlgebraic(p, w) ->
              (exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v))
            [by forall_intro generalize-w]
        }
      @conclusion-at-the-endomorphism |
        forall p: Period; forall w: CycleClass;
          inParameterSet(p) -> (not isZeroClass(w)) -> isAlgebraic(p, w) ->
          (exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v))
        [by forall_intro generalize-p]
    }
  @conclusion |
    forall p: Period; forall w: CycleClass;
      inParameterSet(p) -> (not isZeroClass(w)) -> isAlgebraic(p, w) ->
      (exists v: CycleClass; spansTheWeilPlane(p, w, v) and isAlgebraic(p, v))
    [by exists_elim with-the-endomorphism]
qed
```

## The cited inputs

§12.4 rests on four standard facts about the cycle class map and the conjugation endomorphism,
plus Proposition 12.3 (proved in `construction/marked-class-right.md`). Each is a `hole`
with its source named.


```2b4m
// WELL-KNOWN: the image of the cycle class map CH^4(A) ⊗ Q -> H^8(A, Q) is a Q-subspace.
hole theAlgebraicClassesFormASubspace cites "standard: the image of CH^4(A) (x) Q -> H^8(A,Q) is a Q-subspace": forall p: Period;
  forall z: CycleClass; forall w: CycleClass;
  isAlgebraic(p, add(z, w)) -> isAlgebraic(p, z) -> isAlgebraic(p, w)

// WELL-KNOWN: theta is a divisor class, so any rational multiple of theta^4 is algebraic.
hole aPowerOfThePolarizationIsAlgebraic cites "standard: theta is a divisor class, so theta^4 is an intersection of divisors": forall p: Period; forall a: CycleClass;
  inParameterSet(p) -> isAlgebraic(p, scale(a, polarizationPower))

// WELL-KNOWN: functoriality of the cycle class map under an algebraic correspondence.
hole theCycleClassMapIsFunctorial cites "standard: functoriality of the cycle class map under an algebraic correspondence": forall p: Period; forall e: Endomorphism;
  forall z: CycleClass;
  isAlgebraicEndomorphism(p, e) -> isAlgebraic(p, z) -> isAlgebraic(p, pullback(e, z))

// The endomorphism m*1 + D of §12.4. Its two halves are separated:
//
//   ALGEBRAICITY — standard: an integral matrix commuting with every period in U defines an
//   algebraic endomorphism of every fiber. Axiom, cited, and a fair one.
//
//   SPANNING — the paper's eigenvalue argument, PROVED in `eigenvalues/independence.md`
//   (`theConjugationProducesASpanningPartner`): the eigenvalues are nonreal conjugates, hence
//   distinct, hence no scalar is both, hence w and its pullback are non-proportional, hence
//   spanning. The two axioms it rests on are the eigenspace linear algebra and
//   dim W_K = 2 — both standard — plus the elementary numeric fact that
//   arg(m + i*sqrt(d)) lies in (0, pi/8) under the paper's bound, checked numerically for
//   d = 1..39 including the bound's tightness.
//
// The existential below is assembled from one citation and one proof.
hole theConjugationIsAlgebraic cites "manuscript §12.4: The integral matrix m.1_8 + D commutes with every period in U, and hence defines an algebraic endomorphism of every A_Pi": forall p: Period;
  inParameterSet(p) -> isAlgebraicEndomorphism(p, eigenvalues.theConjugation)

// §12.4's endomorphism, PROVED rather than assumed.
theorem theConjugationEndomorphism: exists e: Endomorphism;
  (forall p: Period; inParameterSet(p) -> isAlgebraicEndomorphism(p, e)) and
  (forall p: Period; forall w: CycleClass;
  inParameterSet(p) -> (not isZeroClass(w)) -> spansTheWeilPlane(p, w, pullback(e, w)))
proof
  @the-conjugation-is-algebraic |
    forall p: Period;
      inParameterSet(p) -> isAlgebraicEndomorphism(p, eigenvalues.theConjugation)
    [by cite theConjugationIsAlgebraic]
  @the-conjugation-spans |
    forall p: Period; forall w: CycleClass;
      inParameterSet(p) -> (not isZeroClass(w)) ->
      spansTheWeilPlane(p, w, pullback(eigenvalues.theConjugation, w))
    [by cite eigenvalues.theConjugationProducesASpanningPartner]
  @both-halves |
    (forall p: Period;
      inParameterSet(p) -> isAlgebraicEndomorphism(p, eigenvalues.theConjugation)) and
      (forall p: Period; forall w: CycleClass;
      inParameterSet(p) -> (not isZeroClass(w)) ->
      spansTheWeilPlane(p, w, pullback(eigenvalues.theConjugation, w)))
    [by and_intro the-conjugation-is-algebraic the-conjugation-spans]
  @conclusion |
    exists e: Endomorphism;
      (forall p: Period; inParameterSet(p) -> isAlgebraicEndomorphism(p, e)) and
      (forall p: Period; forall w: CycleClass;
      inParameterSet(p) -> (not isZeroClass(w)) -> spansTheWeilPlane(p, w, pullback(e, w)))
    [by exists_intro(eigenvalues.theConjugation) both-halves]
qed
```

### Lemmas 12.1 and 12.2, and Proposition 12.3

```2b4m
// Lemmas 12.1 + 12.2, decomposed until only citations remain.
//
//   LEMMA 12.2's constancy — PROVED in `chern-constancy.md` from homotopy invariance of the
//   Chern character plus connectedness of the component.
//   §12.4's SPREADING — PROVED in the same file (`theMarkedClassSpreadsAcrossTheParameterSet`)
//   from that constancy plus surjectivity of H -> U (Lemma 12.1) and ch_4(O_Z) = [Z] of [14].
//   LEMMA 12.1's exceptional loci — PROVED in `hilbert-parameters.md` from Remmert's proper
//   mapping theorem plus "a proper closed analytic subset has empty interior".
//
// §12.4's step from "algebraic at a good period" to "marked by a component", now MODELLED
// on Lemma 12.1 rather than held as an invented bridge.
//
// §12.4: "Its Hilbert point belongs to one of the connected parameter spaces H in Lemma
// 12.1. Since Pi was chosen outside E_Hilb, that component's image cannot be a proper subset
// of U. Thus H -> U is surjective."
//
// Lemma 12.1 supplies the two halves separately, and both are citations:
//
//   COVERING  — "every closed subscheme of every fiber A_Pi occurs in at least one family."
//   PROPERNESS — "the union E_Hilb of those images which are proper subsets is a countable
//                 union of proper closed analytic subsets of U", so a period avoiding
//                 E_Hilb is in no proper image.
//
// Composing them gives the step: the class's subscheme occurs in SOME component, and since
// the period avoids E_Hilb that component's image is not proper.

// The component a class's Hilbert point lands in.
//
// The E_Hilb clause of Lemma 12.1 is not needed here: `everyAlgebraicClassOccursInSomeFamily`
// already delivers a component, and `chern.inComponent` is what the spreading consumes.
func markingComponentOf(p: Period, z: CycleClass) => ParameterPoint

// CITATION (Lemma 12.1, the covering clause): an algebraic class at a period is the marked
// class of a parameter point in some component of the countable collection.
hole everyAlgebraicClassOccursInSomeFamily cites "manuscript Lemma 12.1: every closed subscheme of every fiber A_Pi occurs in at least one family": forall p: Period; forall z: CycleClass;
  inParameterSet(p) -> isAlgebraic(p, z) ->
  (chern.inComponent(markingComponentOf(p, z)) and
  chern.markedClassAt(markingComponentOf(p, z)) = z)

// §12.4's step, PROVED from Lemma 12.1's two clauses.
theorem anAlgebraicClassAtAGoodPeriodIsMarkedByTheComponent: forall p: Period;
  forall z: CycleClass;
  inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
  (exists b: ParameterPoint;
  chern.inComponent(b) and chern.markedClassAt(b) = z)
proof
  @generalize-p |
    fix p: Period {
      @generalize-z |
        fix z: CycleClass {
          @given-p-in-the-parameter-set |
            assume inParameterSet(p) {
              @p-is-in-the-parameter-set |
                inParameterSet(p)
                [by hypothesis given-p-in-the-parameter-set]
              @given-p-avoids |
                assume avoidsExceptional(p) {
                  @given-z-algebraic |
                    assume isAlgebraic(p, z) {
                      @z-is-algebraic |
                        isAlgebraic(p, z)
                        [by hypothesis given-z-algebraic]
                      @the-class-occurs-in-a-family |
                        chern.inComponent(markingComponentOf(p, z)) and
                          chern.markedClassAt(markingComponentOf(p, z)) = z
                        [using specialize everyAlgebraicClassOccursInSomeFamily(p, z) p-is-in-the-parameter-set z-is-algebraic]
                      @conclusion-a-marking-point-exists |
                        exists b: ParameterPoint;
                          chern.inComponent(b) and chern.markedClassAt(b) = z
                        [by exists_intro(markingComponentOf(p, z)) the-class-occurs-in-a-family]
                    }
                  @conclusion-algebraic-gives |
                    isAlgebraic(p, z) ->
                      (exists b: ParameterPoint;
                      chern.inComponent(b) and chern.markedClassAt(b) = z)
                    [by implies_intro given-z-algebraic]
                }
              @conclusion-avoids-gives |
                avoidsExceptional(p) -> isAlgebraic(p, z) ->
                  (exists b: ParameterPoint;
                  chern.inComponent(b) and chern.markedClassAt(b) = z)
                [by implies_intro given-p-avoids]
            }
          @conclusion-at-z |
            inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
              (exists b: ParameterPoint;
              chern.inComponent(b) and chern.markedClassAt(b) = z)
            [by implies_intro given-p-in-the-parameter-set]
        }
      @discharge-z |
        forall z: CycleClass;
          inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
          (exists b: ParameterPoint;
          chern.inComponent(b) and chern.markedClassAt(b) = z)
        [by forall_intro generalize-z]
    }
  @conclusion |
    forall p: Period; forall z: CycleClass;
      inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
      (exists b: ParameterPoint;
      chern.inComponent(b) and chern.markedClassAt(b) = z)
    [by forall_intro generalize-p]
qed

// §12.4's spreading principle, PROVED rather than assumed.
theorem theMarkedClassIsConstantAcrossTheFamily: forall p: Period; forall z: CycleClass;
  inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
  forall q: Period; inParameterSet(q) -> isAlgebraic(q, z)
proof
  @the-marked-class-spreads |
    forall b: ParameterPoint;
      chern.inComponent(b) ->
      forall q: Period; inParameterSet(q) -> isAlgebraic(q, chern.markedClassAt(b))
    [by cite chern.theMarkedClassSpreadsAcrossTheParameterSet]
  @generalize-p |
    fix p: Period {
      @generalize-z |
        fix z: CycleClass {
          @given-p-in-the-parameter-set |
            assume inParameterSet(p) {
              @p-is-in-the-parameter-set |
                inParameterSet(p)
                [by hypothesis given-p-in-the-parameter-set]
              @given-p-avoids-the-exceptional-loci |
                assume avoidsExceptional(p) {
                  @p-avoids-the-exceptional-loci |
                    avoidsExceptional(p)
                    [by hypothesis given-p-avoids-the-exceptional-loci]
                  @given-z-algebraic-at-p |
                    assume isAlgebraic(p, z) {
                      @z-is-algebraic-at-p |
                        isAlgebraic(p, z)
                        [by hypothesis given-z-algebraic-at-p]
                      @a-parameter-point-marks-z |
                        exists b: ParameterPoint;
                          chern.inComponent(b) and chern.markedClassAt(b) = z
                        [using specialize anAlgebraicClassAtAGoodPeriodIsMarkedByTheComponent(p, z) p-is-in-the-parameter-set p-avoids-the-exceptional-loci z-is-algebraic-at-p]
                      @with-the-marking-point |
                        unpack b: ParameterPoint from a-parameter-point-marks-z {
                          @the-marking-facts |
                            chern.inComponent(b) and chern.markedClassAt(b) = z
                            [by hypothesis with-the-marking-point]
                          @the-point-is-in-the-component |
                            chern.inComponent(b)
                            [by and_elim_left the-marking-facts]
                          @the-point-marks-z |
                            chern.markedClassAt(b) = z
                            [by and_elim_right the-marking-facts]
                          @the-marked-class-is-algebraic-everywhere |
                            forall q: Period;
                              inParameterSet(q) -> isAlgebraic(q, chern.markedClassAt(b))
                            [using specialize the-marked-class-spreads(b) the-point-is-in-the-component]
                          @conclusion-z-is-algebraic-everywhere |
                            forall q: Period; inParameterSet(q) -> isAlgebraic(q, z)
                            [by rewrite the-point-marks-z the-marked-class-is-algebraic-everywhere]
                        }
                      @conclusion-spread-at-z |
                        forall q: Period; inParameterSet(q) -> isAlgebraic(q, z)
                        [by exists_elim with-the-marking-point]
                    }
                  @conclusion-algebraic-gives |
                    isAlgebraic(p, z) ->
                      (forall q: Period; inParameterSet(q) -> isAlgebraic(q, z))
                    [by implies_intro given-z-algebraic-at-p]
                }
              @conclusion-avoiding-gives |
                avoidsExceptional(p) -> isAlgebraic(p, z) ->
                  (forall q: Period; inParameterSet(q) -> isAlgebraic(q, z))
                [by implies_intro given-p-avoids-the-exceptional-loci]
            }
          @conclusion-at-z |
            inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
              (forall q: Period; inParameterSet(q) -> isAlgebraic(q, z))
            [by implies_intro given-p-in-the-parameter-set]
        }
      @discharge-z |
        forall z: CycleClass;
          inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
          forall q: Period; inParameterSet(q) -> isAlgebraic(q, z)
        [by forall_intro generalize-z]
    }
  @conclusion |
    forall p: Period; forall z: CycleClass;
      inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
      forall q: Period; inParameterSet(q) -> isAlgebraic(q, z)
    [by forall_intro generalize-p]
qed

// Proposition 12.3, re-exported from the file that proves it — the detection chain of
// `../detection/` plus §12.3's cited last move.
theorem aMarkedAlgebraicClassExistsAtSomeGoodPeriod =
  construction.aMarkedAlgebraicClassExistsAtSomeGoodPeriod
```
