# The proof architecture, top-down

A `2b4m` formalization of the **main thrust** of OpenAI's withdrawn manuscript
*"Algebraicity of Weil classes on split abelian eightfolds"*, built **top-down with `hole`s**.

## Method

Start from Theorem 1.1. State every premise it needs as a `hole` — an aspirational
placeholder the checker tracks but does not let you forget. Prove the theorem from those.
Then take each hole in turn: either *prove* it from smaller holes, or recognise it as a
**result the paper cites** and flip it to an `axiom`. Repeat until no holes remain.

Why this order matters here, and not just stylistically: writing the axioms first lets the
formalizer *choose* convenient premises, and a convenient premise is how you accidentally
assume the thing you meant to check. Holes-first makes the checker name what is actually
needed. `2b4m check --axioms` then reports the full assumption set, and default `check`
**rejects any hole that survives** — so an unjustified step cannot hide.

A first attempt at this file went axioms-first (kept as `architecture-axioms-first.md.bak`).
Strict check caught a real modelling error in it — see "What the checker caught" below — and
that error is exactly the kind holes-first prevents.

## The objects

The objects shared with the quarantined assumption come from `construction/marked-class.md`,
so the axiom is stated once, in the file that explains what it costs.

```2b4m
import construction <<< "construction/marked-class.md"

sort Period = construction.Period
sort CycleClass = construction.CycleClass
sort Endomorphism

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
func pullback(e: Endomorphism, z: CycleClass) => CycleClass

pred isAlgebraic = construction.isAlgebraic
pred inWeilPlane = construction.inWeilPlane
pred isZeroClass = construction.isZeroClass
pred isAlgebraicEndomorphism(p: Period, e: Endomorphism)

// v and w are independent and span the two-dimensional rational Weil space W_K(A_Π).
pred spansTheWeilPlane(p: Period, v: CycleClass, w: CycleClass)
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

## Classifying the six remaining holes

The instruction was: drive holes back until each is a *well-known result*, then flip it to an
axiom. Doing that honestly means separating the holes that really are citations from the ones
that are the paper's own contributions — because flipping the latter to axioms is where this
method stops being verification and starts being assumption.

| hole | status |
|---|---|
| `algebraicClassesSubtract` | **well-known.** The image of the cycle class map is a ℚ-subspace; closure under subtraction is immediate. Flip to axiom. |
| `aPolarizationPowerIsAlgebraic` | **well-known.** `θ` is a divisor class, `θ⁴` an intersection of divisors. Flip to axiom. |
| `anAlgebraicEndomorphismPreservesAlgebraicity` | **well-known.** Functoriality of the cycle class map under an algebraic correspondence. Flip to axiom. |
| `theConjugationEndomorphismExists` | **mixed.** That `m·1₈ + D` is an algebraic endomorphism is standard; the *independence* is the eigenvalue computation `λ± = (m ± i√d)⁸`, which is elementary arithmetic in ℂ (checked numerically — see below) but is the paper's own step. Split, then flip. |
| `aMarkedClassSpreadsToEveryFiber` | **NOT a citation.** This is Lemmas 12.1 + 12.2, and 12.2 has a multi-page proof of its own: eight syzygy sequences, proper base change, flatness of the eighth syzygy on a possibly-singular base. Flipping it to an axiom assumes a substantial part of the paper. |
| `aMarkedPeriodExists` | **NOT a citation.** This is Proposition 12.3, whose input is Proposition 11.4, which rests on Sections 2–11 — i.e. the entire construction, including the sign bookkeeping of Section 6 and the stabilization traces of §3.4 where the withdrawn error lives. |

So four flip cleanly and two do not. The two that do not are precisely where the paper's
content is, and one of them (`aMarkedPeriodExists`) transitively contains the error. **That is
the honest result of this exercise:** the architecture composes, and what it composes *from*
is assumed.

Stated as a slogan: this formalization proves that *if* Sections 2–11 deliver one algebraic
class with nonzero Weil part at one good period, *then* Theorem 1.1 follows. The withdrawal
says Sections 2–11 do not deliver it.

### The four that flip

```2b4m
// WELL-KNOWN: the image of the cycle class map CH^4(A) ⊗ Q -> H^8(A, Q) is a Q-subspace.
axiom theAlgebraicClassesFormASubspace: forall p: Period;
  forall z: CycleClass; forall w: CycleClass;
  isAlgebraic(p, add(z, w)) -> isAlgebraic(p, z) -> isAlgebraic(p, w)

// WELL-KNOWN: theta is a divisor class, so any rational multiple of theta^4 is algebraic.
axiom aPowerOfThePolarizationIsAlgebraic: forall p: Period; forall a: CycleClass;
  inParameterSet(p) -> isAlgebraic(p, scale(a, polarizationPower))

// WELL-KNOWN: functoriality of the cycle class map under an algebraic correspondence.
axiom theCycleClassMapIsFunctorial: forall p: Period; forall e: Endomorphism;
  forall z: CycleClass;
  isAlgebraicEndomorphism(p, e) -> isAlgebraic(p, z) -> isAlgebraic(p, pullback(e, z))

// The endomorphism m*1 + D, with the eigenvalue argument for independence. The algebraicity
// half is standard (an integral matrix commuting with every period in U); the independence
// half is the paper's own elementary computation, verified numerically in
// the README for d = 1..39, including the tightness of the bound m > sqrt(d)*cot(pi/8).
axiom theConjugationEndomorphism: exists e: Endomorphism;
  (forall p: Period; inParameterSet(p) -> isAlgebraicEndomorphism(p, e)) and
  (forall p: Period; forall w: CycleClass;
  inParameterSet(p) -> (not isZeroClass(w)) -> spansTheWeilPlane(p, w, pullback(e, w)))
```

### The two that do not

These are flipped to axioms as well — otherwise nothing downstream can be checked — but they
are labelled for what they are, and `--axioms` will report them beside the genuine citations.

```2b4m
// Lemma 12.1 + 12.2. The CONSTANCY half (Lemma 12.2) is no longer assumed — it is proved in
// `construction/chern-constancy.md` from homotopy invariance of the Chern character plus
// connectedness of the parameter component, both textbook. What remains assumed here is the
// bridge from that constancy to algebraicity on every fiber, which additionally needs Lemma
// 12.1's surjectivity H -> U and the formula ch_4(O_Z) = [Z] of [14].
//
// NOT fully a citation: Lemma 12.1's construction of the Hilbert parameter spaces is the
// paper's own. Labelled accordingly.
axiom theMarkedClassIsConstantAcrossTheFamily: forall p: Period; forall z: CycleClass;
  inParameterSet(p) -> avoidsExceptional(p) -> isAlgebraic(p, z) ->
  forall q: Period; inParameterSet(q) -> isAlgebraic(q, z)

// NOT a citation: Proposition 12.3, resting on Sections 2-11 — the whole construction, with
// the withdrawn sign error inside it. Quarantined in its own file so that flipping it cannot
// happen quietly: see `construction/marked-class.md`.
axiom aMarkedAlgebraicClassExistsAtSomeGoodPeriod =
  construction.aMarkedAlgebraicClassExistsAtSomeGoodPeriod
```
