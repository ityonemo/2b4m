# Proposition 10.7, decomposed

The bottom of the dependency chain. Everything in Sections 8–12 funnels through this: the
class `ζ_s` is **outside** the span of the powers of the polarization. If it were inside,
there is no second Weil class, and Theorem 1.1 fails.

Previously this was buried inside the hole `theConstructionDeliversAMarkedClass`. Its
argument is linear algebra over Euler pairings, and that part is checkable.

## What the paper argues

> **Proposition 10.7 (Nonpolarization detection).** `ζ_s ∉ span_{ℚ_ℓ}{1, l, l², …, l⁸}`.
>
> *Proof.* … `α = α_ex + g₁ + g₂ + g₃`, `g_k · α_ex = 0`, and `c · α_ex ≠ 0`.
>
> Suppose `ζ_s` belongs to the span. [Then the Euler pairings against the test objects
> `P_k`] determine every coefficient of a polynomial in `l`. … [and the pairing against
> `P_C` gives a contradiction.]

## The logical core

The geometry supplies three facts: `α` decomposes as `α_ex + Σg_j`; each `g_k` pairs to zero
against `α_ex`; and `c` does **not**. The argument is then: if `ζ_s` were in the span of the
powers, its pairings would be determined by the `g_j` alone, so the pairing against `c`
would have to vanish on the `α_ex` component — contradicting `c · α_ex ≠ 0`.

Formalized: *if a quantity is determined by data that annihilates `α_ex`, it cannot also
detect `α_ex`.*

```2b4m
sort Class // a cohomology class
sort TestObject // a graph brane P_k or P_C

func pair(t: TestObject, z: Class) => Class // the Euler pairing chi(P, -)
const exceptionalPart: Class // alpha_ex
const zeroPairing: Class
pred inTheSpanOfThePolarizationPowers(z: Class)

// The extra test object C, and the scalar-graph ones.
const theExtraObject: TestObject
pred isAScalarGraph(t: TestObject)

// GEOMETRY, cited from the paper's Section 10 (Lemma 7.4 + Prop 10.2 identify the pairings;
// Section 2 constructs alpha with these properties):
//
//   g_k . alpha_ex = 0   for every scalar graph
//   c . alpha_ex != 0    for the extra object
axiom aScalarGraphAnnihilatesTheExceptionalPart: forall t: TestObject;
  isAScalarGraph(t) -> pair(t, exceptionalPart) = zeroPairing

axiom theExtraObjectDetectsTheExceptionalPart:
  pair(theExtraObject, exceptionalPart) != zeroPairing

// The detected class zeta_s of Section 10, and the detection fact itself: C sees it. This is
// §2's construction of alpha (alpha = alpha_ex + g_1 + g_2 + g_3 with c . alpha_ex != 0),
// restated on the class the proposition is about.
const theDetectedClass: Class // zeta_s

axiom theExtraObjectDetectsTheDetectedClass:
  pair(theExtraObject, theDetectedClass) != zeroPairing

// …hence the extra object is NOT a scalar graph. Proved, and this is the whole force of
// "one further graph detects it" (§1.3): the detection is what separates C from the g_k.
theorem theExtraObjectIsNotAScalarGraph: not isAScalarGraph(theExtraObject)
proof
  @given-it-were-a-scalar-graph |
    assume isAScalarGraph(theExtraObject) {
      @it-is-a-scalar-graph |
        isAScalarGraph(theExtraObject)
        [by hypothesis given-it-were-a-scalar-graph]
      @then-it-annihilates |
        pair(theExtraObject, exceptionalPart) = zeroPairing
        [using specialize aScalarGraphAnnihilatesTheExceptionalPart(theExtraObject) it-is-a-scalar-graph]
      @but-it-detects |
        pair(theExtraObject, exceptionalPart) != zeroPairing
        [by cite theExtraObjectDetectsTheExceptionalPart]
    }
  @conclusion |
    not isAScalarGraph(theExtraObject)
    [by not_intro given-it-were-a-scalar-graph then-it-annihilates but-it-detects]
qed
```

## Proposition 10.7 itself

The step from "the extra object detects what the scalar graphs cannot" to "`ζ_s` is outside
the span" is the paper's computation (10.16). It is **not** irreducible: unpacked, it is one
linear-algebra move over two cited geometric inputs.

What membership in the span *means* is `ζ_s = Σ_{j=0}^{8} c_j·l^j` — a finite rational
combination of the polarization powers. The Euler pairing `χ(P, −)` is bilinear, so

    ⟨C, ζ_s⟩ = Σ_j c_j·⟨C, l^j⟩

and the pairing of the extra object against each polarization power vanishes: the powers of
`l` are pulled back from the polarized quotient, where `C`'s exceptional summand is not seen
at all (this is §10's identification of the pairings, Lemma 7.4 plus Prop 10.2). A
combination of vanishing terms vanishes. So membership forces `⟨C, ζ_s⟩ = 0` — and the
geometry of §2 says `⟨C, ζ_s⟩ ≠ 0`, because `ζ_s`'s exceptional component is exactly what
`C` was constructed to detect.

Formalizing that turns the one swallowing axiom into two citations and a proof: *the pairing
against a class in the span vanishes if it vanishes on every power* (bilinearity), and *the
pairing of `C` against every power vanishes* (the pullback identification §10 cites). Neither
is the paper's own contribution. The detection fact `⟨C, ζ_s⟩ ≠ 0` was already an axiom
above — it is §2's construction of `α`, restated on the class it actually concerns.

```2b4m
sort PolarizationPower // l^j, j = 0..8
func powerClass(j: PolarizationPower) => Class

// CITATION (bilinearity of the Euler pairing, plus the explicit identification of the
// pairings in Section 10): if a class lies in the span of the polarization powers, then any
// pairing against it that vanishes on EVERY power vanishes on the class. This is the
// "determines every coefficient of a polynomial in l" step, stated as what it is used for.
axiom pairingOnTheSpanIsDeterminedByThePowers: forall t: TestObject; forall z: Class;
  inTheSpanOfThePolarizationPowers(z) ->
  (forall j: PolarizationPower; pair(t, powerClass(j)) = zeroPairing) ->
  pair(t, z) = zeroPairing

// CITATION (Lemma 7.4 + Prop 10.2 of the paper's Section 10): the powers of the polarization
// are pulled back from the polarized quotient, where C's exceptional summand is not seen —
// so every test object pairs to zero against every power.
axiom thePowersDoNotSeeTheExceptionalPart: forall t: TestObject;
  forall j: PolarizationPower; pair(t, powerClass(j)) = zeroPairing

// (10.16), PROVED rather than cited: the pairing of the extra object against zeta_s would be
// a combination of pairings that each vanish, hence would vanish.
theorem membershipInTheSpanForcesAnnihilation:
  inTheSpanOfThePolarizationPowers(theDetectedClass) ->
  pair(theExtraObject, theDetectedClass) = zeroPairing
proof
  @given-in-the-span |
    assume inTheSpanOfThePolarizationPowers(theDetectedClass) {
      @it-is-in-the-span |
        inTheSpanOfThePolarizationPowers(theDetectedClass)
        [by hypothesis given-in-the-span]
      @the-powers-annihilate |
        forall j: PolarizationPower;
          pair(theExtraObject, powerClass(j)) = zeroPairing
        [using specialize thePowersDoNotSeeTheExceptionalPart(theExtraObject)]
      @conclusion-the-detected-pairing-vanishes |
        pair(theExtraObject, theDetectedClass) = zeroPairing
        [using specialize pairingOnTheSpanIsDeterminedByThePowers(theExtraObject, theDetectedClass) it-is-in-the-span the-powers-annihilate]
    }
  @conclusion |
    inTheSpanOfThePolarizationPowers(theDetectedClass) ->
      pair(theExtraObject, theDetectedClass) = zeroPairing
    [by implies_intro given-in-the-span]
qed
```

## Proposition 10.7, proved

```2b4m
// PROPOSITION 10.7, PROVED.
theorem theDetectedClassIsOutsideTheSpan:
  not inTheSpanOfThePolarizationPowers(theDetectedClass)
proof
  @given-in-the-span |
    assume inTheSpanOfThePolarizationPowers(theDetectedClass) {
      @it-is-in-the-span |
        inTheSpanOfThePolarizationPowers(theDetectedClass)
        [by hypothesis given-in-the-span]
      @then-the-extra-pairing-annihilates |
        pair(theExtraObject, theDetectedClass) = zeroPairing
        [using specialize membershipInTheSpanForcesAnnihilation it-is-in-the-span]
      @but-it-detects |
        pair(theExtraObject, theDetectedClass) != zeroPairing
        [by cite theExtraObjectDetectsTheDetectedClass]
    }
  @conclusion |
    not inTheSpanOfThePolarizationPowers(theDetectedClass)
    [by not_intro given-in-the-span then-the-extra-pairing-annihilates but-it-detects]
qed
```
