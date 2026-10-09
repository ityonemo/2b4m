# §3.4, repaired

Lemma 3.6 of the withdrawn manuscript, as close to verbatim as `2b4m` allows. Its reference
[6] is axiomatized in `traces.b4m` with the hypotheses the source states.

This file is the **root of the dependency chain**: Lemma 3.6 produces the Lagrangian of
Section 3, which carries Sections 4–7, which carry 8–11, which give Proposition 12.3, which
`architecture.md` turns into Theorem 1.1. So an error here surfaces at the top.

## What the manuscript says

> Put `m = −I(f₁) > 0`. Insert `m` reverse traces in separated radial collars near the
> puncture, ordered from the m-fold stabilization `φₘ` at the innermost end to `φ₀` outward.
> The negative link is now loose and the total signed double count is `I(f₁) + m = 0`.
>
> Apply Eliashberg–Murphy's exact cancellation theorem [9, Theorem 2.3]. Its hypotheses here
> are as follows: … and its signed double count is zero.

Reading the insertion in the direction the manuscript specifies — innermost `φₘ` outward to
`φ₀` — each trace runs `φ_{j+1} → φ_j`, from a stabilization down to the link it stabilizes.
That is [6]'s reverse direction, sign `(−1)ᵏ = +1` at `k = 4`, exactly as (3.6) says.

```2b4m
import traces <<< "traces-wrong.b4m"
import integer <<< "std/integer.b4m"

sort Link = traces.Link
sort Int = integer.Int
const ZERO = integer.ZERO
const ONE = integer.ONE
func neg = integer.neg
func sub = integer.sub
func add = integer.add
func mul = integer.mul
pred less_than = integer.less_than
func stabilize = traces.stabilize
func traceSign = traces.traceSign
pred isLoose = traces.isLoose
axiom aStabilizationIsLoose = traces.aStabilizationIsLoose
axiom forwardTraceSign = traces.forwardTraceSign
axiom reverseTraceSign = traces.reverseTraceSign

// φ₀ — "standard real-plane Legendrian link ϕ₀ ⊂ S¹⁵ at the negative end" (§3.4).
const phiZero: Link

// The FORWARD trace φ₀ → φ₁, sign (-1)^{k-1} = −1 at k = 4, by [6] Lemma 3.4's first case
// ("for any φ", no hypothesis). Not used by §3.4's insertion — which is all reverse traces —
// but it is the other half of (3.6) and is proved here for completeness.
theorem theForwardTraceContributesMinusOne:
  traceSign(phiZero, stabilize(phiZero)) = neg(ONE)
proof
  @conclusion |
    traceSign(phiZero, stabilize(phiZero)) = neg(ONE)
    [using specialize forwardTraceSign(phiZero)]
qed
```

## The consequence for the count

The manuscript needs the total to be exactly zero, because [9, Theorem 2.3]'s hypothesis is
"its signed double count is zero". With `m` reverse traces at `+1` it gets `I(f₁) + m = 0`,
and — on [6]'s signs as [6] states them — that arithmetic is correct.

The withdrawal notice disputes the sign itself, not the arithmetic: if each reverse trace
carries `−1` in the manuscript's convention, the count is `I(f₁) − m = −2m ≠ 0` and
[9, Theorem 2.3] does not apply. Adjudicating that requires comparing [6]'s orientation
convention against the manuscript's, which this directory does not do.

```2b4m
// A reverse trace at a stabilized target, which is what every inserted trace in §3.4 is.
// No looseness step is needed: reverseTraceSign carries no guard, per [6]'s G1-G4 table.
theorem anInnerTraceContributesMinusOne: forall l: Link;
  traceSign(stabilize(stabilize(l)), stabilize(l)) = neg(ONE)
proof
  @generalize-l |
    fix l: Link {
      @conclusion-at-l |
        traceSign(stabilize(stabilize(l)), stabilize(l)) = neg(ONE)
        [using specialize reverseTraceSign(stabilize(l))]
    }
  @conclusion |
    forall l: Link; traceSign(stabilize(stabilize(l)), stabilize(l)) = neg(ONE)
    [by forall_intro generalize-l]
qed
```

## Lemma 3.6, and what it carries

The manuscript's Lemma 3.6 concludes that the immersion can be replaced by an **embedded**
spin Lagrangian — which is what Section 3 needs, and what everything above Section 3 rests
on. Its proof applies [9, Theorem 2.3], whose hypothesis is the zero count.

Transcribing that application makes the dependency explicit: Lemma 3.6 needs the zero count,
the zero count needs the outermost trace to contribute `+1`, and that is the hole.

```2b4m
// -- the negative asymptote is loose --------------------------------------------------------
//
// [9, Thm 2.3]'s other hypothesis: the asymptotic negative boundary has a loose component.
// §3.4 inserts traces ordered "from the m-fold stabilization ϕ_m at the innermost end to ϕ_0
// outward", so the link the construction works with is `stabilize(phiZero)` — and a
// stabilization is loose by [6] §2.2's definition. No separate assumption needed.
theorem theNegativeLinkIsLoose: isLoose(stabilize(phiZero))
proof
  @conclusion |
    isLoose(stabilize(phiZero))
    [using specialize aStabilizationIsLoose(phiZero)]
qed

// The total signed double count after inserting the traces: the manuscript's `I(f₁) + m`.
// Modelled as an actual SUM, not an opaque constant, so std/integer discharges the arithmetic
// rather than it being assumed.
const initialIndex: Int // I(f₁), negative; the manuscript puts m = -I(f₁)

// §3.4: "Put m = -I(f1) > 0", i.e. I(f1) < 0. A cited fact rather than a code comment,
// because whether this chain's count can reach zero turns on I(f1) being STRICTLY negative.
hole theInitialIndexIsNegative
  cites "manuscript §3.4: Put m = -I(f1) > 0 — equation (3.4) gives I(f1) < 0":
  less_than(initialIndex, ZERO)

// `insertedTotal(n)` = n inserted REVERSE traces, each carrying whatever sign this chain's
// traces module gives: n times that sign.
//
// The total is n times the sign, NOT a constant: that is what makes the right/wrong split
// meaningful. (Defining it as `insertedTotal(n) = n` would hard-code +1 into the definition
// and both chains would pass, making the right/wrong split meaningless.)
const theReverseTraceSign: Int

func insertedTotal(n: Int) => Int:
  insertedTotal(n) = mul(n, theReverseTraceSign)

// The inserted traces of §3.4 are reverse traces at stabilized targets, so each carries
// `reverseTraceSign`'s value — +1 in the right chain, -1 in the wrong one.
hole theInsertedSignIsTheReverseTraceSign
  cites "manuscript §3.4: Insert m reverse traces in separated radial collars near the puncture, ordered from the m-fold stabilization phi_m at the innermost end to phi_0 outward":
  theReverseTraceSign = traceSign(stabilize(phiZero), phiZero)

// The total signed double count after the insertion: the immersion's own index plus what the
// inserted traces contribute. This is §3.4's "the total signed double count is I(f1) + m".
func theSignedDoubleCount(n: Int) => Int:
  theSignedDoubleCount(n) = add(initialIndex, insertedTotal(n))

// §3.4's "the total signed double count is I(f1) + m", now a THEOREM read straight off the
// definition of theSignedDoubleCount above.
theorem theCountIsTheSum: forall n: Int;
  theSignedDoubleCount(n) = add(initialIndex, insertedTotal(n))
proof
  @conclusion |
    forall n: Int; theSignedDoubleCount(n) = add(initialIndex, insertedTotal(n))
    [by definition(0) theSignedDoubleCount]
qed

// [9, Theorem 2.3] — Eliashberg–Murphy, "Lagrangian caps", arXiv:1303.0586v1 — which is
// what the manuscript's §3.4 actually applies. Verbatim:
//
//   "Let (X, lambda) be a simply connected Liouville manifold with a negative end X_-, and
//    f : L -> X a cylindrical at -infinity exact self-transverse Lagrangian immersion with
//    finitely many self intersections. Suppose that I(f) = 0, and the asymptotic negative
//    boundary Lambda of f has a component which is LOOSE in the complement of the others.
//    If n = 3 suppose, in addition, that X \ f(L) has infinite Gromov width. Then there
//    exists a compactly supported Hamiltonian regular homotopy f_t, connecting f_0 = f with
//    an EMBEDDING f_1."
//
// Both of [9]'s substantive hypotheses are carried below: the zero count AND a loose
// component of the asymptotic negative boundary. (Note this is [9], arXiv:1303.0586v1 — NOT
// [6] Thm 3.6, which is the conical-point version and a different result.)
pred anEmbeddedLagrangianExists()
hole exactCancellation cites "arXiv:1303.0586v1 (Eliashberg-Murphy, Lagrangian caps) Thm 2.3: I(f)=0 + a loose negative-boundary component => embedding": forall n: Int;
  isLoose(stabilize(phiZero)) -> theSignedDoubleCount(n) = ZERO ->
  anEmbeddedLagrangianExists()

// THE REPAIRED COUNT. With m+2 traces — m+1 reverse at +1 and the outermost forward at −1 —
// THE MANUSCRIPT'S INSERTION, as a counting fact. §3.4: "Put m = -I(f1) > 0. Insert m
// reverse traces ... the total signed double count is I(f1) + m = 0." Each reverse trace
// carries +1 by equation (3.6), so m of them total m = -I(f1).
//
// The inserted total, as a function of this chain's sign.
theorem theInsertedTracesTotal:
  insertedTotal(neg(initialIndex)) = mul(neg(initialIndex), theReverseTraceSign)
proof
  @the-total-is-n-times-the-sign |
    forall n: Int; insertedTotal(n) = mul(n, theReverseTraceSign)
    [by definition(0) insertedTotal]
  @conclusion |
    insertedTotal(neg(initialIndex)) = mul(neg(initialIndex), theReverseTraceSign)
    [by forall_elim(neg(initialIndex)) the-total-is-n-times-the-sign]
qed

// This chain's sign, read off its traces module.
theorem theInsertedSignValue: theReverseTraceSign = neg(ONE)
proof
  @the-inserted-sign-is-the-reverse-trace-sign |
    theReverseTraceSign = traceSign(stabilize(phiZero), phiZero)
    [by cite theInsertedSignIsTheReverseTraceSign]
  @the-reverse-trace-sign |
    traceSign(stabilize(phiZero), phiZero) = neg(ONE)
    [using specialize reverseTraceSign(phiZero)]
  @conclusion |
    theReverseTraceSign = neg(ONE)
    [using chain the-inserted-sign-is-the-reverse-trace-sign the-reverse-trace-sign]
qed

// THE COUNT, with this chain's sign. m traces at -1 total -m = I(f1), so the count is
// I(f1) + I(f1) = -2m. This is the withdrawal notice's arithmetic, kernel-checked.
theorem theCountIsTwiceTheInitialIndex:
  theSignedDoubleCount(neg(initialIndex)) = add(initialIndex, initialIndex)
proof
  @the-count-is-the-sum |
    theSignedDoubleCount(neg(initialIndex))
      = add(initialIndex, insertedTotal(neg(initialIndex)))
    [using specialize theCountIsTheSum(neg(initialIndex))]
  @the-inserted-total |
    insertedTotal(neg(initialIndex)) = mul(neg(initialIndex), theReverseTraceSign)
    [by cite theInsertedTracesTotal]
  @the-sign-is-minus-one |
    theReverseTraceSign = neg(ONE)
    [by cite theInsertedSignValue]
  @the-total-at-minus-one |
    insertedTotal(neg(initialIndex)) = mul(neg(initialIndex), neg(ONE))
    [by rewrite the-sign-is-minus-one the-inserted-total]
  @minus-m-times-minus-one-is-the-index |
    mul(neg(initialIndex), neg(ONE)) = initialIndex
    [using polynomial(integer)]
  @the-inserted-total-is-the-index |
    insertedTotal(neg(initialIndex)) = initialIndex
    [using chain the-total-at-minus-one minus-m-times-minus-one-is-the-index]
  @conclusion |
    theSignedDoubleCount(neg(initialIndex)) = add(initialIndex, initialIndex)
    [by rewrite the-inserted-total-is-the-index the-count-is-the-sum]
qed

// …and it is NOT zero. I(f1) < 0 gives I(f1) + I(f1) < I(f1) + 0 = I(f1) < 0, so the count is
// strictly negative. This is the notice's "-2m != 0", from std/integer's order theory.
theorem theCountIsNegative:
  less_than(theSignedDoubleCount(neg(initialIndex)), ZERO)
proof
  @the-index-is-negative |
    less_than(initialIndex, ZERO)
    [by cite theInitialIndexIsNegative]
  @adding-the-index-preserves-order |
    less_than(add(initialIndex, initialIndex), add(initialIndex, ZERO))
    [using specialize integer.additionPreservesOrder(initialIndex, ZERO, initialIndex) the-index-is-negative]
  @adding-zero-does-nothing |
    add(initialIndex, ZERO) = initialIndex
    [using polynomial(integer)]
  @twice-the-index-is-below-the-index |
    less_than(add(initialIndex, initialIndex), initialIndex)
    [by rewrite adding-zero-does-nothing adding-the-index-preserves-order]
  @twice-the-index-is-negative |
    less_than(add(initialIndex, initialIndex), ZERO)
    [using specialize integer.lessThanTransitive(add(initialIndex, initialIndex), initialIndex, ZERO) twice-the-index-is-below-the-index the-index-is-negative]
  @the-count-is-twice-the-index |
    theSignedDoubleCount(neg(initialIndex)) = add(initialIndex, initialIndex)
    [by cite theCountIsTwiceTheInitialIndex]
  @conclusion |
    less_than(theSignedDoubleCount(neg(initialIndex)), ZERO)
    [by rewrite the-count-is-twice-the-index twice-the-index-is-negative]
qed

theorem theCountIsNotZero:
  theSignedDoubleCount(neg(initialIndex)) != ZERO
proof
  @the-count-is-negative |
    less_than(theSignedDoubleCount(neg(initialIndex)), ZERO)
    [by cite theCountIsNegative]
  @given-it-were-zero |
    assume theSignedDoubleCount(neg(initialIndex)) = ZERO {
      @it-is-zero |
        theSignedDoubleCount(neg(initialIndex)) = ZERO
        [by hypothesis given-it-were-zero]
      @zero-is-below-zero |
        less_than(ZERO, ZERO)
        [by rewrite it-is-zero the-count-is-negative]
      @nothing-is-below-itself |
        not less_than(ZERO, ZERO)
        [using specialize integer.lessThanIrreflexive(ZERO)]
    }
  @conclusion |
    theSignedDoubleCount(neg(initialIndex)) != ZERO
    [by not_intro given-it-were-zero zero-is-below-zero nothing-is-below-itself]
qed

// LEMMA 3.6 CANNOT BE PROVED IN THIS CHAIN, and that is the whole point of the wrong/right
// split. [9, Thm 2.3] requires a ZERO signed double count; here the count is provably
// NEGATIVE (`theCountIsNegative`), hence nonzero (`theCountIsNotZero`), so the hypothesis is
// unavailable and §3.4's insertion delivers nothing.
//
// Left as an UNCITED hole deliberately: strict `2b4m check` then FAILS and names this step,
// with the blast radius up to Theorem 1.1. Writing the discharge anyway gives
//
//   error: step claims 'theSignedDoubleCount(neg(initialIndex)) = ZERO'
//          but the theorem derives '... = add(initialIndex, initialIndex)'
//
// which is the withdrawal notice's I_new = I(f1) - m = -2m != 0.
hole anEmbeddedSpinLagrangianExists: anEmbeddedLagrangianExists()
```
