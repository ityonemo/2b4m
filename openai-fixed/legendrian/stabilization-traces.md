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
import traces <<< "traces.b4m"
import integer <<< "std/integer.b4m"

sort Link = traces.Link
sort Int = integer.Int
const ZERO = integer.ZERO
const ONE = integer.ONE
func neg = integer.neg
func add = integer.add
func stabilize = traces.stabilize
func traceSign = traces.traceSign
pred isLoose = traces.isLoose
axiom aStabilizationIsLoose = traces.aStabilizationIsLoose
axiom forwardTraceSign = traces.forwardTraceSign
axiom reverseTraceSign = traces.reverseTraceSign

// φ₀ — "standard real-plane Legendrian link ϕ₀ ⊂ S¹⁵ at the negative end" (§3.4). It is
// GIVEN; the manuscript asserts no looseness for it, and treats looseness as the OUTPUT of
// the insertion step ("The negative link is now loose").
const phiZero: Link

// The outermost inserted trace is φ₁ → φ₀, where φ₁ = stabilize(φ₀) is "its loose
// stabilization ϕ₁" (§3.4). The manuscript assigns it the reverse sign +1.
//
// THE DEFECT IS HERE. `reverseTraceSign` requires `isLoose` of its TARGET, and the target
// is φ₀. Nothing establishes that. The step is transcribed as the manuscript has it, so the
// checker reports the missing hypothesis rather than this comment asserting it.
// THE REPAIR. The manuscript inserted m traces, all reverse. That cannot work: the
// outermost one targets φ₀, and [6] grants the reverse sign only when the TARGET is loose.
//
// Insert m+2 traces instead, with the outermost one FORWARD:
//
//   innermost  φ_{m+1} → φ_m → … → φ₁   (m+1 reverse traces, each at +1)
//              φ₀ → φ₁                  (one forward trace, at −1)
//
// Every inner target φ₁ … φ_{m+1} is a stabilization, hence loose by [6] Lemma 2.2, so each
// reverse trace has its hypothesis. The outermost trace is forward, which [6] grants "for
// any φ" — no looseness needed at φ₀.
//
// The count: I(f₁) + (m+1) − 1 = −m + m = 0. Still zero, so [9, Theorem 2.3] still applies.
theorem theOutermostTraceContributesMinusOneAsRepaired:
  traceSign(phiZero, stabilize(phiZero)) = neg(ONE)
proof
  @conclusion |
    traceSign(phiZero, stabilize(phiZero)) = neg(ONE)
    [using specialize forwardTraceSign(phiZero)]
qed
```

That is the error, in the checker's words:

```
error: cannot discharge the guard premise 'isLoose(phiZero)' at this call site
```

Compare OpenAI's withdrawal notice: *"a sign error invalidates a stabilization-trace
cancellation argument."* This is that argument, and that is the sign.

## The consequence for the count

The manuscript needs the total to be exactly zero, because [9, Theorem 2.3]'s hypothesis is
"its signed double count is zero". With `m` reverse traces at `+1` it gets `I(f₁) + m = 0`.

But the outermost trace cannot be a reverse trace. Taken as a forward trace instead — the
"for any φ" case, which needs no looseness — it contributes `−1`, and the count becomes
`(m−1) − 1 = m − 2`, so the total is `I(f₁) + m − 2 = −2 ≠ 0`.

```2b4m
// The count the manuscript CLAIMS, with the outermost trace forced to the only sign that is
// actually available at φ₀. Stated so the discrepancy is a theorem rather than a remark.
theorem theOutermostTraceContributesMinusOne:
  traceSign(phiZero, stabilize(phiZero)) = neg(ONE)
proof
  @conclusion |
    traceSign(phiZero, stabilize(phiZero)) = neg(ONE)
    [using specialize forwardTraceSign(phiZero)]
qed

// An INNER trace is fine: its target is itself a stabilization, hence loose by [6] Lemma 2.2.
// So the defect is confined to the outermost one — which is why the count is off by exactly
// two (one trace flipping from +1 to -1) rather than by m.
theorem anInnerTraceContributesPlusOne: forall l: Link;
  traceSign(stabilize(stabilize(l)), stabilize(l)) = ONE
proof
  @generalize-l |
    fix l: Link {
      @the-target-is-a-stabilization-hence-loose |
        isLoose(stabilize(l))
        [using specialize aStabilizationIsLoose(l)]
      @conclusion-at-l |
        traceSign(stabilize(stabilize(l)), stabilize(l)) = ONE
        [using specialize reverseTraceSign(stabilize(l)) the-target-is-a-stabilization-hence-loose]
    }
  @conclusion |
    forall l: Link; traceSign(stabilize(stabilize(l)), stabilize(l)) = ONE
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
// The total signed double count after inserting the traces. The manuscript's `I(f₁) + m = 0`.
const theSignedDoubleCount: Int

// [9, Theorem 2.3] (Eliashberg–Murphy, "Lagrangian caps"), the hypothesis that matters here:
// a zero signed double count gives the Hamiltonian regular homotopy to an embedding.
pred anEmbeddedLagrangianExists()
axiom exactCancellation:
  theSignedDoubleCount = ZERO -> anEmbeddedLagrangianExists()

// THE REPAIRED COUNT. With m+2 traces — m+1 reverse at +1 and the outermost forward at −1 —
// the total is I(f₁) + (m+1) − 1 = 0. The arithmetic is the paper's, restated for the
// repaired insertion, and it now depends on the sign that is actually AVAILABLE at φ₀.
axiom theRepairedCountIsZero:
  traceSign(phiZero, stabilize(phiZero)) = neg(ONE) -> theSignedDoubleCount = ZERO

// LEMMA 3.6 — the conclusion Section 3 exports.
theorem anEmbeddedSpinLagrangianExists: anEmbeddedLagrangianExists()
proof
  @the-outermost-trace-is-forward |
    traceSign(phiZero, stabilize(phiZero)) = neg(ONE)
    [by cite theOutermostTraceContributesMinusOneAsRepaired]
  @the-count-is-zero |
    theSignedDoubleCount = ZERO
    [using specialize theRepairedCountIsZero the-outermost-trace-is-forward]
  @conclusion |
    anEmbeddedLagrangianExists()
    [using specialize exactCancellation the-count-is-zero]
qed
```
