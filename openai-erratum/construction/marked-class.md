# Proposition 12.3, assumed

The output of Sections 2 through 11 of the withdrawn manuscript, stated as a single
existential and assumed.

## What it says

> **Proposition 12.3.** For this choice of `M`, there is a period `Π ∉ E` and a
> codimension-four integral subvariety `Z ⊂ A_Π` such that
> `[Z] = aθ⁴ + w`, `a ∈ ℚ`, `0 ≠ w ∈ W_K`.

## Why it is quarantined here

Its dependency chain is the entire construction:

    Prop 12.3  <-  Prop 11.4  <-  Prop 11.3  <-  Prop 10.7
               <-  Sections 8-10 (theta section ring, mirror symmetry)
               <-  Sections 4-7  (weighted Floer module, sign bookkeeping)
               <-  Section 3     (the Lagrangian L)
               <-  §3.4          (stabilization traces of [6])  <-- THE ERROR IS HERE

`openai-erratum/signs.md` checks the sign identities of Section 6 and finds them valid; the
withdrawal points instead at §3.4's traces, whose *internal* arithmetic is also consistent
(`φ → φ₁ : −1`, `φ₁ → φ : +1` at k = 4) but which depends on the convention imported from
reference [6]. A formalization that axiomatizes this proposition cannot see any of that.

So: assumed, labelled, and imported by `architecture.md` under a name that says what it is.

```2b4m
sort Period
sort CycleClass

pred inParameterSet(p: Period)
pred avoidsExceptional(p: Period)
pred isAlgebraic(p: Period, z: CycleClass)
pred inWeilPlane(p: Period, z: CycleClass)
pred isZeroClass(z: CycleClass)
const polarizationPower: CycleClass
func scale(q: CycleClass, z: CycleClass) => CycleClass
func add(z: CycleClass, w: CycleClass) => CycleClass

// PROPOSITION 12.3 — ASSUMED. Not a well-known result: the paper's own Sections 2-11, which
// transitively include the invalidated stabilization-trace argument of §3.4.
axiom aMarkedAlgebraicClassExistsAtSomeGoodPeriod: exists p: Period;
  inParameterSet(p) and avoidsExceptional(p) and
  (exists a: CycleClass; exists w: CycleClass;
  inWeilPlane(p, w) and (not isZeroClass(w)) and
  isAlgebraic(p, add(scale(a, polarizationPower), w)))
```
