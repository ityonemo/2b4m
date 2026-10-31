# Layering the algebra theories: pull the order out, compose models instead of restating

A design note, not a change. Three threads the user raised, with one root cause.

## The measurement

**44 restatements of the same 11 field axioms**, across four files:

| file | restated field axioms | own axioms | theorems |
|---|---|---|---|
| `std/field.b4m` | — (it *is* the 11) | 11 | 15 |
| `std/field/order.b4m` | **11 / 11** | 17 | 32 |
| `std/rational.b4m` | **11 / 11** | 17 | 30 |
| `std/real.b4m` | **11 / 11** | 40 | 41 |
| `std/complex.b4m` | **11 / 11** | 30 | 21 |

`std/field/order.b4m` declares `sort OrderedField`, restates all 11 of `field.b4m`'s axioms
over it, then runs `model FieldIsOrdered` to pull field's theorems back. Each concrete sort
below then restates the same 11 *again*.

## Thread 1 — pull out just the order parts

`std/order.b4m` **already exists** and already has the three order axioms
`std/field/order.b4m` restates: `lessThanTransitive`, `lessThanIrreflexive`, `trichotomy`
(its header calls them the obligations of a strict total order, which is the right framing —
trichotomy is what makes the order *total*, and `lessOrEqualTotal` /
`unequalAreComparable` / `notLessThanImpliesLessOrEqual` genuinely need it). It carries **12
derived theorems**.

`std/field/order.b4m` imports only `std/field.b4m`, not `std/order.b4m`. So it duplicates a
theory that exists, and its consumers inherit the duplication. Its three *genuinely new*
axioms are the ones coupling order to the arithmetic:

    lessThanAddRight     a < b -> a + c < b + c
    lessThanAddCancel    a + c < b + c -> a < b
    positiveProduct      0 < a -> 0 < b -> 0 < a·b

**Those three are the whole content of "ordered field" beyond field + order.** That is the
extraction: `field/order.b4m` keeps them, models `std/order.b4m` for the order half and
`std/field.b4m` for the algebra half, and restates neither theory's axioms.

## Thread 2 — one sort, several concurrent models

Already the established idiom, which is why this is low-risk:

- `std/rational.b4m` runs **four** (`RationalOrderedField`, `RationalField`,
  `IntegersInRational`, `NaturalsInRational`)
- `std/integer.b4m` runs **two** (`NonNegInt`, `IntegerRing`)

What nobody does yet is compose an **order** model with an **algebra** model on one sort —
every current pair is algebra+algebra or algebra+cut. That composition is what Thread 1
needs, and the existing four-model file is evidence the engine handles the multiplicity.

The one thing to verify before relying on it: that a proof can cite facts from *both* models
in the same step list without the accelerants getting confused about which model a bare name
resolves through. The shim idiom (`import`-vs-`model` are two axes) suggests transferred
facts need local names either way, so this probably costs one shim per shared operator.

## Thread 3 — an ordered ring

**There is no `std/ring/order.b4m`.** ℤ is exactly the sort that wants one: it is an ordered
ring, not an ordered field, and `std/integer/order.b4m` currently carries its order facts
locally. Same three coupling axioms as the field case (`lessThanAddRight`,
`lessThanAddCancel`, `positiveProduct`) — the field-ness is irrelevant to them.

So the clean shape is:

    std/order.b4m        strict total order            (exists, 12 theorems)
    std/ring.b4m         ring                          (exists)
    std/ring/order.b4m   + the 3 coupling axioms       (MISSING — ℤ's home)
    std/field.b4m        field                         (exists)
    std/field/order.b4m  + the same 3                  (exists, but restates everything)

with each concrete sort discharging an order model and an algebra model rather than
restating 11 + 3 axioms.

## Why this is queued, not done

It touches `rational.b4m`, `real.b4m`, `complex.b4m` and `integer/order.b4m` — the number
tower's foundations, all four of which just absorbed changes. It is also adjacent to the
**generic polynomial theory** the user raised (polynomials over ring / field / ℚ / ℝ): the
duplication there has the same cause — a theory that fixes its parameter by aliasing a
specific sort cannot be re-pointed, so each new coefficient domain restates the layer. Both
are the same refactor seen from two sides, and they should be designed together.

**Order of work, suggested:** Thread 1 first (smallest, and `std/order.b4m` already exists
to model), then Thread 3 (new file, no existing consumers to break), then the generic
polynomial theory with Thread 2's composition pattern settled by the first two.
