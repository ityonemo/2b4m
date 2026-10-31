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

## The polynomial half, now measured (2026-10-30 — all five layers exist)

The note above guessed that the polynomial duplication "has the same cause". With ℤ[x]
landed there are **five** polynomial layers and the guess can be replaced with a count.

| file | coefficient sort | own axioms | theorems | models |
|---|---|---|---|---|
| `std/ring/polynomial.b4m` | `R` (abstract commutative ring) | 18 | 19 | — (it IS the layer) |
| `std/field/polynomial.b4m` | `F` (abstract field) | 21 | 81 | `ring_poly` |
| `std/rational/polynomial.b4m` | ℚ | 8 | 6 | `fieldpoly` |
| `std/integer/mod-n-polynomial.b4m` | ℤ_n | 12 | 3 | `ring_poly` + `ring` |
| `std/integer/polynomial.b4m` | ℤ | 13 | 5 | `ring_poly` + `ring` |

**54 axioms below the abstract layer, and essentially all of them are the same equations.**

### What is identical across every layer

Line up ℤ_n[x]'s twelve against ℤ[x]'s thirteen and they are the same list with one letter
changed (`z` → `i`) — extensionality, the zero/one coefficients, `addP`/`negP`/`mulP`
coefficientwise, the two convolution clauses, `degreeAtMost`'s meaning, and the two degree
facts. ℚ[x] carries a six-axiom subset (it needs no `degree`, having `fieldpoly`'s). The
**only** thing that differs between any two of them is the *name of the coefficient sort
appearing in the equation*, e.g.

    axiom zZeroPolyCoeff: forall i: Nat; zcoeff(ZZEROP, i) = mod_n.ZERO
    axiom iZeroPolyCoeff: forall i: Nat; icoeff(IZEROP, i) = IZERO

Nothing else varies. Not the index sort (ℕ everywhere), not the convolution recursion, not
`degreeAtMost`'s characterization, not extensionality.

### What genuinely varies — and it is only two things

1. **The coefficient sort and its ring laws.** This is the real parameter, and it is what
   the `ring.*` / `ring_poly.*R` half of each model block supplies: seven ring axioms plus
   `mulOneLeft` and `mulIsCommutative`. These maps are *not* duplication — each one is a
   genuine discharge, pointing at a theorem the coefficient theory actually proved
   (`integer.mulIsAssociative`, `mod_n_domain.mulIsCommutativeInZn`).
2. **What is TRUE of that coefficient sort beyond being a commutative ring.** This is the
   only mathematically interesting axis, and it is small:
   - ℚ[x]: the coefficients have a *cut* (`dividesOnTheCut`, `coefficientsAreRelativelyPrimeUpTo`)
   - ℤ_n[x]: the coefficients form a *domain* at prime `N` (`modNPolynomialsHaveNoZeroDivisors`)
   - ℤ[x]: the coefficients map *into* ℤ_n (`reduce`, `reduceCoefficientwise`)
   - F[x]: the coefficients are *invertible* (division algorithm, monic, irreducible, …)

So the shape a generic polynomial theory has to hit is: **one layer parameterized by a
coefficient ring, with the coefficient sort as the ONLY thing a user supplies — and an
extension point for the four facts above.** The twelve coefficient equations should never
be written a sixth time.

### The specific thing blocking it, named

`std/ring/polynomial.b4m` *is already* parameterized in the sense that matters: it declares
`sort R` abstractly and all 19 theorems are about an arbitrary commutative ring. The problem
is **not** the abstraction, it is that **a `model` can only re-point a symbol onto a symbol
the target file already declares.** So the only way to use R[x] at a new coefficient sort is
to declare a fresh `Poly` sort locally, restate every coefficient equation over it, and map
them across — which is exactly what the four lower files do.

That is the same disease as Thread 1 above (a theory that fixes its parameter by aliasing a
specific sort cannot be re-pointed), but with a sharper diagnosis: here the theory does
*not* fix its parameter — it is genuinely generic — and the duplication is entirely in the
**instantiation mechanism**. There is no way to say "give me `ring_poly` at coefficient sort
`Int`" and have the sort and its twelve axioms come into being. Each instantiation mints
them by hand.

Two further findings from building the last two layers, both worth keeping:

- **A transfer must map every symbol the transferred PROOF mentions**, not merely the
  theorem's statement. `std/ring/polynomial.b4m` aliases `ring.Ring`, so a model onto a new
  coefficient sort must *also* map `std/ring.b4m`'s own seven axioms — and the error surfaces
  inside `std/ring.b4m`, far from the model block. Both ℤ_n[x] and ℤ[x] carry that second
  half, with a comment saying why.
- **Transfers chain.** A theorem that was itself proved by a model transfer re-checks that
  inner transfer when you transfer it again, demanding the inner layer too. This is why
  `polyMulIsCommutative` is *not* transferred into ℤ[x]: R[x] proves it through
  `tailConvolution` and `segment`, so carrying it would mean restating two more layers of
  recursion axioms for a fact Gauss does not need.

### Revised order of work

The polynomial case is now the **better** motivating example than the field case, because
its duplication is larger (54 axioms vs 44), purely mechanical (one letter differs), and has
no competing design question — nobody disputes what a polynomial over a ring is. Thread 1
still goes first on size, but the instantiation mechanism it needs is the same one, and the
polynomial layers are the cleaner test of whether it works.

## Why this is queued, not done

It touches `rational.b4m`, `real.b4m`, `complex.b4m` and `integer/order.b4m` — the number
tower's foundations, all four of which just absorbed changes. It is also adjacent to the
**generic polynomial theory** the user raised — measured in the section above, which
supersedes the guess that once stood here: the polynomial duplication is *not* a theory
fixing its parameter (R[x] is genuinely generic) but the **instantiation mechanism** having
no way to mint a sort and its axioms. Still the same refactor seen from two sides, and they
should be designed together.

**Order of work, suggested:** Thread 1 first (smallest, and `std/order.b4m` already exists
to model), then Thread 3 (new file, no existing consumers to break), then the generic
polynomial theory with Thread 2's composition pattern settled by the first two.
