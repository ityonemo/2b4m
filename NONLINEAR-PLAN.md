# Nonlinear arithmetic — what is built, and what is deliberately not

## What "nonlinear arithmetic" actually bundles

The request "support nonlinear arithmetic" covers several capabilities of very
different difficulty. Naming them apart is the whole point, because one of them is
provably impossible and the rest are not.

| Capability | Difficulty | Accelerated? | Status |
|---|---|---|---|
| Nonlinear **identities** (`(k+1)² = k²+2k+1`) | low — a canonicalizing tactic | **no** (kernel-checked rewrites) | **LANDED** |
| Euclidean `div` / `mod` | low–medium — axiomatize + reuse Cooper | mostly no | **LANDED** |
| Polynomial **equality entailment** (Gröbner) | medium | no (reduction is a certificate) | deferred |
| Nonlinear **inequalities** (SOS / Positivstellensatz) | hard, incomplete | yes (disclosed) | deferred |
| **Full** nonlinear decision | **impossible** (Matiyasevich) | n/a | not a goal |

Two facts shape all of it:

- **Nonlinear integer arithmetic is undecidable** (Hilbert's 10th / MRDP). There can
  be no complete decision procedure, unlike Cooper's algorithm for the linear
  fragment. So the goal is *useful incomplete fragments*, disclosed honestly where
  they fall back.
- **Polynomial normalization is equational rewriting** — commutativity, associativity
  and distributivity are all proven `std/peano.b4m` theorems, so the identity tactic
  needs no trusted step at all.

## What landed

**`polynomial` / `polynomial_quantified`** canonicalize both sides to a sorted sum of
sorted monomials (distribute, right-nest and bubble-sort each monomial, sort the outer
sum, fold identity/absorbing factors) and emit a kernel-checked join. Both sides reach
the same canonical form iff the expansions are equal; otherwise a located
`polynomial: sides expand differently: '<nf(s)>' vs '<nf(t)>'`. It is
theory-parameterized like `arithmetic` (`polynomial(peano)`), not resolved by
well-known name in local scope. Elaborated by construction — there is no accelerated
step and nothing to disclose.

`mulLeftSwap` (the monomial sorting primitive) landed with it and retroactively
unblocked `ac`'s mul mode.

**Euclidean division** is `std/peano/divides.b4m` — declarations plus two axioms, not a
new solver:

```
func div(a: Nat, b: Nat) => Nat requires b != ZERO
func mod(a: Nat, b: Nat) => Nat requires b != ZERO
axiom divModProperty: forall b, a: Nat; b != ZERO -> add(mul(b, div(a, b)), mod(a, b)) = a
axiom modBound:       forall b, a: Nat; b != ZERO -> less_than(mod(a, b), b)
```

The guards are ordinary obligations. Reasoning about `div`/`mod` then reduces to linear
arithmetic plus the two defining facts, and Cooper's algorithm in `src/presburger.zig`
already decides divisibility atoms, so `arithmetic` largely handles `div`/`mod` goals.
(The plan named a new `std/division.b4m`; it went into the existing divides theory
instead, re-exported from `std/peano.b4m`.)

## HONEST LIMITS of the identity tactic

Worth keeping because each one is a located error rather than a wrong answer:

- **Identities only** (`=`), not inequalities.
- **Whole-number coefficients only.**
- **No cancellation.** `x·a = x·b ⊢ a = b` is not an identity; that stays with
  `arithmetic` / `mulCancel`.
- **A subtraction-like or division-like shape is out of fragment** → located error, not
  a false countermodel.
- **`succ` is kept OPAQUE**, a deliberate non-privileging decision. This is why the
  Gauss `target` payoff was deferred — it needs `succ`-expansion. √2's algebra is pure
  `add`/`mul`/`ONE` and needs none.

## Explicitly deferred / out of scope

- **Nonlinear inequalities** (SOS, Positivstellensatz): incomplete, so it would be a
  *disclosed accelerated tactic*. Real but a separate, later decision.
- **Gröbner-basis equality entailment** — proving an equation *from* other nonlinear
  equations rather than as an identity. Medium effort, certificate-producing (the
  reduction chain), worth it once a concrete need appears.
- **Full nonlinear decision**: impossible. Not a goal; the disclosure machinery keeps
  every incomplete fallback honest.
