# Corollary 17.8 ("at most n distinct zeros") — what it actually reduces to

An earlier deferral note in `aata/17.2` said this "cannot currently be encoded" because
`std` had no counting over a field's carrier. **That was wrong** — see
`memory/counting-over-any-carrier.md`. These probes establish what the real obstacle is.

## What works (all strict-green)

| probe | result |
|---|---|
| `probe.b4m` | the five-line `std/sized.b4m` model over `F`; zeros reify as a `Set`; set membership IS being a zero; a pointwise containment of zero sets gives the size bound |
| `probe2.b4m` | the same reification with the **polynomial quantified** — `setFromPredicate` is plain comprehension, so no model is needed for it |
| `probe3.b4m` | `peano.induction` **accepts** the property `prop(k) := forall p, s; ... degreeAtMost(p,k) -> ... size <= k`, with `p` bound inside, so the polynomial may change between hypothesis and conclusion |
| `base.b4m` | the **base case, proved**: a nonzero polynomial of degree ≤ 0 has degree exactly 0, evaluates everywhere to its nonvanishing constant term, hence has no zeros, hence an empty zero set |
| `step.b4m` | the **induction step's logic, complete** — resting on exactly two holes, below |

Three successive predictions of mine about where this would break were all false
(counting unavailable; the subobject predicate must fix the polynomial as a `const`; the
induction cannot carry a quantified polynomial). Each took one probe to disprove.

## The actual obstacle: evaluation is not known to be multiplicative

`step.b4m` needs "any zero β ≠ α of (x−α)q is a zero of q". With `field.noZeroDivisors`
that follows immediately from two facts, and `std/field/polynomial.b4m` has neither:

```
hole evaluationPreservesMultiplication: forall p, q: Poly; forall b: F;
  evaluate(mulP(p, q), b) = mulF(evaluate(p, b), evaluate(q, b))

hole theLinearPolynomialEvaluates: forall al, b: F;
  evaluate(linear(al), b) = addF(b, negF(al))
```

The library proves evaluation **additive** (`evaluationPreservesAddition`) and the product
case **at the root only** (`theProductVanishesAtTheRoot`, `theRootOfTheLinearPolynomial`).
Everything stated about a product's evaluation is at `al`, never at a general point.

**And the multiplicative half is the 17.1 double-sum gap, reached from a new direction.**
`evalUpTo(mulP(p,q), b, n)` is a sum over `i` whose summand is `convolution(p,q,i,i)` —
itself a sum over `j`. Turning that into `(Σ p_j b^j)(Σ q_k b^k)` is exactly the
flattening of a nested pair of sums into a sum over pairs that `aata/17.1` records as
having no kernel route (the same obstruction that leaves multiplicative associativity of
`R[x]` unproved). So 17.8 is not blocked by counting, by the statement, or by the
induction — it is blocked by the one gap already on record.

`theLinearPolynomialEvaluates` is a corollary of it (`linear(al)` is a two-term
polynomial, so its own evaluation is finite), and would be cheap once the general lemma
lands.

## What this buys even unfinished

`base.b4m`'s two lemmas are new and self-contained:
`aNonzeroConstantHasDegreeZero` and `aNonzeroConstantHasNoZeros`, plus
`theZeroSetOfAConstantIsEmpty`. `step.b4m` adds `aVanishingDifferenceMeansEqual`
(`b − al = 0 → b = al` over a field, which `std/field.b4m` does not package).
