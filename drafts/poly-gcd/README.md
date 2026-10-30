# Proposition 17.10 — what is proved, and the one thing that blocks the rest

`gcd.b4m` holds the work. It checks under `--draft` with exactly one hole,
`polyMulIsAssociative`.

## The split

Judson's proof has three parts. Two of them need no minimality and no new machinery:

| part | status |
|---|---|
| "a common divisor divides every combination" (his 2nd ¶ algebra) | proved, **but rests on associativity** |
| "a combination that divides both IS a gcd" (his 2nd ¶ conclusion) | proved, **rests on associativity** |
| "two gcds divide each other" (his 3rd ¶, uniqueness) | **proved, hole-free** |
| "let d be the monic polynomial of smallest degree in S" (his 1st ¶) | not encodable — see below |

`distributingOnTheRight` (F[x] distributes on the right, from the left form plus
commutativity) is also proved and hole-free; `std/field/polynomial.b4m` has only the left
form.

## The blocker: F[x] multiplicative associativity

His second paragraph computes

    d = r p + s q = r u d' + s v d' = d' [r u + s v]

and the last step needs `r(ud') = (ru)d'` — associativity of `mulP`, which
`std/field/polynomial.b4m` does not have. It is **Judson's own §17.1 exercise**, whose proof
reindexes a double sum into a sum over triples `j + k + l = i`.

`std/nested-sum.b4m` proves exactly that exchange, but **it cannot be instantiated here.**
Its `term` is a 2-argument func, while the family needed is

    term(j, k) = p_j * q_k * r_{(i-j)-k}

carrying four more parameters (`p`, `q`, `r`, `i`). Declaring the derived sums at the wider
arity and mapping them fails:

    'triUpTo' expects 5 argument(s), got 1

A model substitutes **names**, not partially applied terms, so a parameterized family cannot
be a model target. (Verified, not assumed — the model block itself type-checks and reports
*zero* theorems, which is the `indexed/examples.b4m` trap: the consistency conditions are
only exercised at an actual transfer.)

The identity itself is confirmed numerically: for `i = 0..5` over random coefficient
triples, `coeff((pq)r, i)`, `coeff(p(qr), i)`, the triangular sum and the shortened-rows sum
all agree — including with truncating `sub` nested as `(i-j)-k`.

**So the remaining route is to re-prove the exchange directly at the concrete family**, using
`std/nested-sum.b4m`'s proof as a template rather than a transfer: induct on the row count
with the bound fixed, increment by one anti-diagonal, regroup four atoms by `assoc_commut`.
That is four substantial inductions (the two exchange halves, plus "a factor not depending on
the summation index pulls out of a finite sum", twice), each with 6-deep binder towers
instead of 1. Bigger than Corollary 17.8 was.

## His first paragraph is separately out of reach

"Let `d(x)` be the monic polynomial of smallest degree in the set
`S = {f(x)p(x) + g(x)q(x)}`" needs a least element of a *set of polynomials* — the
comprehension-over-a-sort limit also recorded for §16.4 and used as a hypothesis in §17.3's
principal-ideal theorem. The same escape works here: take the minimal-degree combination as
a hypothesis rather than constructing it. That is what the proved theorems above do.
