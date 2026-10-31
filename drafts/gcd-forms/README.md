# `gcd(a,b)` versus `isGcd(d,a,b)` — where each form earns its place

A scan, not a change. Recorded for future work.

## The situation is already split, and nobody decided it

Both forms ship today:

| form | where | shape |
|---|---|---|
| `func gcd(a, b) => Int` | `std/integer/divides.b4m:4042` | **total**, Euclidean recursion |
| `func gcd(a, b) => Nat` | `std/peano/divides.b4m:661` | same, over ℕ |
| `define isGcd(d, a, b)` | `std/integer/lattice.b4m:65` | relational, four clauses |
| `pred isFamilyGcd(d, s, k)` | `std/integer/family-gcd.b4m` | relational, indexed |

Consumers are split too: `std/group/generated.b4m` aliases the **function**;
`std/integer/lattice.b4m` uses the **relation** throughout.

**The sharpest evidence that this was never settled:** `lattice.b4m` imports
`std/integer/divides.b4m` and aliases `lcm` from it as a concrete function
(`lattice.b4m:32`) while declining to alias `gcd` from the same file — relational gcd
beside functional lcm, in one file, for the lattice of *both*. There is also **no bridge
theorem** anywhere connecting `gcd(a,b)` to `isGcd(d,a,b)`.

## The total `gcd` is not a no-totalizing violation

Worth settling, because it looks like one. `gcdZero: gcd(a, ZERO) = a` asserts
`gcd(0,0) = 0`, and asserted values at junk inputs are exactly the violation
`drafts/no-totalizing-ops/README.md` names (ℕ `sub`'s `subZeroLeft`).

But `gcd(0,0) = 0` is **total-and-correct**, not junk, under either standard reading:

- as the nonnegative generator of the ideal $(a,b)$ — the ideal $(0,0)$ is $\{0\}$;
- as the top of the divisibility preorder — every $n \mid 0$, so $0$ is the greatest
  common divisor of nothing but itself.

`lattice.b4m` frames gcd/lcm as a **lattice**, which is precisely the reading that makes
$0$ the correct top. So the existing function is fine, and a proposal to add
"a total gcd with the $\gcd(0,0)=0$ convention" would duplicate what already ships.

## Where the function is better

**Counted: 72 sites in `lattice.b4m` thread an `isGcd` hypothesis.** The cost concentrates
in multi-gcd statements. The worst is `gcdOfGcdsDividesGcdWithGcd` (`lattice.b4m:970`),
which carries **five** relational hypotheses and eight universally quantified variables:

    forall N, m, n, d1, d2, g, e, B: Int;
      isGcd(d1, N, m) -> isGcd(d2, N, n) -> isGcd(g, m, n) ->
      isGcd(e, d1, d2) -> isGcd(B, N, g) -> divides(e, B)

As terms that is one line with no hypotheses at all:

    forall N, m, n: Int;
      divides(gcd(gcd(N,m), gcd(N,n)), gcd(N, lcm(m,n)))

So: **a function is better wherever gcds NEST or several appear in one statement.** Every
nested gcd under the relation needs its own variable, its own hypothesis, and its own
existence step at the call site — and the statement stops resembling the mathematics.

## Where the relation is better

Three places, and they are real:

1. **No sign commitment.** `lattice.b4m:15-17` says the existential form is chosen "so no
   sign facts about the concrete `gcd` function are needed". A relation states
   `less_than(ZERO, d)` as a clause; a function inherits whatever `gcdAbs` and the
   Euclidean recursion settle, and those have to be proved before use.
2. **Bézout.** `gcdIsLinearCombination` is naturally relational — it says *a* gcd is a
   linear combination, which is a property of any gcd, not of a chosen representative.
3. **Guarded existence.** `gcdExists` is guarded on both arguments nonzero. That guard is
   the honest statement, and `family-gcd.b4m` depends on it: the indexed recursion gets its
   existence at each step from `gcdExists`, which is why the family gcd needs no total
   function and no invented $\gcd(0,0)$.

## Recommendation, for when this is picked up

Keep both, and **add the missing bridge** rather than choosing:

    theorem theConcreteGcdIsAGcd: forall a, b: Int;
      a != ZERO -> b != ZERO -> isGcd(gcd(a, b), a, b)

One theorem buys the rest: relational consumers keep their guards and their sign-freedom,
and any statement with nested or repeated gcds can be stated over terms and discharged
through the bridge. It also removes the current oddity of `lattice.b4m` using a functional
`lcm` beside a relational `gcd`.

**Do not migrate `family-gcd.b4m` to the function.** Its whole point is that the indexed
recursion avoids needing a total combine; routing it through `gcd` would reintroduce
exactly the dependency the no-totalizing rule closed off.
