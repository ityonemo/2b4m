# A guarded model transfers nothing: `apply_at` loses the relativization

**Found 2026-10-30, while completing AATA ch17.** Reproducible, upstream of everything that
wants it, and latent for months because no file in the corpus transfers through the affected
model.

## The repro

```2b4m
import rational <<< "std/rational.b4m"
import integer <<< "std/integer.b4m"

sort Q = rational.Q
pred isInteger = rational.isInteger

theorem probeBaseTransfer: forall a, b: Q;
  isInteger(a) -> isInteger(b) -> rational.add(a, b) = rational.add(b, a)
proof
  @conclusion |
    forall a, b: Q;
      isInteger(a) -> isInteger(b) -> rational.add(a, b) = rational.add(b, a)
    [using model(rational.IntegersInRational) integer.addIsCommutative]
qed
```

Strict `check`:

```
std/integer.b4m:200:16: error: IntegersInRational@negNegNonneg: step claims
  'neg(prev(neg(k))) = succ(neg(neg(k)))' but apply_at derives
  'isInteger(neg(k)) -> neg(prev(neg(k))) = succ(neg(neg(k)))'
```

`--fast` PASSES it — `model` keeps the statement α-match and drops the per-axiom obligation
coverage, so the whole failure is strict-only. (Consistent with the documented boundary, but
it means the mode you iterate in cannot see this at all.)

## The site

`std/integer.b4m:196-202`, inside `negNegNonneg`:

```2b4m
@inner-negation-over-prev |
  neg(prev(neg(k))) = succ(neg(neg(k)))
  [by apply_at(neg(k)) negation-over-prev-rule]
```

`negation-over-prev-rule` is a `forall x: Int; …`. Under the guarded model its `Int` binder
relativizes to `isInteger(x) -> …`, so `apply_at(neg(k))` correctly produces
`isInteger(neg(k)) -> neg(prev(neg(k))) = succ(…)`. But the step's CLAIM — the author's
written formula — was relativized too, and then *not*: it stayed the bare equation.

So the two sides disagree by exactly one guard antecedent. Either the claim should carry the
same `isInteger(neg(k)) ->` (and the discharge happen at the next step), or `apply_at` should
discharge the guard itself from scope the way a direct `requireKnown` call does — `neg(k)` IS
in the cut here, `isIntegerNeg` gives it immediately.

**The second is almost certainly the intended behaviour**, since nothing in `std/integer.b4m`
was written with guards in mind and every other guard obligation in the corpus is *found*, not
threaded through claims. That matches the standing rule: guard obligations are discharged from
scope, never named.

## Why it was never noticed

`grep -rn IntegersInRational` finds exactly one consumer outside `std/rational.b4m` itself,
and it is in `scratch-needswork/`. The model has been declared, documented at length, and
never once used to transfer a theorem. `check std --library` is green because a model block
with no transfer through it is never exercised — the obligations are checked per *transfer*,
not at the declaration.

**That is the real lesson, and it generalizes past this bug:** a `model` block is dead code
until something cites it. The corpus has at least one more (`NaturalsInRational`) in the same
position; worth sweeping for others and adding one transfer theorem each, the way
`std/<ns>/examples.b4m` exists to exercise axioms. A model with no consumer should probably
fail `--library` for the same reason an unused axiom does.

## What it blocks

- **AATA Gauss's Lemma, the `d = 1` branch.** Needs `dividesOneImpliesUnit` on the cut
  (`c a_m b_n = 1` forces `c = ±1`); that proof is a sign argument, so it needs ℤ's ORDER on
  the cut, which needs a working guarded transfer.
- **Corollary 17.14 (rational roots)** and **Theorem 17.15 (Eisenstein)**, both of which rest
  on Gauss's conclusion.
- `std/rational/integer-order.b4m` stops at the four discreteness facts for this reason; its
  header carries the same repro.

So three of chapter 17's remaining deferrals are one bug, not three pieces of missing
mathematics. The mathematics is done and committed (`40cccbd`).

## Fixing it

The guard machinery is `paramGuards` + `requireKnown`; `painted-accelerant-guard-fix` is the
precedent (abstracted params losing guards, and `model` applying to TERMS not NAMES). Attribute
with a `std.debug.print` at `refForKnown` rather than by reading code — that is what worked
last time, and four wrong seams were ruled out that way.
