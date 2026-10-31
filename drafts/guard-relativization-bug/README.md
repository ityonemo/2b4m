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

---

## Update 2026-10-30: the first half is FIXED; the second is localized exactly

### Half one — missing nominations (fixed, `6478118`)

The original diagnosis above was incomplete. The first failure was not an engine bug at all:
`IntegersInRational` mapped every symbol but **nominated no membership discharger**. A guarded
model needs a ground fact per const and a closure per func, and the model had none, so
`emitDischargeStep` had nothing to find. Fixed by nominating all nine; `isIntegerSubClosed` was
the only fact that had to be written (`isIntegerSub` concludes `isInteger(add(a, neg(b)))`, but
`-|` matches on the *mapped func*, so `sub` needed its closure in terms of `sub`).

**Lesson: nominations are not optional decoration on a guarded model — without them it cannot
transfer anything.** Worth a `--library` check: a guarded model whose refined sort has
unnominated consts/funcs is inert, and nothing currently says so.

### Half two — `produceSpecialize`'s space mismatch (open, exactly localized)

With nominations in place the failure moves to `std/integer.b4m:407`:

```
IntegersInRational@negPreimageIsNegation: instantiate: expected premise
  'isInteger(succ(x))', got 'forall x: Q; isInteger(x) -> neg(x) = k -> neg(k) = x'
```

The seam, **measured** with a trace at the local-head site (not inferred):

```
LOCALHEAD model=0     src_universe=true   f=forall n: Int; nonneg(n) -> add(n, ZERO) = n
LOCALHEAD model=2484  src_universe=false  f=forall x: Q; isInteger(x) -> neg(x) = k -> neg(k) = x
```

`produceSpecialize` builds in SOURCE space (`Prove.zig:223`, "accelerants build in source space
and the instance adopts the model"). But a LOCAL head's formula comes from
`producerPremiseFormula` (`Prove.zig:1366`), which returns `low_steps[...]` — the **lowered,
relativized** formula — whenever `self.model != .universe`. So under a guarded model the head
arrives with `isInteger(x) ->` already injected, the antecedent walk at `Prove.zig:3403` reads
it as a hypothesis slot, and it gets paired with the user's next `specialize` ref.

A GLOBAL head does not have this problem: it goes through `citedFactFormula`, which is source
space. The asymmetry between the two branches of that `if (head_local)` IS the bug.

### Two fixes tried and reverted — don't repeat these

1. **Skip the guard in the antecedent walk** (`ai > 0 and isBinderGuard(...)`). Wrong place: a
   trace showed every antecedent reaching that walk is a genuine hypothesis (`add(p1,p2) = ZERO`
   etc.) because the walk runs in source space where guards do not exist yet.
2. **Strip the guards off the relativized local head** before the walk
   (`stripLocalHeadGuards`). Right shape — the expected premise became the correct source form
   `forall x: Q; neg(x) = k -> neg(k) = x` — but a local head is ALSO antecedent #0, matched at
   the call site against the actual step, which is still relativized. The mismatch only moved.

### What the fix probably is

Make the two branches agree on space. Either:

- give `producerPremiseFormula` a source-space twin for this call site (`source_formulas` is
  already maintained in parallel and is what the universe-model path returns), **and** ensure
  the call-site premise for antecedent #0 is taken in the same space; or
- keep the head relativized and teach the instance that antecedent #0's guards are guards —
  i.e. route them through the same `withGuardPremises` excess path the `∀`-binder guards use.

The first looks smaller and matches the stated architecture ("accelerants build in source
space"). The invariant to hold either way: **the schema instance's antecedent #0 and the step
supplied for it must be in the same space.**
