# `--fast` admits a `specialize` whose claim does not match its instance

**Status: OPEN. Fix immediately after the documentation run.**

This is the one place `--fast` admits a goal that is plainly FALSE. Every other trustable
word either runs its decision or α-matches the cited statement; `specialize` checks only
that a head is present.

## The repro

`tests/cases/tactics/specialize/specialize_claim_mismatch_fast.b4m`:

```2b4m
theorem bad: succ(ZERO) = ZERO
proof
  @conclusion |
    succ(ZERO) = ZERO
    [using specialize succInjective(ZERO, ZERO)]
qed
```

    $ 2b4m check --fast …/specialize_claim_mismatch_fast.b4m
    — NOT FULLY VERIFIED: 1 theorem(s) accelerated (admitted, not proved): specialize

    $ 2b4m check …/specialize_claim_mismatch_fast.b4m
    error: the claim does not match the instance's conclusion:
      claim:      succ(ZERO) = ZERO
      instance:   succ(ZERO) = succ(ZERO) -> ZERO = ZERO

`succ(ZERO) = ZERO` is false in ℕ. It is admitted, disclosed as accelerated, and enters the
fact pool where downstream proofs can cite it.

## Why it is there, and why the obvious fixes don't work

The claim-vs-instance match happens in `withGuardPremises`, **after** the instance is
proven — which is exactly the work `--fast` skips.

Two fixes that look right and are not:

- **Move the check into the producer.** The consequent is in PARAM space: `forall a, b; a = b`
  is literally `p1 = p2`. Matching that against the goal with the params as pattern variables
  succeeds for ANY equation goal. (Measured: `succ(ZERO) = ZERO` matches and is admitted.) A
  real check needs the ELABORATED ARGS, i.e. the instance.
- **Move admit past the ∀-peel.** Separately wrong — `fvar_binds` are installed after the
  producer returns.

So the fix has to get the instance's conclusion in target space without proving the instance.

## Contrast: the words that do check

Both verified by direct probe, so they are the shape to copy:

| word | behaviour under `--fast` |
|---|---|
| `import` | α-matches. A mismatched claim errors with `claim:` / `imported:` |
| `model` | α-matches. A mismatched claim errors with `claim:` / `transfer:` |

`specialize` differs only in that its statement needs instantiating first.

## Acceptance

- the repro above FAILS under `--fast`, with a located diagnostic naming both formulas;
- `tests/cases/tactics/specialize/*.b4m` still pass in both modes;
- `check std --library` and `check aata` unchanged in both modes.

## Related

- `design/acceleration.md` — the per-word trust table (the `specialize` row points here).
- `design/acceleration.md`, "Rules for `--fast` evaluation truncation" — the two cases where
  `--fast` is ALLOWED to outrun strict. This is not one of them.
