# `--fast` must never admit what strict REFUTES

The invariant: if the strict path says a goal is FALSE (not merely "valid but I cannot build a
certificate"), `--fast` must say so too. Each probe here is a goal strict refutes; `--fast`
must reject every one.

Checked 2026-10-26 across all 17 trustable words (`Verify.Word`):

| word | probe | `--fast` |
|---|---|---|
| `arithmetic` (+`_quantified`) | `tests/cases/arithmetic_false_fast.b4m` | rejects |
| `simplify` (+`_quantified`) | `tests/cases/simplify_false_fast.b4m` | rejects |
| `polynomial` (+`_quantified`) | `tests/cases/polynomial_false_fast.b4m` | rejects |
| `tautology` | `tests/cases/tautology_false_fast.b4m` | rejects |
| `chain` | `tests/cases/chain_false_fast.b4m` | rejects |
| `assoc` (+`_quantified`) | `w-assoc.b4m` | rejects |
| `assoc_commut` (+`_quantified`) | `w-assoc-commut.b4m` | rejects |
| `extensionality` (+`_quantified`) | `w-extensionality.b4m` | rejects (fixed 2026-10-26) |
| `model` | `w-model.b4m` | rejects (α-match runs in admit mode) |
| `import` | `w-import.b4m` | rejects (α-match runs in admit mode) |
| **`specialize`** | `w-specialize.b4m` | **ADMITS — the one known violation** |

`instantiation` is not trustable at all, so it has no `--fast` behaviour to check.

## The `specialize` violation

`[using specialize succInjective(ZERO, ZERO)]` claiming `succ(ZERO) = ZERO` passes `--fast`
and fails strict. Whether the instance's conclusion matches the claim is checked by
`withGuardPremises` AFTER the instance is proven, which `--fast` skips.

It cannot be checked in the producer: the consequent is in PARAM space — for
`forall a, b; a = b` it is literally `p1 = p2` — and the actual arguments are AST exprs that
only the instance pass elaborates. Matching the consequent against the goal with the params as
pattern variables therefore succeeds for ANY equation goal (measured: `succ(ZERO) = ZERO`
matched `p1 = p2`). A sound check needs the elaborated args, i.e. the instance itself.

Gated by `tests/cases/specialize_claim_mismatch_fast.b4m`, which pins today's wrong behaviour
so that a future fix is noticed rather than silently landing.
