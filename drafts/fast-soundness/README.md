# `--fast` must never admit what strict REFUTES

The invariant: if the strict path says a goal is FALSE (not merely "valid but I cannot build a
certificate"), `--fast` must say so too. Each probe here is a goal strict refutes; `--fast`
must reject every one.

Checked 2026-10-26 across all 17 trustable words (`Verify.Word`):

| word | probe | `--fast` |
|---|---|---|
| `arithmetic` (+`_quantified`) | `tests/cases/tactics/arithmetic/arithmetic_false_fast.b4m` | rejects |
| `simplify` (+`_quantified`) | `tests/cases/tactics/simplify/simplify_false_fast.b4m` | rejects |
| `polynomial` (+`_quantified`) | `tests/cases/tactics/polynomial/polynomial_false_fast.b4m` | rejects |
| `tautology` | `tests/cases/tactics/tautology/tautology_false_fast.b4m` | rejects |
| `chain` | `tests/cases/tactics/chain/chain_false_fast.b4m` | rejects |
| `assoc` (+`_quantified`) | `w-assoc.b4m` | rejects |
| `assoc_commut` (+`_quantified`) | `w-assoc-commut.b4m` | rejects |
| `extensionality` (+`_quantified`) | `w-extensionality.b4m` | rejects (fixed 2026-10-26) |
| `model` | `w-model.b4m` | rejects (α-match runs in admit mode) |
| `import` | `w-import.b4m` | rejects (α-match runs in admit mode) |
| `specialize` | `w-specialize.b4m` | rejects (the claim is α-matched against the instance in `decide`) |

`instantiation` is not trustable at all, so it has no `--fast` behaviour to check.

## The `specialize` case

`[using specialize succInjective(ZERO, ZERO)]` claiming `succ(ZERO) = ZERO` is rejected in
both modes. Strict checks the claim against the instance's conclusion only after the instance
is proven (`withGuardPremises`), which `--fast` skips, so `Specialize.decide` does the check on
the head's STATEMENT: it opens one ∀ per arg at the ELABORATED argument and α-matches a suffix
of the resulting `->` chain against the goal. It cannot be done in param space — the consequent
of `forall a, b; a = b` is literally `p1 = p2`, which matches any equation goal — which is why
the args are elaborated first, in the caller's scope with the head's free eigenvars bound.

Gated by `tests/cases/tactics/specialize/specialize_claim_mismatch_fast.b4m` (identical
diagnostic in both modes) and `specialize_claim_unrelated_bad.b4m` (antecedent-free shape).
