# A substituting tactic re-owes a guard that a step in scope has proved

**Status: OPEN.**

## The symptom

A `simplify`, `chain` or `specialize` step fails with

```
error: unproved obligation: 'ok(s)'
```

even though a step *earlier in the same block* proved exactly that. The guard is in scope;
each cited premise checks on its own; the failure appears only once the tactic has to build
an intermediate term containing the guarded application.

## Scope: three words of eight

| word | verdict | why |
|---|---|---|
| `simplify` | **RED** | rewrites INSIDE the guarded application |
| `chain` | **RED** | joins two equations THROUGH it |
| `specialize` | **RED** | instantiates a binder UNDER it |
| `assoc` / `assoc_commut` | green | reorder, never rebuild |
| `polynomial` / `arithmetic` | green | the guarded application is an opaque atom |
| `extensionality` | green | reduces to a pointwise residue |

**The dividing line is SUBSTITUTION.** A word that treats a guarded application as an opaque
atom passes; a word that substitutes into it reconstructs the application and re-raises its
guard. `tautology` sees every non-propositional subformula as opaque and so cannot
manufacture a guarded term. `model`/`import` are engine words, not term builders, and
discharge guards through `withGuardPremises`.

## Why it happens

The obligation DOES reach `Elab.requireKnown` — but in the synthetic's own ProveTask, where
`e.known = null` is set deliberately: a synthetic schema is registered globally and
instantiated by name, so it must not depend on one call site's context.

So the guard is never missing. It is raised in the synthetic's space, where by design
nothing can answer it, instead of being carried out to the call site as an antecedent.

## The target behaviour

An accelerant relativizes its own generated statement to `guard(...) -> <statement>` and
emits the invocation so the guard is discharged at the call site by citing a step in scope.

The machinery exists and is already uniform: `Builder.termExpr` records every delaborated
term in `Synthetic.seen`, `syntheticObligations` reads what those terms owe,
`wrapObligations` prepends them as antecedents, `withGuardPremises` discharges them at the
call site, and the single call site `demandUsing` covers every accelerant. So the gap is
narrower than "some words have the mechanism and some do not".

**A fix must preserve `e.known = null` in `syntheticObligations`** — for the reason above.
The obligation has to remain an ANTECEDENT of the synthetic, discharged where the caller's
context is legitimately available.

**The constraint on any fix:** the only thing an accelerant may go digging for is a GUARD.
Logical inputs stay named in the citation — a guard has one possible answer, so searching
for it cannot change what the proof proves, while a tactic silently choosing a premise
could. The rule governs the ENGINE, not the author; manual rummaging while writing a proof
is fine. (`design/acceleration.md`, "Inputs are named; guard obligations are searched for".)

## Fixtures

`drafts/accelerant-generated-guard/` — one ~80-line ground proof per affected word,
differing only in the final justification; its README records what each suppresses.
`drafts/accelerant-guard-discharge/specialize-refined-arg.b4m` — 30 lines, the `specialize`
case at a refined binder. Both still fail.

**The trap that costs the most time:** an axiom written `forall f: Fn; inv(inv(f)) = f` is
genuinely ILL-FORMED — it asserts something about `inv(f)` where `inv(f)` may be undefined —
and its error is reported against the CITING step, looking exactly like this defect. Check
the cited statement's own well-formedness before believing a fixture.

## Author-side workarounds

- substitute the equations one at a time with `[by rewrite …]` instead of one
  `simplify`/`chain`. A one-ref `[by rewrite EQ]` handles congruence, so this costs fewer
  steps than it used to;
- for a `specialize` at a REFINED binder, `[by cite …]` then `[by apply_at(t) …]`.

Cost: a 1-line tactic call becomes 2–6 steps, at every site whose intermediate terms mention
a guarded application.

## Why this matters

De-totalization makes guarded functions normal rather than exceptional. Any proof that
substitutes over terms built from `sub`, `div`, `mod`, `recip` or `inverse` can hit this, and
the error points at the tactic rather than the cause — so the natural response, *"but I
proved that two steps ago"*, is correct and unhelpful.

**Not to be confused with** the authoring rule that a guard in a DISCHARGED CONCLUSION must
come from the antecedent (the conclusion is elaborated in the PARENT block, outside the
`assume` whose hypothesis proves the guard). That one is working as designed and is recorded
in `.claude/rules/std-guide.md`. The discriminator: print the source offset — if it lands in
a `[by discharge]` step rather than the tactic's, it is the authoring rule.

## Related

- `NESTED-MODEL-COMPOSITION-ISSUE.md` — the sibling diagnostics problem: an incomplete model
  discharge also reports itself as a sort error in an unrelated file.
- `drafts/guard-relativization-bug/` — an earlier positional-matching fix in
  `withGuardPremises`.
