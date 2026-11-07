# A substituting tactic re-owes a guard that a step in scope has proved

**Status: FIXED for `simplify` and `chain`** (`Prove.syntheticObligations`). `specialize` at a
REFINED binder remains open — see "What remains" below.

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
| `simplify` | **FIXED** | rewrites INSIDE the guarded application |
| `chain` | **FIXED** | joins two equations THROUGH it |
| `specialize` | partly — see below | instantiates a binder UNDER it |
| `assoc` / `assoc_commut` | green | reorder, never rebuild |
| `polynomial` / `arithmetic` | green | the guarded application is an opaque atom |
| `extensionality` | green | reduces to a pointwise residue |

**The dividing line is SUBSTITUTION.** A word that treats a guarded application as an opaque
atom passes; a word that substitutes into it reconstructs the application and re-raises its
guard. `tautology` sees every non-propositional subformula as opaque and so cannot
manufacture a guarded term. `model`/`import` are engine words, not term builders, and
discharge guards through `withGuardPremises`.

## Why it happened (two defects, both in `syntheticObligations`)

The relativization machinery was right; the obligation SET handed to it was wrong.

1. **A real obligation was subtracted as "internal."** The filter dropped any obligation that
   appeared among the terms the producer had DELABORATED (`Builder.seen`). The intent was
   narrower — a premise the synthetic ASSUMES teaches its own and-tree, so it does not owe it
   — but `seen` holds every goal, premise and intermediate step formula alike. A
   `specialize invIsOk(s)` certificate delaborates `ok(s)` as a step of its own, so the
   `ok(s)` that `inv(s)` REQUIRES matched it and was never stated. Mentioning a proposition
   is not proving it. Fixed by tracking the assumed set explicitly: `Builder.assumeTerm`
   records each hypothesis into `Synthetic.assumed`, and only that set is subtracted.

2. **The antecedents were emitted in collection order.** `wrapObligations` nests them as
   `o0 -> o1 -> … -> goal`, and an antecedent is known only while what FOLLOWS it elaborates
   (`Elab`'s `local_known`). `collectObligations` returns post-order, which put the dependent
   guard first: `ok(inv(s)) -> ok(s) -> …`, whose leading antecedent names the guarded
   `inv(s)` and re-owes `ok(s)` where nothing is yet known. Fixed by ordering the obligations
   by dependency (an obligation's own obligations are over strict subterms, so no cycle), and
   by re-adding a subtracted obligation that a SURVIVOR still owes — otherwise the survivor
   sits ahead of the body antecedent that would have taught it.

## The behaviour, as built

An accelerant relativizes its own generated statement to `guard(...) -> <statement>` and emits
the invocation so the guard is discharged at the call site by citing a step in scope. The
pipeline is uniform and unchanged: `Builder.termExpr` records every delaborated term in
`Synthetic.seen`, `Builder.assumeTerm` records every hypothesis in `Synthetic.assumed`,
`syntheticObligations` reads what the seen terms owe MINUS what the assumed ones teach and
orders the remainder by dependency, `wrapObligations` states them as antecedents,
`withGuardPremises` discharges them at the call site — and `demandUsing` is the single call
site covering every accelerant.

`e.known = null` in `syntheticObligations` is preserved: a synthetic schema is registered
globally and instantiated by name, so it must not depend on one call site's context. The
obligation stays an ANTECEDENT, discharged where the caller's context legitimately is.

**The constraint on the engine:** the only thing an accelerant may go digging for is a GUARD.
Logical inputs stay named in the citation — a guard has one possible answer, so searching
for it cannot change what the proof proves, while a tactic silently choosing a premise
could. The rule governs the ENGINE, not the author; manual rummaging while writing a proof
is fine. (`design/acceleration.md`, "Inputs are named; guard obligations are searched for".)

## What remains

`specialize` at a REFINED binder (`drafts/accelerant-guard-discharge/specialize-refined-arg.b4m`)
no longer reports a spurious `unproved obligation`; it now reports the honest

    cannot discharge the guard premise 'invertible(inverse(f))' at this call site

The synthetic correctly states what it needs, and the call site genuinely cannot answer it:
`invertible(inverse(f))` would follow from the involution lemma being cited, which is the
lemma being applied. Whether a specialize at a refined binder should instead relativize over
the binder's own guard is a design question, not this defect.

The third original fixture (`specialize-guard-in-scope`, now deleted) was MIS-WRITTEN: its
claim was `… = swap(c, c)`, but `theClosedForm(s, a, b)` yields
`… = swap(at(inv(s), a), at(inv(s), b))`, with no step rewriting the images. The README claims
the three files differ "only in the final justification"; that is not true of this one, and its
`the claim does not match the instance's conclusion` is correct behaviour.

## Fixtures

`tests/cases/tactics/guard/{simplify,chain}_generated_guard.b4m` — the two fixed words, now
regression gates in `zig build test` (strict only: `--fast` emits no certificate, so it never
builds the terms that owe these).

`drafts/accelerant-guard-discharge/specialize-refined-arg.b4m` — the remaining specialize case.

**The trap that costs the most time:** an axiom written `forall f: Fn; inv(inv(f)) = f` is
genuinely ILL-FORMED — it asserts something about `inv(f)` where `inv(f)` may be undefined —
and its error is reported against the CITING step, looking exactly like this defect. Check
the cited statement's own well-formedness before believing a fixture.

## Author-side workaround (still needed for `specialize` only)

For a `specialize` at a REFINED binder, `[by cite …]` then `[by apply_at(t) …]`.

`simplify` and `chain` need no workaround now; the one-at-a-time `[by rewrite …]` expansion
that used to be required can be collapsed back into a single tactic call.

## Why this mattered

De-totalization makes guarded functions normal rather than exceptional. Any proof that
substitutes over terms built from `sub`, `div`, `mod`, `recip` or `inverse` could hit this, and
the error pointed at the tactic rather than the cause — so the natural response, *"but I
proved that two steps ago"*, was correct and unhelpful.

**Not to be confused with** the authoring rule that a guard in a DISCHARGED CONCLUSION must
come from the antecedent (the conclusion is elaborated in the PARENT block, outside the
`assume` whose hypothesis proves the guard). That one is working as designed and is recorded
in `.claude/rules/std-guide.md`. The discriminator: print the source offset — if it lands in
a `[by discharge]` step rather than the tactic's, it is the authoring rule.

## Related

- `NESTED-MODEL-COMPOSITION-ISSUE.md` — the sibling diagnostics problem: an incomplete model
  discharge also reports itself as a sort error in an unrelated file.
- `tests/cases/model/guarded/model_guarded_local_head_specialize.b4m` — the gate for an
  earlier positional-matching fix in `withGuardPremises`.
