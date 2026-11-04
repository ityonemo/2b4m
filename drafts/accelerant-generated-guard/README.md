# An accelerant re-owes a guard that a step in scope has proved

Three RED fixtures, one per affected `using` word. Each is the same 80-line ground proof
differing only in its final justification, and each fails with:

    78:12: error: unproved obligation: 'ok(s)'

`ok(s)` is proved by `@s-is-ok` at the top of the proof, and `ok(inv(s))` by
`@the-inverse-is-ok` right after it.

## Why these fixtures isolate the engine, and nothing else

Each of the following would otherwise fire in the same proof and has been deliberately
suppressed, because each is a SEPARATE and already-documented issue:

- **The proof is GROUND** — no `fix`, no `assume`, one block. So the DISCHARGED-CONCLUSION
  rule cannot be implicated (that one is resolved as NOT A BUG in
  `ACCELERANT-GUARD-DISCHARGE-ISSUE.md`: a guard in a conclusion elaborated in the parent
  block must come from the antecedent).
- **`theClosedForm` binds `f` at the REFINED sort `OkFn`**, so `inv(inv(f))` is defined at
  every instance and the statement owes nothing of its own. An axiom written
  `forall f: Fn; inv(inv(f)) = f` would be genuinely ill-formed, and the resulting error —
  reported against the citing step — looks identical. That trap cost real time; check the
  cited statement's own well-formedness before believing a fixture.
- **The guards precede every use**, so "the fact exists but only later" is not available as
  an explanation.
- **The same term elaborates fine one step earlier.** `@the-closed-form-at-s` writes
  `compose(compose(inv(s), swap(a, b)), inv(inv(s)))` and is accepted via `[by apply_at …]`.

And the goal is TRUE: replacing the one accelerant step with two `[by rewrite …]` steps — the
same substitutions the tactic performs — proves it green. So the defect is on the
accelerant's own path, not in the statement, the term, or the context.

## Measured scope: three words of eight, not all of them

Swept 2026-11-03 with one fixture per word, each shaped so the tactic actually has to work
over a guarded application:

| word | verdict | why |
|---|---|---|
| `simplify` | **RED** | rewrites INSIDE the guarded application |
| `chain` | **RED** | joins two equations THROUGH it |
| `specialize` | **RED** | instantiates a binder UNDER it |
| `assoc` | green | reorders, never rebuilds |
| `assoc_commut` | green | reorders, never rebuilds |
| `polynomial` | green | guarded application is an opaque atom |
| `arithmetic` | green | abstracts it as an opaque variable |
| `extensionality` | green | reduces to a pointwise residue |

**The dividing line is SUBSTITUTION.** A word that treats a guarded application as an opaque
atom passes; a word that substitutes into it reconstructs the application and re-raises its
guard. So this is a three-word fix, not a sweep of every accelerant.

`model` and `import` are engine words, not term builders, and already discharge guards through
`withGuardPremises`. `instantiation` routes through the same place. `tautology` sees every
non-propositional subformula as an opaque atom and so cannot manufacture a guarded term.

## Where the defect is NOT — four theories ruled out by measurement

Each of these was checked and is wrong. Recorded so the next attempt starts further along.

1. **"Generated terms are not scanned for guards."** FALSE. `Builder.termExpr` appends every
   delaborated term to `Synthetic.seen` automatically, and `syntheticObligations` scans all of
   them. Traced: the `simplify` synthetic collects `ok(s)` and `ok(inv(s))` and KEEPS both.
2. **"The obligation never reaches `requireKnown`."** FALSE — this was written into
   SIMPLIFY-ISSUES.md on the strength of the instrumentation printing nothing for the live
   sites, and the minimal fixture disproves it:

       [guard-miss] prop=3 'ok(s)' at kb=0 loc=3082 entries=0

   It arrives in block 0 against an EMPTY `known`. That is the synthetic's own ProveTask,
   where `e.known = null` is set by design.
3. **"`wrapObligations` fails to add the antecedents."** FALSE. Traced: the wrapped decl is a
   `binary` (the implication) with 2 steps (the assume/discharge pair) and both guards as
   leading antecedents.
4. **"It is about constants not being abstracted into params."** FALSE. The same failure
   occurs with a `fix`-bound subject that does abstract to `p1`.

**The decisive test is `wrapped-shape-by-hand.b4m`**, in this directory: the shape
`wrapObligations` produces, written by hand — `ok(s) -> ok(inv(s)) -> <goal>` proved under
`assume ok(s) { assume ok(inv(s)) { … } }`, with both guards also restated as explicit
`[by hypothesis …]` steps immediately above the `simplify`. It STILL reports `ok(s)`
unproved. So the guards are simultaneously the enclosing hypotheses and proved steps in the
same block, and `simplify` reads neither.

So the wrapped shape is not the problem, and neither is the obligation collection. What
remains is how `simplify`'s own check consults (or fails to consult) the context it is given.
That is where the next session should look — not at `paramGuards`, `seen`, or
`wrapObligations`, all of which behave correctly.

## The target behaviour

An accelerant relativizes its own generated statement to `guard(...) -> <statement>` and emits
the invocation so the guard is discharged at the call site by citing a step in scope — user
design, 2026-11-03. The plumbing for this EXISTS and is uniform: `Builder.termExpr` →
`Synthetic.seen` → `Prove.syntheticObligations` → `Prove.wrapObligations` →
`Prove.withGuardPremises`, with one call site (`demandUsing`) covering every accelerant.

The constraint: the only thing an accelerant may go digging for is a GUARD. Logical inputs
stay named in the citation. The rule governs the ENGINE, not the author — manual rummaging
while writing a proof is fine. See `fast-strict-invariant-and-rummage-rule`.

## Related

- `SIMPLIFY-ISSUES.md` — the author-facing symptom and the `[by rewrite …]` workaround.
- `ACCELERANT-GUARD-DISCHARGE-ISSUE.md` — the discharged-conclusion rule these fixtures
  deliberately avoid, plus the `guard_trace` instrumentation recipe.
- `drafts/accelerant-guard-discharge/` — the earlier `specialize`-at-a-refined-binder repro.
