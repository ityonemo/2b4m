# A tactic's generated rewriting does not see guards that a step in scope has proved

**Status: OPEN, diagnosed 2026-11-03.** Found while de-totalizing `sub` — specifically in
`std/field/polynomial-associativity.b4m`, whose terms are full of `sub(sub(i,j), k)`.

## The symptom

A `simplify` (or `chain`) step fails with

```
error: unproved obligation: 'less_than(j, i) or j = i'
```

even though a step *earlier in the same block* has proved exactly that:

```2b4m
@j-is-within |
  peano_order.less_or_equal(j, i)
  [by hypothesis given-j-within]
...
@base-case |
  tripleRow(p, q, r, i, j, succ(ZERO)) =
    mulF(coeff(p, j), fieldpoly.convolution(q, r, sub(i, j), ZERO))
  [using simplify the-row-at-one the-empty-row the-first-entry
    subtracting-zero the-convolution-at-zero addZeroLeftAtTheEntry
    theProductRegroups]        // <- owes `j <= i` here, despite @j-is-within
```

The guard IS in scope. Each cited premise, checked on its own, is fine. The failure appears
only when enough premises are cited for the tactic to construct an intermediate term.

## What is actually happening

`GUIDE.md`'s rule — *"what a tactic FINDS is a guard obligation a written term owes … met from
`fix`-block guards, enclosing `assume` hypotheses, or proved steps in scope"* — holds for terms
the **author writes**. It does not appear to hold for terms the tactic's own normalization
**generates** mid-rewriting. `simplify` re-derives intermediate forms while walking to a normal
form; when such a form contains a guarded application, the obligation surfaces at the tactic's
source position with no access to the surrounding step list.

Evidence gathered:

1. **Bisection shows no single premise is responsible.** Citing `the-row-at-one` plus any ONE
   other premise changes the error to a normal-form mismatch, not a guard failure. The guard
   obligation only appears once the premise set is large enough to build the intermediate.
2. **Reordering does not help.** Hoisting the guard step to the top of the `assume` block, and
   separately fixing genuine forward references (several steps did cite later steps — a real
   bug in that file, now fixed), left the obligation unchanged.
3. **`chain` has it too.** Replacing the `simplify` with a single `chain` over the same
   equations reproduced it, so this is not specific to `simplify`'s rewriting engine — it is
   whatever path builds a term from cited equations.
4. **Hand-written steps are fine.** The same equalities, assembled as explicit
   `rewrite`/`chain`/`symmetry` steps each naming its own formula, all discharge the guard from
   the step in scope and check strictly. That is the workaround and it is what the file now
   does.

## The workaround

Replace the one big `simplify` with explicit steps whose formulas you write yourself. The
guard then attaches to a term the author wrote, which the documented rule covers:

```2b4m
@the-entry-at-the-collapsed-index |
  tripleTerm(p, q, r, i, j, ZERO) =
    mulF(mulF(coeff(p, j), coeff(q, ZERO)), coeff(r, sub(i, j)))
  [by rewrite subtracting-zero the-first-entry]
@the-entry-regrouped |
  tripleTerm(p, q, r, i, j, ZERO) =
    mulF(coeff(p, j), mulF(coeff(q, ZERO), coeff(r, sub(i, j))))
  [using chain the-entry-at-the-collapsed-index theProductRegroups]
... etc
```

Cost: a 1-line `simplify` becomes 5–6 steps. In the associativity file that is the difference
between a readable proof and a mechanical one, and it has to be done at every site whose
intermediate terms mention a guarded application.

## Why this matters beyond one file

De-totalization makes guarded functions normal rather than exceptional. Any proof that
`simplify`s over terms built from `sub`, `div`, `mod` or `recip` can hit this, and the error
message points at the tactic rather than at the cause, so the natural response — "but I proved
that two steps ago" — is correct and unhelpful. It cost several hours here before the pattern
was isolated.

## What a fix would need to decide

- Should a tactic's generated intermediate terms be able to discharge guards from the enclosing
  step list? If yes, the guard search has to be threaded into the normalizer, not just applied
  at author-written terms.
- Or should the obligation be reported differently — naming the generated term that owes the
  guard, rather than the step position? Even without a behavioural change, an error that said
  *which* term needs the guard would have saved most of the time lost here.
- `--fast` admits these, so they surface only under strict check. That is correct (the guard
  genuinely is not discharged) but means the loop does not warn you.

## The engine half

**`ACCELERANT-GUARD-DISCHARGE-ISSUE.md` (2026-11-04) traces this through the engine** and
finds the path it takes: an accelerant generates a synthetic SCHEMA whose obligations become
ANTECEDENTS (`wrapObligations`), and the call site must discharge them via
`withGuardPremises` → `dischargeGoal` → `refForKnown` → `Known.lookup`. That machinery exists
and is on the path, so the fix belongs at the discharge end rather than in the tactic. It also
records what was ruled out (block visibility, alpha-equivalence, a missing fact) and the one
real bug found on the way, in `settleMisses`, now fixed.

## Related

- `GUIDE.md`, `### WHAT A TACTIC IS GIVEN vs WHAT IT FINDS` — the rule this appears to violate
  for generated terms.
- `[[no-totalizing-functions-in-std]]` — why guarded functions are becoming the norm.
- `NESTED-MODEL-COMPOSITION-ISSUE.md` — the sibling diagnostics problem: an incomplete model
  discharge also reports itself as a sort error in an unrelated file. (That file's original
  claim, that models cannot compose, was wrong and is retracted there.)

## MEASURED 2026-11-03: three accelerants re-owe a guard a step in scope has proved

Hit during the `function.inverse` de-totalization, in
`std/permutation/alternating-identities.b4m` (`theLongCycleCommutatorIsAThreeCycle`,
`theTwoThreeCyclesCommutatorIsAFiveCycle`, `theTwoCycleCommutatorRegrouped`) and in
`std/group/order.b4m:776`.

**RED FIXTURES: `drafts/accelerant-generated-guard/`** — one 80-line ground proof per affected
word, differing only in the final justification, each failing `unproved obligation: 'ok(s)'`
with `ok(s)` proved at the top of the same (and only) block. The README there records what
each fixture suppresses so that nothing but the engine is implicated, and the trap that cost
the most time: an axiom written `forall f: Fn; inv(inv(f)) = f` is genuinely ILL-FORMED (it
asserts something about `inv(f)` where `inv(f)` may be undefined), and its error is reported
against the CITING step, looking exactly like this defect. Check the cited statement's own
well-formedness first.

### Scope: three words of eight

| word | verdict | why |
|---|---|---|
| `simplify` | **RED** | rewrites INSIDE the guarded application |
| `chain` | **RED** | joins two equations THROUGH it |
| `specialize` | **RED** | instantiates a binder UNDER it |
| `assoc` / `assoc_commut` | green | reorder, never rebuild |
| `polynomial` / `arithmetic` | green | guarded application is an opaque atom |
| `extensionality` | green | reduces to a pointwise residue |

**The dividing line is SUBSTITUTION:** a word treating a guarded application as an opaque atom
passes; a word substituting into it reconstructs the application and re-raises its guard.

### Where the lookup actually goes — CORRECTION

An earlier version of this section claimed the obligation never reaches `requireKnown`, on the
evidence that the `guard_trace` instrumentation printed nothing for the live sites. **That was
wrong**, and the minimal fixtures show it. With `guard_trace = true`:

```
[guard-miss] prop=3 'ok(s)' at kb=0 loc=3082 entries=0
```

It DOES reach `requireKnown` — in block 0 against an EMPTY `known` (`entries=0`). That is the
synthetic's own ProveTask, where `e.known = null` is set deliberately (a synthetic is
registered globally and instantiated by name, so it must not depend on one call site's
context). The guard was never missing; it was being looked up in a space that has no steps.

That still points at relativize-and-cite as the fix, but for a different reason than
originally recorded: not "the obligation is invisible", but "the obligation is raised in the
synthetic's space, where by design nothing can answer it, instead of being carried out to the
call site as an antecedent".

### The target behaviour

An accelerant relativizes its own generated statement to `guard(...) -> <statement>` and emits
the invocation so the guard is discharged at the call site by citing a step in scope (user
design, 2026-11-03: *"it would be nice to make simplify work out of the box"*, then *"all of
the accelerants should be able to reconfigure theorem statement as `guard(...) -> <actual
statement>`"*). The machinery exists and is already uniform — `Builder.termExpr` records every
delaborated term in `Synthetic.seen`, `syntheticObligations` reads what those terms owe,
`wrapObligations` prepends them as antecedents, `withGuardPremises` discharges them at the call
site, and the single call site `demandUsing` covers every accelerant. So the gap is narrower
than "some words have the mechanism and some do not".

The constraint on any fix: the ONLY thing an accelerant may go digging for is a guard —
logical inputs stay named in the citation. The rule governs the ENGINE, not the author; manual
rummaging while writing a proof is fine.

### Author-side workarounds meanwhile

All landed in `5d47eb9`, all green: substitute the equations one at a time with
`[by rewrite …]` instead of one `simplify`/`chain`; and for a `specialize` at a REFINED binder,
`[by cite …]` + `[by apply_at(t) …]`.
