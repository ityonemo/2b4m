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

## MEASURED 2026-11-03: `simplify` owes a guard no in-scope step can satisfy — WORKAROUND FOUND

Hit three times during the `function.inverse` de-totalization, in
`std/permutation/alternating-identities.b4m` (`theLongCycleCommutatorIsAThreeCycle`,
`theTwoThreeCyclesCommutatorIsAFiveCycle`, `theTwoCycleCommutatorRegrouped`). Each is a
`[using simplify image-a1 image-a2 image-a3 the-closed-form]` step whose formula writes
`inverse(sigma)` and `inverse(inverse(sigma))`, reporting
`unproved obligation: 'invertible(sigma)'`.

**THE WORKAROUND: substitute the equations one at a time with `[by rewrite …]`.** Each
`simplify` became three kernel `rewrite` steps — the same substitutions the tactic was doing,
written out — and all three theorems now check strict. The guard is read normally on the
kernel path. This is the same explicit-steps escape the rest of this file documents, and it is
cheap here: three steps per site, no new lemmas.

**What made it look unfixable.** Every placement that fixes the *discharged-conclusion* rule
(which `ACCELERANT-GUARD-DISCHARGE-ISSUE.md` resolved as NOT A BUG) was tried first, and none
moved the error: the fact restated as the step immediately above; `invertible(inverse(sigma))`
added for the outer `inverse`; the binder retyped to the refined sort `Perm`; the guard read
via `[by predicate …]`; the antecedent hoisted ahead of the point binders; the fact hoisted to
the `fix`/`assume` boundary. So this is NOT the discharged-conclusion rule — teaching `known`
at any depth cannot satisfy it.

**Two diagnostics that localize it:**

- **It is a `--fast`/strict divergence.** `check --fast <file> <theorem>` PASSES; strict
  rejects. Under the standing invariant (`--fast` must never reject what strict certifies;
  `--fast` may accept what strict rejects, but neither may accept something FALSE) this is the
  permitted direction — the goals are true, now proved — but it places the obligation on the
  CERTIFIER path, not the decision path.
- **The guard-miss trace never sees it.** The instrumentation in `Elab.requireKnown` (now a
  flip-to-true `guard_trace` constant in `src/Engine/ProveTask/Elab.zig`; recipe in
  `ACCELERANT-GUARD-DISCHARGE-ISSUE.md`) prints nothing for these three sites while printing
  freely for others in the same run. **So the obligation is not routed through `requireKnown`
  at all** — which explains why no amount of teaching `known` helps, and is where a real fix
  should look: `simplify`'s certifier builds its own terms and raises their guards on a path
  that does not consult the step's context.

**Status: all three theorems PROVED**, so the de-totalization pass is not blocked. What remains
open is the engine behaviour, and it SHOULD be fixed rather than worked around (user, 2026-11-03:
"it would be nice to make simplify work out of the box"). The workaround trades one tactic call
for three hand-written kernel steps that spell out exactly what the tactic was already doing —
a tactic owing a guard its caller cannot discharge is a defect, and the trace localizes it: the
obligation bypasses `requireKnown`, so the fix belongs where `simplify`'s certifier builds its
terms and raises their guards without consulting the step's context.

## A second, cheaper pattern found in the same pass (NOT a bug)

`[using specialize invInvolution(sigma) sigma-is-a-permutation]` fails with
`unproved obligation: 'invertible(sigma)'` whenever the cited theorem binds its variable at a
REFINED sort (`forall a: Perm`). `specialize` cannot read a refined binder's qualifier from a
ref — the guard is looked up, never passed. Peel the binder explicitly instead:

```2b4m
@the-involution |
  forall a: Perm; inverse(inverse(a)) = a
  [by cite function_invertible.invInvolution]
@double-inverse |
  inverse(inverse(sigma)) = sigma
  [by apply_at(sigma) the-involution]
```

This fixed four sites across `decomposition.b4m`, `normal-subgroup.b4m` and
`alternating-identities.b4m`, and is worth reaching for before any restructuring: it is two
steps and changes no statement.
