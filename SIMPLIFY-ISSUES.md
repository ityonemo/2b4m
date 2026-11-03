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

## Related

- `GUIDE.md`, `### WHAT A TACTIC IS GIVEN vs WHAT IT FINDS` — the rule this appears to violate
  for generated terms.
- `[[no-totalizing-functions-in-std]]` — why guarded functions are becoming the norm.
- `NESTED-MODEL-COMPOSITION-ISSUE.md` — the sibling diagnostics problem: an incomplete model
  discharge also reports itself as a sort error in an unrelated file. (That file's original
  claim, that models cannot compose, was wrong and is retracted there.)
