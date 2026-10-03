# drafts/schema-transfer — the accelerant-in-a-transferred-schema-body gap

**These files FAIL ON PURPOSE.** A live repro, not a regression suite — in `drafts/` so they
stay out of the `--library` sweep, and because `2b4m check` on the consumer is expected to error
until the gap is closed.

## What is already fixed (moved to tests/)

The original question — *a plain theorem transfers through a model, so why not a schema?* — is
answered and the fix landed. A schema instance runs passes in BOTH spaces (its statement in
target terms, a source-space pass over its body), so its arguments must be bound twice, once per
space; the no-discharge transfer path bound them once. Regression guard:
`tests/cases/model_schema_transfer.b4m` (+ `_source.b4m`).

## What remains here

`binders-only.b4m` / `binders-only-consumer.b4m`: the same transfer, but the schema's body uses
an **accelerant** (`[using specialize all(y)]`). Accelerants run their own source-space pass with
their own argument binding, and that path has the same two-space mismatch the instance path had:

```
drafts/schema-transfer/binders-only.b4m:21:20: error: expected sort 'Thing', got 'Elem'
```

Run `2b4m check drafts/schema-transfer/binders-only-consumer.b4m` to see it.

So: a transferred schema whose body is pure kernel steps works; one whose body uses an
accelerant does not. Since nearly every real schema in std uses accelerants
(`std/group/listing.b4m`'s five, `std/permutation/listing.b4m`'s four), this is the gap that
still blocks the duplicated-proof consolidation — see `CONTAINER-THEORY.md`.

## Why it is not a small fix — the source-space design has no room for a consumer symbol

Chased 2026-10-03. The failing check is `Elab.elaborateCall`'s argument sort test, and the
instrumented callee is the giveaway:

```
[dbg] elaborateCall callee='flagged' model=.universe source_space=true expected=Thing got=Elem
```

`flagged` is the CONSUMER's predicate, substituted in as the schema argument, being applied in
a SOURCE-SPACE pass. The pass elaborates the schema's own binder `y` at `Elem` (source), but
`flagged` is a target-space symbol expecting `Thing`. The two cannot agree.

**Why the accelerant runs source-space at all** (`Prove.demandUsing`, the comment at
"ACCELERANTS BUILD IN SOURCE SPACE AND THE INSTANCE ADOPTS THE MODEL"): a synthetic schema is
registered against the SCHEMA's file, so a synthetic built from a target-relativized goal would
delaborate target names into the source file's namespace, where they do not resolve. Producing
in source space avoids that, and the instance then adopts the model. Sound — for an ordinary
transfer, where every symbol in the goal HAS a source form.

**Why that premise fails here.** A consumer-supplied schema argument is target-only by
construction. `flagged` is declared in the citing file and has no source-side twin, so there is
nothing for a source-space pass to build from. Two attempts confirmed this is structural, not
an oversight:

- Suppressing source-space production when the args are target-only: the guard never fires,
  because the source twin IS a distinct map (the sorts differ even though the body does not).
- Extending the MODEL-HOME FALLBACK (`Elab.lookupIdent`, which already resolves target-only
  symbols like guard predicates in the model's home file) into source-space passes via a
  separate `home_model` field: `flagged` then resolves fine, and the error does not move —
  because it was never a name-resolution failure. The mismatch is that the pass mixes
  source-space BINDERS with a target-space SYMBOL.

**So the accelerant must become namespace-aware** (user, 2026-10-03) rather than model-off. The
present design handles the namespace question by sidestepping it — turn the model off, build in
one space, let the instance adopt the model afterwards. That works when the goal is wholly a
source-theory statement and breaks as soon as a consumer symbol rides in through a schema
argument. The fix is for the producer to know which space each symbol belongs to, which is a
real piece of design, not a patch.

Related: this is a sibling of the known "accelerants not model-aware" boundary already recorded
for guarded transfers (memory `accelerants-not-model-aware`, and the omitted
`group.invProduct` in `tests/cases/model_subgroup_transfer.b4m`, which cites the `assoc`
accelerant). Worth checking whether one fix covers both.
