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

## The mangled-name route: tried, and what it costs

The user's proposal — "can't accelerants run in model space and synthesize/call mangled theorem
names?" — is the right instinct, and most of the machinery is already there:

- synthetics are **already mangled per model**: `name{m<model-index>}` (`Prove.zig:2608`);
- the builder already has an **exact-symbol** encoding — `Accelerant.Builder.symTok(sym, exact)`
  sets `qualifier = .universe`, which `Elab.resolveSymbolTok` reads as "this Index is final,
  skip `applyModel`";
- `Delaborate.runExact` exists for precisely this, emitting exact symbols throughout.

**`runExact` is never called.** The builder's `termExpr` uses plain `Delaborate.run`, so every
delaborated symbol is subject to the ambient model on re-elaboration — which is exactly why the
producer must run with the model off.

Wired it up as an experiment: a `Builder.exact_syms` flag feeding `runExact`, a
`Prove.produce_in_model_space` flag threaded into all 11 producer Builders, and `demandUsing`
selecting model-space production instead of source-space. **The target case passed** — the
failure moved off the accelerant and onto the `specialize` head's own argument, then that
resolved too once `producerPremiseFormula` returned the target formula (it already branches on
`self.model`, so it needed no change).

**What it broke:** `std/group/listing.b4m:803` under the ℤ_n transfer —
`expected sort 'Zn', got 'Grp'`. An ORDINARY transfer, which must build in source space.

So the hard part is not the mechanism, it is the PREDICATE: *when* must a producer build in model
space? Two conditions were tried and both are too coarse:

- "this proof is a schema instance under a model" — fires for every ordinary transfer.
- "...and its source twin differs from its target args" — still fires for `group/listing`, so
  twin-identity does not separate the cases.

The real distinction is per-SYMBOL, not per-pass: a goal is unbuildable in source space exactly
when it mentions a symbol with no source form. That is decidable (walk the goal, ask whether
each symbol resolves in the source namespace) but it is a different shape of question from the
single boolean the code asks today — which is what "accelerants must be namespace aware" means
concretely.

Related: this is a sibling of the known "accelerants not model-aware" boundary already recorded
for guarded transfers (memory `accelerants-not-model-aware`, and the omitted
`group.invProduct` in `tests/cases/model_subgroup_transfer.b4m`, which cites the `assoc`
accelerant). Worth checking whether one fix covers both.
