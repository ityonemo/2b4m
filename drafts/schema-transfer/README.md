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

Related: this is a sibling of the known "accelerants not model-aware" boundary already recorded
for guarded transfers (memory `accelerants-not-model-aware`, and the omitted
`group.invProduct` in `tests/cases/model_subgroup_transfer.b4m`, which cites the `assoc`
accelerant). Worth checking whether one fix covers both.
