# drafts/schema-transfer — why a schema did not transfer through a model

**These files FAIL ON PURPOSE.** They are a live repro, not a regression suite — `2b4m check`
on the two consumers is expected to error until the fix lands. They are in `drafts/` rather
than `tests/cases/` for exactly that reason (and so they stay out of the `--library` sweep).

Built 2026-10-03 to answer: *a plain theorem transfers through a model, so why not a schema?*

## The files

| file | what it is |
|---|---|
| `source-theory.b4m` | one sort, one axiom, and TWO theorems proved from it — one PLAIN, one a SCHEMA over a predicate. Both proofs cite the same axiom the same way. |
| `consumer.b4m` | models that theory onto its own sort. **Case A** cites the plain theorem — passes. **Case B** cites the schema at a predicate of its own — fails, inside the SOURCE file. |
| `binders-only.b4m` / `binders-only-consumer.b4m` | the same, with NO constants anywhere, so the failure is isolated to BINDER SORTS. |
| `FINDING.md` | the diagnosis, with the confirming experiment. |

Run `2b4m check drafts/schema-transfer/consumer.b4m` — case A proves, case B reports
`source-theory.b4m:26: expected sort 'Thing', got 'Elem'`. The minimal pair differs only in
whether the cited theorem takes a predicate parameter.

## The answer, in one paragraph

A schema **should** transfer; nothing structural prevents it. The machinery is all present — a
schema instance's body is re-checked at the instance, `buildInstanceState` sets
`prove.model = task.model` ("so the monomorphized body is in target terms"), and sort
resolution is model-aware throughout (`Elab.lookupIdent` and `resolveSymbolTok` both end in
`applyModel`). What breaks is the ARGUMENTS: `demandInstance` binds them TWICE, once in target
space and once as a source-space twin, because a transferred proof runs passes in both spaces.
The no-discharge path added in `7cf3c94` binds ONCE and passes the same map for both
(`.{ bound, bound }`), so the source-space pass receives target-space args. See `FINDING.md`
for the confirming experiment (writing the lambda binder in source space moves the error from
the source file to the cite — one map cannot satisfy both checks, which is why there are two).

## Two separable obstacles

1. **The two-space args bug** — mine, from `7cf3c94`. Fix: bind twice, as `demandInstance`
   does. Would make capture-free maps work.
2. **The lambda cannot capture a `fix`-bound variable** — a design question, not a bug.
   `demandSchemaTransfer` runs in the READ PASS, before step-local scope exists;
   `demandInstance` receives the caller's live `Elab`, the read-pass path has none. Needs a
   decision about pass structure.

When (1) lands, `consumer.b4m` case B should pass and these files move to `tests/cases/` as a
regression fixture. Until then they document the gap. Related: `CONTAINER-THEORY.md` (the
container's generic lemmas are blocked on this), `CHAPTER6-PAINPOINTS` (§6.3 hits it from the
other side).
