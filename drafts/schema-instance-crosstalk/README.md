# schema-instance crosstalk — RESOLVED 2026-10-22 (minimal repro + the two controls)

**ROOT CAUSE** (`src/Engine/ProveTask/Prove.zig`, `produceSpecialize`): the synthetic schema's
name was `specialize{hash}` with the hash over the HEAD FORMULA and ARG COUNT only. But the
schema BODY also depends on whether the head is LOCAL — a local head's body carries the head
formula as antecedent #0 (discharged by the citing step) and a declared head's does not — and
a local step that `[by cite]`s a fact has exactly the fact's formula. So the two flavours
hashed to ONE name, `registerDecl` is keep-first, and whichever theorem ran second silently
instantiated the OTHER flavour's body against its own premise list: a one-position premise
shift, which is both faces below. Scheduling-dependent because the loser is whoever runs
second. The `{m<N>}` model-mangling a few lines up is the same bug class, fixed earlier along
a different axis.

**FIX:** mix the head flavour into the hash (one line). Verified: the repro and both controls
pass; the 2026-10-10 repro passes (under `--draft` — it has an unrelated dead step of its own
that the crosstalk had masked); the 400-line parent is 10/10 green at `-j1` where it was an
8/2 split of two different errors. Regression: `tests/cases/schema_instance_crosstalk/`.

The `--chaos=<seed>` non-replay noted below is a SEPARATE defect and is still open.

---


Bisected 2026-10-22 from a 400-line `std/group/size.b4m` failure down to 75 lines over
`std/peano` only. Refines the bug recorded at `drafts/schema-instance-crosstalk.b4m`
(2026-10-10), which this supersedes as the primary repro.

## The trigger: a MIXED ACCESS PATH to one shared fact

Two theorems both `specialize` the SAME declared fact. What matters is HOW each reaches it:

| `first` reaches the fact by | `second` reaches it by | result |
|---|---|---|
| declared name | declared name | **passes** (`control-both-declared-names.b4m`) |
| local label (`[by cite]` then specialize that step) | local label | **passes** (`control-both-local-labels.b4m`) |
| declared name | **local label** | **FAILS** (`mixed-access-paths.b4m`) |

Each theorem also passes ALONE in the failing file — check with
`2b4m check mixed-access-paths.b4m first` and `… second`. Only the pass over both is red.

So the recorded framing "a specialize whose head is an assumed hypothesis" is too narrow:
neither access path is wrong by itself, and labels are not the culprit. It is the MIXTURE.

## The two faces, and which appears is SCHEDULING-DEPENDENT

Both diagnostics from the original memo show up:

    error: instantiate: expected premise 'less_than(n, n) or n = n',
           got 'forall n: Nat; forall b: Nat; forall a: Nat; ...'   ← the WHOLE universal, unpeeled
    error: cannot discharge the guard premise '<the whole statement of the fact>'

The "got" value being the unpeeled universal is the tell: `specialize` never eliminated the
head's binders — the head-step got fed in as a PREMISE instead. `src/kernel.zig:625`
(`.schema_instance`) walks premises left-to-right peeling one `->` each, and
`src/Engine/ProveTask/Prove.zig:3382` (`wrapObligations`) PREPENDS one antecedent per guard
obligation — which shifts every premise position. That is the shape of the corruption; the
cause is still upstream of both.

## NEW, and a correction to the old memo: it is NONDETERMINISTIC AT `-j1`

The 2026-10-10 memo says `-j1` reproduces deterministically. It does not. Measured on the
400-line parent, 10 runs at `-j1`: **8 failed at one site, 2 at the other**. Controls:

| flag | result |
|---|---|
| `-j1` alone | 8/10 site A, 2/10 site B |
| `-j1 --sync-io` | 6/6 site A — **pins it** |
| `-j1 --io-delay=200` | 6/6 site A |
| `-j1 --chaos` | 2/6 site A, 4/6 site B — **flips the majority** |

So the variation rides on ASYNC IO COMPLETION ORDER (`--sync-io` removes it), which perturbs
demand order, which selects which theorem's instance gets corrupted. Not a data race on the
instance itself — a single worker still corrupts it — but order-dependent.

**Separate defect found while measuring:** `--chaos=<seed>` does NOT replay. The same seed
gave site B, then site A, on consecutive runs (seeds 1/2/3, twice each, all six differed from
their pair). A seeded chaos mode that cannot reproduce a schedule defeats its own purpose.

## Workarounds (both verified)

1. Make the access path UNIFORM — have every theorem in the file reach the fact the same way.
   This is what fixed `std/group/size.b4m`: drop the local restatement and cite the declared
   name at the use site.
2. The original memo's two: cite-to-a-local-step everywhere, or split a conjunction theorem
   into single implications.
