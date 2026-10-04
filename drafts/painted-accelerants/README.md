# drafts/painted-accelerants — accelerants should produce in the AMBIENT namespace

Banked 2026-10-04, NOT applied. `painted-production.patch` is a 2-change WIP against
`src/Engine/ProveTask/Prove.zig`; applying it takes `check --library std` from green to ONE red
file. Kept because the diagnosis is solid and the remaining error is a known blocker.

## The design question (user, 2026-10-03/04)

> "An accelerant is running in whatever namespace it's running in, and that's that. It should
> not matter whether it's in universe or in a model."

Today `demandUsing` does the opposite: `if (source_mode) self.model = .universe` — it turns the
ambient model OFF, runs the producer in SOURCE space, and lets the instance `ProveTask` re-paint
the result afterwards. I defended that as "namespace-neutral, therefore one synthetic serves
every transfer." That defence is wrong.

## Why neutrality is wrong — the decisive example

The user's framing: two models that create a `SOME_NEG_NUMBER` and a `POS_NUMBER` and use them
in the same arithmetic call will need DIFFERENT theorems. The producer, running unpainted, sees
an opaque source symbol with no sign information and emits one skeleton.

`std/set.b4m` confirms it concretely, with no arithmetic needed. The step
`[using specialize unionMember(b, c)]` cites `unionMember`, an AXIOM the model discharges
(`set.unionMember <- unionCollectionContains` in `std/collection.b4m`). The two differ in the
binder sort:

    axiom unionMember:              forall a, b: Set;        …   (source)
    axiom unionCollectionContains:  forall a, b: Collection; …   (the discharging fact)

So the producer reads a **different theorem** depending on whether it is painted. That is the
consumer contributing the fact, which is exactly what unpainted production cannot see.

Corroborating: `arithmetic` is documented as receiving its domain facts FROM THE THEORY — memory
`arithmetic-pure-integer-engine`, "ℕ nonnegativity is theory-supplied via a well-known `nonneg`
predicate injected per variable", and `ARITHMETIC-SORT-AGNOSTIC-DESIGN.md`'s "integrality is a
declared capability, not a sort". A neutral producer asks the WRONG THEORY for those facts.

## What the patch does, and what it fixes

1. `source_mode = false` — produce with the ambient model ON.
2. A `Prove.painted_production` flag that SUPPRESSES the source-space arg twin. Under painting
   the synthetic is already target-space text, so a source twin is meaningless — and harmful.
   Instrumentation at the failing check showed exactly that: `src_space=true`, wanting
   `Collection` (the painted param) while elaborating the arg at `Set`.

Result: `check --library std` goes from 3 errors to 1.

## The one remaining error is a DOCUMENTED BLOCKER

```
std/group.b4m:433: AffineGroup@assoc{…}: step claims
  'forall b1: Real; notMinusOne(b1) -> … star(star(starInverse(a), b1), b2) = …'
but forall_elim derives
  'notMinusOne(starInverse(a)) -> forall b1: Real; notMinusOne(b1) -> …'
```

A GUARD PREMISE appearing where the claim is unguarded — verbatim the symptom pinned in
`ACCELERANT-ON-GUARDED-SETS.md`, which lists three candidate root-cause readings and states none
is established. Painted production arrives at that blocker from the opposite side, which is
evidence it and the accelerant-namespace question are one issue rather than two.

Also unresolved and likely the same: `group.invProduct` is omitted from
`tests/cases/model_subgroup_transfer.b4m` because its proof cites the `assoc` accelerant (the
fixture calls it "a known separate boundary"), and the month-old memory note
`accelerants-not-model-aware`.

## Sequencing (user, 2026-10-04)

Bank this → items 1–3 of `~/.claude/plans/mighty-whistling-shannon.md` (demote `Prop`, the
schema-parameter union, the syntax) → then the documented blocker, with this patch as the
starting point.

## A process note worth keeping

Four wrong conclusions about this subsystem in one session, each from reading code rather than
running it: a correct diagnosis retracted on a misread comment, a deliberate mode switch called
"conceptually wrong", a transfer failure reported as a plain-case failure (the diagnostic names
the SOURCE file, which is misleading), and `source_mode` described as the only asymmetry when
the arg twin was another. Every one was settled in a single step by `std.debug.print` at the
failing comparison. In this subsystem, instrument first.
