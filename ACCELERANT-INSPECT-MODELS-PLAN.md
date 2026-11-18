# `debug accelerant` through models, and through towers of them

**Status: BUILT 2026-11-18** (items 1, 2, 3 partly, 5 of "What to build"). `--model` is
repeatable and composes a tower; the registry is keyed by space. What remains is item 4 (name
which mapping supplied each symbol) and the cross-file selector, both noted at the bottom.
User direction 2026-10-11: inspection must trace through models, possibly several layers; the
surface should be repeated `--model` flags building the tower we care about.

    2b4m debug accelerant <file> <line> --model <M1> --model <M2> --model <M3> …

## What happens today

The inspector re-runs the ordinary check and reprints the synthetic theorem an accelerant
produced for a step (`src/debug/accelerant.zig`). It contains **no mention of `model`**, and
two things block the multi-layer case.

### 1. A model-transfer citation is not inspectable at all

`std/rational/units.b4m:111` is

```2b4m
[using model(RationalUnits) field_units.oneIsNonzero]
```

and the inspector answers:

```
error: no accelerant produced a theorem there (is it a `[using <tactic> …]` step?)
```

It *is* a `[using …]` step. `model` is a citation rule rather than a producing accelerant, so
nothing lands in `synthetic_at` for it — but it is exactly the step a reader most wants
expanded, because what the kernel checked is the source theorem RE-PROVED under the mapping.

**Two-layer towers are the right test**, and `std/field/order.b4m` is full of them — e.g. its
line 177 is `[using model(FieldIsOrdered) field.addNegRight]`, so a ℚ-level citation of an
ordered-field theorem reads ℚ ← `RationalUnits` ← ordered field ← `FieldIsOrdered` ← field.
Reading what was checked at the bottom means composing two mappings.

### 2. The registry cannot hold more than one space per step

Generation IS model-aware — a synthetic produced under a model is renamed
(`Prove.zig:2531`):

```zig
if (self.model != .none and self.model != .universe) {
    const bytes = try std.fmt.allocPrint(arena, "{s}{{m{d}}}", .{ syn_name_bytes, @intFromEnum(self.model) });
    syn_name = try interner.internString(bytes);
    setSyntheticName(decl_ptr, syn_name);
}
```

but the step registry is not:

```zig
// Context.zig:401 — "keep-first: a step's synthetic is produced once per space;
// the first stays the answer"
pub fn registerSynthetic(self: *Context, file: FileId, loc: u32, name: InternPool.StrId) std.mem.Allocator.Error!void {
    const gop = try self.synthetic_at.getOrPut(self.arena, .{ .file = file, .loc = loc });
    if (!gop.found_existing) gop.value_ptr.* = .{ .file = file, .name = name };
}
```

The key is `(file, loc)` — **no model**. A step inside a theorem transferred through two models
produces three synthetics (universe, M1, M2) at one `(file, loc)`, and keep-first silently
keeps whichever space was scheduled first. The doc comment states the limitation honestly; it
is simply the wrong key for this feature.

Note also `{m<N>}` interpolates the model's raw `InternPool.Index`, which is
allocation-ordered — the same class of defect fixed in `instanceHash` (commit `cc800fe`,
`[[schema-instance-crosstalk]]`). A name a user is asked to pass on a command line should not
move between runs; expect to give the model the same `(name, loc)` treatment.

## What was built

1. **DONE — the registry is keyed by space.** `Context.SyntheticKey` is
   `(file, loc, model)`. Generation was ALREADY model-aware (the `…{m<N>}` rename), so the
   distinct decls existed and only this index collapsed them; keep-first now applies within a
   space rather than across all of them. Two read shapes, because the call sites want
   different things: `syntheticAt(file, loc, model)` reads one space, and
   `syntheticAtAnySpace(file, loc)` answers "is this offset inside a generated proof?" — which
   is what `ProveTask`'s demand diagnostic asks, and a step reached only under a model has no
   universe entry to find. `syntheticSpacesAt` enumerates them for the error path.
2. **DONE — repeated `--model`.** Each name resolves through `IdentKV` under the root file's
   universe namespace, then composes with `composeModel` (structurally interned, so the same
   composition is the same model). **GOTCHA:** composing with `.universe` is NOT the identity —
   `composeModel` reads `inner` as a model and panics on the universe — so the innermost flag
   must be taken directly and each further one composed over it.
3. **DONE for accelerant steps** — the model-space reprint IS the target-space formula, and a
   transfer onto a refined sort shows its relativization (`good(p1) ->` per binder), so the
   guarded-model caveat below is honoured. A bare `model(...)` CITATION step still has no
   synthetic to reprint (it is a citation rule, not a producer); that half is unbuilt.
5. **DONE — no flag means the universe space**, so existing behaviour is unchanged and the
   flags are purely additive. Gated by a same-step/two-space pair in `tests/test_query.zig`.

**GOTCHA worth keeping:** a model is an UNNAMED InternPool kind — `nameOf` is `unreachable` on
it, because the name lives in `IdentKV` under the declaring namespace, not on the entity. To
print a space as a `--model` argument the user can retype, walk the root file's `model` decls
and match by Index. A composed space was never declared under one name, so it says so instead
of inventing one.

## Still to build

4. **Report the tower, not just the leaf.** With `--model M1 --model M2`, say which mapping
   supplied each symbol. A composed overlay that silently loses a layer is worse than an error.
   (`2b4m debug model` now prints a model's surface, which covers part of this need.)
6. **The selector is ROOT-FILE ONLY** — pre-existing, not introduced by this work, but it is
   what blocks the two-layer test the plan wanted. A step in a transitively-imported file has
   its multi-space synthetics in the registry, yet cannot be addressed: `lineToStepOffset`
   resolves against the root AST. A fixture whose root holds BOTH the accelerant step and the
   transfer (`tests/cases/model/accel/model_accel_simplify.b4m`) exercises the feature; a true
   ℚ → F → ring tower needs a `<file>:<line>` selector naming the inner file.
7. **`{m<N>}` still interpolates the model's raw allocation-ordered Index** (see below). It is
   TRIMMED from the reprint, so no user-visible name moves between runs today — but it would
   if anything ever printed it.

## Watch out for

- **`model` is a FULL OVERLAY over the universe, not a scoped rename** (`[[model-source-theory-only]]`,
  user ruling 2026-09-26). Composing two models is composing two overlays; it is not a
  namespace stack, and `--model A --model B` must not be implemented as sequential renaming.
- **Guarded models nominate dischargers on the `:` map** (`[[model-mechanism-design]]`): a
  const maps as `src.C: TGT(baseFact…)` and a func as `src.op: F -| closureFact…`. Transferred
  theorems RELATIVIZE — a guard premise per binder. An inspection that prints the unrelativized
  statement would misreport what was checked.
- **`sourceSpaceAccelerants()` is `self.underModel()`** — true when the CITING proof is under a
  model. A model named at the CITE makes that guard false. Any inspection that reconstructs
  the producer's space has to distinguish "under a model" from "citing through one".
- **Accelerants build in SOURCE space** (`[[accelerants-not-model-aware]]`, resolved
  2026-09-11): the producer emits source-space AST and the mapping applies afterwards. So the
  honest reprint may want BOTH — what the producer emitted, and what the kernel checked after
  remapping.
