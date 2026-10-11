# `debug accelerant` through models, and through towers of them

**Status: DESIGNED, not built.** User direction 2026-10-11: inspection must trace through
models, possibly several layers; the surface should be repeated `--model` flags building the
tower we care about. Not urgent.

    2b4m debug accelerant <file> <line> --model <M1> --model <M2> --model <M3> …

## What happens today

The inspector re-runs the ordinary check and reprints the synthetic theorem an accelerant
produced for a step (`src/debug/accelerant.zig`). It contains **no mention of `model`**, and
two things block the multi-layer case.

### 1. A model-transfer citation is not inspectable at all

`std/rational/units.b4m:155` is

```2b4m
[using model(RationalUnits) field_order.recipMulLeft]
```

and the inspector answers:

```
error: no accelerant produced a theorem there (is it a `[using <tactic> …]` step?)
```

It *is* a `[using …]` step. `model` is a citation rule rather than a producing accelerant, so
nothing lands in `synthetic_at` for it — but it is exactly the step a reader most wants
expanded, because what the kernel checked is the source theorem RE-PROVED under the mapping.

**This case is already a two-layer tower**, which is why it is the right test: the transferred
theorem's own proof at `std/field/order.b4m:303` is itself
`[using model(FieldIsOrdered) field.recipMulLeft]`. So ℚ ← `RationalUnits` ← ordered field ←
`FieldIsOrdered` ← field. Reading what was checked at the bottom means composing two mappings.

### 2. The registry cannot hold more than one space per step

Generation IS model-aware — a synthetic produced under a model is renamed
(`Prove.zig` ~2752):

```zig
if (self.model != .none and self.model != .universe) {
    const bytes = try std.fmt.allocPrint(arena, "{s}{{m{d}}}", .{ syn_name_bytes, @intFromEnum(self.model) });
    syn_name = try interner.internString(bytes);
    setSyntheticName(decl_ptr, syn_name);
}
```

but the step registry is not:

```zig
// Context.zig ~402 — "keep-first: a step's synthetic is produced once per space;
// the first stays the answer"
pub fn registerSynthetic(self: *Context, file: FileId, loc: u32, name: StrId) !void {
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

## What to build

1. **Key the registry by space.** `SyntheticKey` gains the model: `(file, loc, model)`. Then
   every space's synthetic is reachable and keep-first stops discarding information. This is
   the enabling change; the flag is useless without it.
2. **Accept repeated `--model`,** resolving each name to its declaration in the file under
   inspection (or in an import), and compose them into the overlay the inspection runs under —
   left-to-right, outermost first, matching how the citation nests.
3. **Make `model(...)` citations inspectable.** Reprint the source theorem's statement with the
   mapping applied, so a reader sees the target-space formula the kernel re-checked rather
   than the source-space one they can already read. The rendering is a reprint, not a second
   producer — same discipline as the existing module.
4. **Report the tower, not just the leaf.** With `--model M1 --model M2`, say which mapping
   supplied each symbol. A composed overlay that silently loses a layer is worse than an error.
5. **Default with no flag**: the universe-space synthetic, which is what it prints now — so the
   existing behavior is unchanged and the flags are purely additive.

## Watch out for

- **`model` is a FULL OVERLAY over the universe, not a scoped rename** (`[[model-source-theory-only]]`,
  user ruling 2026-09-26). Composing two models is composing two overlays; it is not a
  namespace stack, and `--model A --model B` must not be implemented as sequential renaming.
- **Guarded models nominate dischargers on the `:` map** (`[[model-mechanism-design]]`): a
  const maps as `src.C: TGT(baseFact…)` and a func as `src.op: F -| closureFact…`. Transferred
  theorems RELATIVIZE — a guard premise per binder. An inspection that prints the unrelativized
  statement would misreport what was checked.
- **`sourceSpaceAccelerants()` is `self.underModel()`** — true when the CITING proof is under a
  model. A model named at the CITE makes that guard false (noted in the `prop-demotion` plan's
  item 4). Any inspection that reconstructs the producer's space has to distinguish "under a
  model" from "citing through one".
- **Accelerants build in SOURCE space** (`[[accelerants-not-model-aware]]`, resolved
  2026-09-11): the producer emits source-space AST and the mapping applies afterwards. So the
  honest reprint may want BOTH — what the producer emitted, and what the kernel checked after
  remapping.
