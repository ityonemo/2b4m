# "An accelerant's guard obligation is not discharged from a step in scope" — NOT A BUG

**Status: RESOLVED 2026-11-04. There is no engine defect here.** The investigation is kept
because four plausible theories were ruled out along the way, one unrelated latent bug WAS
found and fixed, and the measurement technique is worth reusing.

## The answer

The failing obligation comes from the **discharged conclusion**, not from the accelerant.

A `std.debug.print` in `requireKnown`, reporting the proposition, the lookup block and the
SOURCE OFFSET, settles it in one run of the minimal repro:

```
[guard-miss] prop=19 'invertible(inverse(f))' at kb=1 loc=1400 entries=7
    SAME TEXT taught: prop=19 block=2 step=2
```

- `prop=19` at BOTH the miss and the teach — the term matches; hash-consing is fine.
- Taught at **block 2**, looked up at **block 1**. `ancestorOrSelf(2, 1)` is false: block 2 is
  a CHILD of block 1, so `lookup` correctly declines.
- **`loc=1400` is inside the `@conclusion-impl` step** — the `[by discharge]`, not the
  accelerant step at all.

So this is the documented rule working as designed: **a guard on a term in a DISCHARGED
CONCLUSION must be met from the antecedent**, because the conclusion is elaborated in the
parent block, outside the `assume` whose hypothesis proves it. The fix is authorial — state
the guard as an antecedent — exactly as it was for `sqrtMulNonneg`, `sqrtMonotone`,
`theConstructionDropsADegree` and `theProductIsASingleScaling` during the `recip`/`sqrt` work.

**The accelerant was a red herring.** It looked implicated because the error's reported
position is the accelerant step's, while the obligation originates in a later discharged
conclusion mentioning the same term.

## Process note, worth more than the conclusion

I proposed four locations and was wrong about every one, each time from reading code rather
than measuring: block visibility, alpha-equivalence, the statement path's antecedent teaching
(which already works, `Elab.zig:308`), and the accelerant's synthetic-obligation route. One
`std.debug.print` reporting `loc` answered it immediately. **When a guard obligation looks
misplaced, print the proposition, the lookup block and the source offset first** — the offset
alone would have ended this in five minutes.

The instrumentation, for reuse — in `Elab.requireKnown`, just before `misses.append`:

```zig
const rendered = self.renderProp(prop) catch "?";
std.debug.print("[guard-miss] prop={d} '{s}' at kb={d} loc={d}\n",
    .{ @intFromEnum(prop), rendered, @intFromEnum(self.known_block), loc });
for (known.entries.items) |t| {
    const r2 = self.renderProp(t.prop) catch "?";
    if (std.mem.eql(u8, r2, rendered))
        std.debug.print("    SAME TEXT taught: prop={d} block={d} step={?d}\n",
            .{ @intFromEnum(t.prop), @intFromEnum(t.block), t.step });
}
```

## MINIMAL REPRO

`drafts/accelerant-guard-discharge/specialize-refined-arg.b4m` — 30 lines, expected to fail:

```2b4m
sort Fn
pred invertible(f: Fn)
sort InvFn = Fn where invertible
func inverse(f: Fn) => Fn requires invertible(f)
axiom invInvolution: forall a: InvFn; inverse(inverse(a)) = a   // over the REFINED sort

theorem doubleInverseAtAnFn: forall f: Fn; invertible(f) -> inverse(inverse(f)) = f
proof
  … assume invertible(f) {
      @f-is-invertible | invertible(f) [by hypothesis given-invertible]
      @the-double-inverse |
        inverse(inverse(f)) = f
        [using specialize invInvolution(f) f-is-invertible]    // <- unproved obligation
```

**Depth is not the issue** — this is the shallowest possible case: the guard is the enclosing
assume's own hypothesis, restated two steps above the failure.

**The contrast that localizes it:** adding a step that writes `inverse(f)` directly, justified
`[by reflexivity]`, discharges FINE. An author-written term is checked against `known` by
`Elab.requireKnown`; only the accelerant path fails. That rules out everything about the
proposition, the block, and the term, and points squarely at the synthetic-obligation route
below.

## A REAL bug found on the way, and fixed

`Prove.settleMisses` (`:1213`) only ever attempted to SETTLE a miss when a model transfer was
active:

```zig
for (misses) |m| {
    if (self.model != …universe) {              // ← only under a model
        if (try self.dischargeGoal(kb, m.loc, m.prop)) |sref| { … continue; }
    }
    self.ctx.sink.add(… "unproved obligation: …");   // otherwise: straight to the error
}
```

In an ordinary proof a miss went to the diagnostic **without re-checking `known`** — even
though a miss is recorded while a term is elaborated, and an accelerant's terms are elaborated
during `lowerJustification`, by which point `known` may already teach the guard.

Fixed by re-looking-up first. It is a pure re-check against the same visibility rule
`requireKnown` uses, so it discharges nothing that was not already proved and visible — it
just stops asking before the answer exists. **It did not fix the site above**, so it is a
latent bug rather than this one's cause; kept because it is correct.

## Why SIMPLIFY-ISSUES.md is still open

This resolution does NOT close `SIMPLIFY-ISSUES.md`. That file's case is different: a guard
proved by a step in scope, owed by a term the TACTIC GENERATED, inside the same block — not a
discharged conclusion. It was observed on `sub(sub(i,j), k)` owing `j <= i`, and its
explicit-steps workaround was measured as necessary. Whether it has the same "wrong block"
character or is a real defect is unsettled; apply the instrumentation above to its repro
before theorising.

## Why it matters

De-totalization makes guarded functions normal rather than exceptional, and accelerants are
used everywhere. Every guarded operation whose term lands under a `simplify`, `chain`,
`tautology` or `specialize` hits this, and the author's only recourse is to hand-expand the
tactic into 5–6 explicit steps — on formulas that in `alternating-identities.b4m` are already
eight lines wide.

**Measured cost on the `function.inverse` de-totalization:** the ordinary pattern (derive the
invertibility fact inside every `fix`, outside every `assume`, so it serves the whole nesting)
is ~12 lines and worked 9 times out of 9. The sites that hit THIS bug cannot be fixed that
way at all. So the bug is what separates a mechanical pass from an open-ended one.

## What a fix must preserve

The `e.known = null` in `syntheticObligations` is correct and must stay: a synthetic schema is
registered globally and instantiated by name, so it cannot depend on one call site's context.
The obligation must remain an ANTECEDENT of the synthetic. The fix belongs at the
discharge end — `withGuardPremises`/`dischargeGoal` — where the caller's context is legitimately
available, and where the code already tries.

## Related

- `SIMPLIFY-ISSUES.md` — the author-facing symptom, with the explicit-steps workaround and a
  second instance (`sub(sub(i,j), k)` owing `j <= i` in the old associativity file).
- `drafts/guard-relativization-bug/` — the earlier positional-matching fix in
  `withGuardPremises`, same function, different failure.
- `[[no-totalizing-functions-in-std]]` — why guarded functions are now the norm.
