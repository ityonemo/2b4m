# A `definition` keyword — status read from a table, not parsed from a name

PAINPOINTS 16e. `--axioms` reports a definition block's clause as `— DEFINITION` and a
hand-written `axiom` as a plain assumption, even when the axiom's content is purely
definitional. The counts a reader weighs are therefore wrong, on an artifact whose whole
deliverable is an honest assumption count.

Measured instance (`examples/music-of-primes`, 2026-11-20): two definitional axioms sat in a
54-entry `--axioms` report beside 37 cited holes, and the published total was wrong until an
audit of the report caught them.

## Why it happens: definition-ness is INFERRED, hole-ness is RECORDED

That asymmetry is the defect. Both statuses answer "what kind of declaration is this", but
they are carried completely differently:

| status | how the reporter learns it | where it lives |
|---|---|---|
| hole | **recorded** when the decl publishes | `Context.holes_reached`, keyed `(file, loc)` |
| definition | **parsed** out of the mangled name `definition-<symbol>-<arm>` | `InternPool.definitionClauseParts` |

So a definition block's clause gets the status because the synthesizer spells its name a
certain way, and a hand-written axiom can never get it — there is no such name to parse, and
nowhere to record the author's intent.

Two costs, not one:

1. **16e proper.** A definitional axiom is miscounted as an assumption.
2. **A naming coupling.** The checker reads meaning out of a spelling, which is the class of
   problem [[accelerator-naming-couplings]] exists to forbid. Rename the mangling scheme and
   the report silently changes.

### The long form is often FORCED, so this is not a contrived case

A definition block cannot infer a bound variable's sort under a quantifier (PAINPOINTS 16).
Any definitional `iff` whose body quantifies must therefore be written long:

```2b4m
pred noZerosRightOfTheCriticalLine()
axiom noZerosRightMeansNoZeroIsRight:
  noZerosRightOfTheCriticalLine() iff
  (forall r: Zero; isNonTrivialZero(r) -> (not rightOfTheCriticalLine(r)))
```

PAINPOINTS 16 pushes the author out of the block form; 16e then mislabels what they wrote.
The two compose, which is why fixing 16 alone would also dissolve this — see *Alternatives*.

## The design: a third surface variant over one kernel kind

**The hole/axiom relationship is the template, and it is a THREE-layer split** (verified in
the source, not inferred):

| layer | what it knows | evidence |
|---|---|---|
| surface AST | `axiom` and `hole` are distinct `Decl` variants | `ast.zig:294` `hole: Axiom` |
| **kernel** | **only `.axiom` vs `.theorem`** | `InternPool.zig:323` `Kind = enum { axiom, theorem }` |
| Context side tables | which `(file, loc)` was declared a hole | `Context.zig:195` `holes_reached` |

The kernel is completely innocent of status. `kernel.zig:794` mints every assertion as
`.axiom`, and `cite` is kind-agnostic (`ast.zig:382` collapses `.axiom, .hole` into one arm).
That is what makes a status tier safe to add: **it cannot weaken soundness, because the
trusted core never learns it exists.** The only thing at stake is what the reporter prints.

So `definition` slots in exactly parallel:

| | surface | kernel | status |
|---|---|---|---|
| `axiom` | own variant | `.axiom` | — |
| `hole` | own variant | `.axiom` | `holes_reached` |
| **`definition`** | **own variant** | **`.axiom`** | **recorded, see below** |

### Syntax

```2b4m
definition noZerosRightMeansNoZeroIsRight:
  noZerosRightOfTheCriticalLine() iff
  (forall r: Zero; isNonTrivialZero(r) -> (not rightOfTheCriticalLine(r)))
```

Identical to `axiom` in every respect but the keyword. Cited the same way
(`[by cite noZerosRightMeansNoZeroIsRight]`), aliased the same way (`fact X = ns.y`), and
reported as `— DEFINITION`.

**Deliberately NOT a new `cites`-style modifier on `axiom`.** `hole` earned its own keyword
rather than becoming `axiom … draft`, and for the same reason: the status is a claim about
what the declaration IS, which belongs where the reader's eye already is.

### Where the status is recorded, and read

The two reporting sites want different reads, because they have different things in hand:

| site | has | should read |
|---|---|---|
| `root.zig:axiomSite` | a fact `Index`, resolved to `(file, loc)` | the side table |
| `root.zig:collectUnusedAxioms` | the AST `decl` itself | `decl == .definition` directly |

The second needs no table at all — it already walks `ctx.parsed`, so the variant is visible.

For the first, extend the existing status table rather than adding a parallel one.
`HoleDecl` is already `{ name, file, loc, cites }`; `holes_reached` and a hypothetical
`definitions_reached` would be structurally identical, and two tables scanned by the same key
invite the two from drifting. Prefer **one table with a tag**:

```zig
pub const DeclStatus = enum { hole, definition };
status_reached: std.ArrayList(struct { status: DeclStatus, decl: HoleDecl }) = .empty,
```

with `recordHoleReached` kept as a thin wrapper so existing callers do not move.

### What the publish arm must and must not do

`ProveTask.publish`'s `.hole =>` arm (`ProveTask.zig:255-272`) does five things. A
`.definition =>` arm copies four and drops one:

| | hole | definition | why |
|---|---|---|---|
| publish the leaf as `.axiom` | yes | **yes** | the kernel sees one kind |
| record the status | `holes_reached` | **`status_reached`, tagged** | the reporter's join key |
| `recordAxiomOrigin` | yes | **yes** | `--axioms` needs `file:line` |
| `recordAxiomTaint` | yes | **yes** | see below — `--library` depends on it |
| `recordHoleTaint` | yes | **NO** | a definition is not a hole; nothing should enter a `--draft` blast radius for it, and default `check` must NOT reject a file for having definitions |

**The taint choice is forced, not a judgement call.** `--library` treats an unused definition
as an ERROR, not a pass — `main.zig:726` says so in as many words ("A definition is as much a
library's SURFACE as an assumption is"). So definitions must keep flowing through the same
used/unused machinery as axioms, which means `axiom_taint` stays. Only the hole taint goes.

## What this does NOT do, and the honest risk

The tier is **self-asserted**. Nothing checks that a `definition` is definitional, any more
than anything checks that an `axiom` is citable to the literature. A user can write
`definition` on a substantive assumption and have it excluded from the assumption count.

That is the same trust shape as `axiom` itself, and the mitigations are the ones already in
place rather than new machinery:

- **`--axioms` prints the statement, not just the name.** A mislabelled definition is visible
  to anyone who reads what it says — which [[axiom-tracking-plan]]'s own rule already demands
  ("`--axioms` is the deliverable, not the green checkmark").
- **`--library` still requires it to be USED.** A `definition` nothing rests on is an error,
  so it cannot be a quiet parking space.
- **The report separates rather than hides.** A definition is counted apart, not omitted; the
  total still includes it.

What would make the tier *checkable* is a real soundness condition — that the symbol is fresh
and the clause set determines it. That is `DEFINITION-SOUNDNESS-PLAN.md`'s territory and is
explicitly out of scope here. **This plan fixes the REPORTING defect only.**

## Alternatives considered

**Fix PAINPOINTS 16 instead** (let a definition block's clause infer a bound variable's sort
under a quantifier). This would *dissolve* 16e rather than solve it: the long form would stop
being forced, so definitional content would live in blocks and get the status automatically.
Arguably the better fix, and it is strictly more work — it changes elaboration rather than
reporting. **Not mutually exclusive:** doing 16 later would reduce `definition`'s use to the
genuinely-long cases, which is fine.

**A modifier on `axiom`** (`axiom … is definition`, or a `defines` clause). Rejected for the
reason `hole` is its own keyword: the status is what the declaration IS.

**Infer definition-ness from shape** (a single `iff` whose LHS is the declared symbol applied
to distinct binders). Rejected — it would silently reclassify existing axioms, and "looks
definitional" is not the same claim as "is offered as a definition".

## Work

1. `definition` token + `Decl.definition` variant, parsed exactly as `axiom`. Reject
   `definition` where `axiom` is rejected (no local form questions arise: it mirrors `axiom`).
2. `Context`: `DeclStatus` + `status_reached`, with `recordHoleReached` as a wrapper.
3. `ProveTask.publish`: the `.definition =>` arm, per the table above.
4. `root.zig:axiomSite`: read the tagged table; keep the mangled-name test as a fallback so
   definition BLOCKS are unaffected.
5. `root.zig:collectUnusedAxioms`: add `.definition` to the decl filter and set
   `is_definition` from the variant.
6. `fact` aliasing, `--library`'s header rule, and `2b4m fmt` — confirm each treats
   `definition` as it treats `axiom` (they key on the decl, so expect no change; verify).
7. GUIDE: a `### KEYWORD: definition` section and a row in the keyword table.

## Gates

- `zig build test -Doptimize=ReleaseFast`
- `./2b4m check std --library` — theorem count UNCHANGED (this carries no mathematics)
- `./2b4m check aata`
- A new fixture under `tests/cases/` : a hand-written `definition`, asserted to report
  `— DEFINITION` under `--axioms` and to be an ERROR under `--library` when unused.
- **The 16e regression itself**: `examples/music-of-primes`'s two definitional axioms, once
  respelled, must move out of the cited-hole count and into the definition count, leaving the
  total unchanged at 60.
