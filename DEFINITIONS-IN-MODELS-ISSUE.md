# Definitions in models — CLOSED

**Status: RESOLVED 2026-11-03.** A definition block's clause set can now discharge a model
obligation, and the polynomial layers state their operations as definitions rather than as
bare axioms. Kept as the record of what the gap was and what the rule turned out to be.

## The gap, as originally diagnosed

A `model`'s `<-` discharge required a NAME, and a definition block's clauses have none — the
parser publishes each as `definition{<symbol>}{<arm>}`, a spelling deliberately unreachable
from source. So a theory that participated in a model had to write its definitions as bare
axioms, and `--axioms` then listed them beside genuine assumptions.

## What the diagnosis got WRONG

The original write-up proposed naming the discharging clause on the TARGET side:

```2b4m
fieldpoly.addPolyCoeff <- definition(0) raddP     // the proposed fix
```

That is the wrong half of the problem. The shape the corpus actually hits is that **both
sides are definitional**: F[x]'s `convolutionZero` is a definition in all but keyword, and so
is ℝ[x]'s. Counted on `RealPolynomials`, 43 of 48 discharges are definitional-on-definitional;
only 5 (`polyExtensionality`, the two `degree` constraints, the `const` coefficient equations)
pair a definition against a genuine axiom.

Fixing only the target side leaves the source's obligation nameless, so the model cannot
mention it at all — the mapping is rejected as *"'base.sdbl' is a sort or symbol, not an
axiom"* and the transfer dies. `drafts/model-composition/defsrc.b4m` + `defsrc2.b4m` is the
probe that shows it.

## The rule, as settled

> **A definitional axiom is overloadable only by another definition.**

`base.defsymbol <- tgt.defsymbol` names two SYMBOLS. The symbol stands for its whole
obligation set, and the clauses pair ARM FOR ARM: clause 0 discharges clause 0, clause 1
clause 1. Both sides must be definition blocks, and must have the same number of clauses.

**The pairing is deliberately not shape-checked at the model.** A mismatched pair is caught
at the first citation, where the diagnostic can show both formulas (`step claims X but the
axiom derives Y`); re-deriving that check at the model site would duplicate it and say less.

Three rejections, each naming the rule:

| written | diagnosed |
|---|---|
| target is a bare `func` + named axiom | `'madd' discharges the definition 'base.nadd', so it must itself be a definition block (a definitional axiom is overloadable only by a definition)` |
| clause counts differ | `'madd' has 1 definition clause(s) but 'base.nadd' has 2 — a definitional discharge pairs them arm for arm` |
| symbol with no clauses at all | `'source.op' is a symbol with no definition clauses, so there is nothing to discharge — map it with `:`, not `<-`` |

Gates: `tests/cases/model_definition_{source,discharge,bad,arity_bad,cite}.b4m`. The
happy-path fixture transfers a theorem resting on EACH arm, so a mis-paired discharge fails
rather than passing by luck.

## The other direction: CITING a source clause

`[using model(M) definition(N) src.f]` cites one clause of a source definition, for a target
that does NOT overload it — an opaque local `func` with no clauses of its own:

```2b4m
theorem theZeroClauseTransfers: forall b: M; madd(MZ, b) = b
proof
  @conclusion | forall b: M; madd(MZ, b) = b
    [using model(Mod) definition(0) base.nadd]
qed
```

Since nothing local replaces it, the source clause IS an assumption the citing file inherits,
and `--axioms` reports it — as a DEFINITION, attributed to the source's file. That is the
honest reading, and the contrast with the discharge direction is the point: discharge
substitutes the local clause and reports THAT, citation inherits the source's and reports it.

## The shim, and why it is needed

`specialize` resolves its head BY NAME, and a clause has none. So each converted clause keeps
a one-line theorem under the name it had as an axiom:

```2b4m
theorem convolutionZero: forall p, q: Poly; forall j: Nat;
  convolution(p, q, j, ZERO) = mulR(coeff(p, j), coeff(q, ZERO))
proof
  @conclusion | … [by definition(0) convolution]
qed
```

These add no assumption — every one is proved from the clause it names. They are what let the
conversion leave ~140 existing `specialize` citations untouched.

## What it was worth

Reported ASSUMPTIONS per layer, before and after (definitions are now disclosed separately):

| file | before | after | of which its OWN |
|---|---|---|---|
| `std/ring/polynomial.b4m` | 49 | 23 | 9 |
| `std/field/polynomial.b4m` | 57 | 25 | 7 |
| `std/real/polynomial.b4m` | 46 | 19 | **3** |
| `std/rational/polynomial.b4m` | 67 | 33 | 8 |
| `std/integer/polynomial.b4m` | 50 | 42 | 4 |
| `std/integer/mod-n-polynomial.b4m` | 37 | 34 | 4 |

(Measured, both columns, with `check --axioms <file> | grep -vc DEFINITION`. The ℤ layers
move least because most of what they rest on is ℤ's own ring and order theory, which this
change does not touch.)

ℝ[x] is the clearest case: three own assumptions, all legitimate, and everything else
inherited from ℝ/ring/Peano below it. F[x]'s model block also shrank — 26 per-clause `<-`
lines collapsed to 13 symbol lines.

## What stays an axiom, correctly

- `polyExtensionality` — the sort's equality criterion, not a computation.
- `degreeIsALeadingIndex`, `degreeBoundsTheCoefficients` — these CONSTRAIN an opaque
  `func degree` rather than computing it, and one is deliberately SILENT about
  `degree(ZEROP)` (Judson's degree −∞, left unconstrained). No definition block can express
  "undetermined here".
- a `const`'s coefficient equations (`ZEROP`, `ONEP`) — a `const` is uninterpreted and takes
  no clauses.
- **anything with an INNER quantifier.** A clause binder's sort is inferred from its first
  argument-position use, so `degreeAtMostMeaning`, `qIsMonic`, `isZeroOfMeaning` and the
  integer-coefficient predicates fail with `cannot infer the sort of 'i'`. These stay axioms
  unless clause binders gain declared sorts.

## KNOWN GAP: an alias cannot discharge a definitional obligation

**Not yet fixed; do it if it bites again.** `base.f <- localAlias` is refused —

```
error: 'hnz' discharges the definition 'base.gnz', so it must itself be a definition block
       (a definitional axiom is overloadable only by a definition)
```

— even when `pred hnz = base.gnz` aliases a definition block. The cause is mechanical, not
mathematical: `definitionArmCount` re-mangles the TOKEN'S OWN name, so for the alias it probes
for `definition{hnz}{0}`, which does not exist — the clause was published as
`definition{gnz}{0}` in the origin file. The arm count comes back 0 and the discharge is
refused.

**The fix:** resolve the token to its ORIGIN declaration before probing. Alias resolution is
identity-by-origin everywhere else in the engine (see the `alias-collapse` design), so the
probe is the odd one out.

**The workaround, which is what `std/real/units.b4m` does:** name the origin on the discharge,
qualified — `field_order.nonzero <- real.nonzero` rather than `<- nonzero`. Works today and
reads fine, so this is a convenience gap rather than a blocker.

Repro: `drafts/model-composition/aliasdisch.b4m`.

## Engine notes for whoever touches this next

- The mangling now lives in one place: `InternPool.definitionClauseName` /
  `definitionClauseParts`. Four call sites re-derived it independently before.
- `ProveTask`'s "reference not found" demangles, so no diagnostic ever prints
  `definition{f}{7}` — it reads *"'f' has no definition clause 7"*.
- `definitionArmCount` takes an ALREADY-RESOLVED file on purpose. Resolving it inside would
  demand the declaring file's parse for every `<-` source, definitional or not, pulling other
  files' parses earlier and perturbing the engine's schedule corpus-wide.
- **The bug worth knowing about:** an early draft added a suspend INSIDE the obligations loop.
  That made every existing model resolve one obligation per engine run instead of all at once
  — `NatIsOrdered` went from 4 runs to 9, and `tests/cases/chaos_replay.b4m`'s pinned citation
  count moved 2418 → 2438. Nothing else caught it; the verdict was green throughout. If you
  add a mid-loop early return here, re-measure that fixture.

Related: `CONVENTIONS.md` (definition blocks), `agents/2b4m-cheatsheet.md`,
`NESTED-MODEL-COMPOSITION-ISSUE.md`.
