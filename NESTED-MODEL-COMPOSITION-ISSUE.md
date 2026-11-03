# Model composition works — but an incomplete model reports itself terribly

**Status: the original claim in this file was WRONG and is retracted.** What remains is a real
diagnostics problem, demonstrated by a minimal repro, plus the record of how the wrong
diagnosis cost most of a working session.

## What this file used to say, and why it was wrong

It claimed: *"Two models that each transfer correctly cannot be CHAINED … a transfer whose
source theory was itself reached by transfer is inexpressible."*

That is false. **Models compose, and `std` has relied on it all along.** A scan on 2026-11-03
found **40 composed-model citations** already in the library — each citing a theorem whose own
proof is nothing but a transfer:

| file | example |
|---|---|
| `std/rational.b4m:327` | `model(RationalField) field.mulZeroLeft`, and `field.mulZeroLeft` is itself `model(RingIsField) ring.mulZeroLeft` |
| `std/real.b4m:332` | the same chain for ℝ |
| `std/complex.b4m:178` | the same chain for ℂ |
| `std/field/order.b4m:233` | ordered fields over `field` |
| `std/ring/first-isomorphism.b4m:386` | `ring.additiveInverseUnique` |

So ℚ → F → ring is routine, two hops, green. The question *"why doesn't it work through
F[x]?"* had the right premise: it should, and it now does.

## What the problem actually is

**When you re-transfer a theorem whose own proof is a transfer, the outer model must discharge
every axiom the INNER proof reaches — not only the axioms its statement mentions.**

The failing case was `std/rational/polynomial.b4m`'s `theMonomialShift`, citing
`fieldpoly.theMonomialShiftsEveryCoefficient` (itself a one-line transfer of
`ring_mono.aMonomialShiftsEveryCoefficient`). `RationalPolynomials` mapped the polynomial
symbols but omitted the F-level algebra facts that `FieldPolyModelsRingPoly` discharges onto
`ring_poly` — `addZeroLeftF`, `mulAddDistribLeftF`, `addIsAssociativeF` and five more.
Supplying those eight lines fixed it, and the F[x] route then worked exactly as expected.

**The diagnostic is the defect.** Omitting such a discharge does not say *"undischarged
axiom"*. It surfaces far away, as a sort mismatch inside the SOURCE theory's own proof:

```
std/ring.b4m:143:39: error: expected sort 'Field', got 'Q'
```

`ring.b4m:143` is a `specialize addZeroLeft(ZERO)` step inside `ring.mulZeroLeft`'s proof — a
file the author never cited, in a theory two layers down. Nothing in the message names the
model, the missing discharge, or the citation being elaborated.

## The minimal repro

`drafts/model-composition/` — toy theories, ~40 lines each, no polynomial machinery:

- `base.b4m` / `mid.b4m` / `top.b4m` — a three-level chain where the middle theorem is
  transfer-proved and the top re-transfers it. **Passes.** This is the control that disproves
  the original claim.
- `base2.b4m` / `mid2.b4m` / `top2.b4m` — the same with two sorts, where `top2`'s model
  discharges only the axiom its statement mentions. **Failed** with
  `expected sort 'MScalar', got 'TScalar'` reported inside `base2.b4m`; adding
  `mid2.msopZeroLeft` and `mid2.msopIsCommutative` to `top2`'s model makes it pass. (Both
  discharges are present now, so the directory checks green; delete either to see the bad
  diagnostic.)
- `base3.b4m` / `mid3.b4m` / `top3.b4m` — the bisection ladder used to find it: single sort,
  then two sorts, then `by cite`, then `by rewrite`, then an unused axiom. All pass, which is
  how the discharge set was isolated as the only remaining variable.

## What a fix should do

1. **Report the missing discharge where it happens.** When a transfer's re-elaboration reaches
   a symbol or axiom the active model does not map, say so — naming the model, the unmapped
   name, and the citation being elaborated — instead of letting it fall through to a sort check
   in an unrelated file.
2. **Consider listing a model's obligations.** A `debug model <Name>` printing what a model
   must discharge for a given citation would turn this from archaeology into a checklist; the
   information is all present at elaboration time.
3. Composition itself needs no change.

## The process lesson, recorded because it was expensive

I asserted "models don't compose" from a single failing site, wrote it up as an engine defect,
and built around it — including re-routing ℚ[x] at `ring_mono` to dodge the F[x] hop. Four
successive hypotheses (alias-collapse, missing `ring` mappings, theorem-vs-axiom leaves,
`ring_poly` alias spellings) were each tested and each wrong. The correct answer appeared only
when the user asked two questions I should have asked myself first: *are we using composed
models in std?* (yes, 40 times) and *shouldn't it work through F[x]?* (yes).

**The rule this suggests: before writing up an engine defect, grep the corpus for the thing
you are claiming is impossible.** If the library already does it, the bug is in your usage.

## Still open elsewhere

A ℤ[x]-onto-a-cut-of-ℚ[x] model (`sort IntPolyCut = QPoly where hasIntegerCoefficients`) was
also blamed on this non-existent defect. Re-tested 2026-11-03: the sort mapping is **accepted**,
and the failures that follow are the same incomplete-discharge pattern, surfacing one unmapped
symbol at a time. It was not carried to completion, so `std/rational/gauss-cut.b4m` still
duplicates ℤ[x] — but the reason is unfinished work, not an engine wall, and that file's header
needs the same correction.

Related: `SIMPLIFY-ISSUES.md` — a separate, still-open diagnostics problem in the same family
(guards owed by a tactic's generated terms rather than by author-written ones).
