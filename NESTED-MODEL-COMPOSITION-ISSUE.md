# An incomplete model discharge reports as a sort mismatch in an unrelated file

**Status: FIXED 2026-11-17.** Both failure shapes now name their cause AND their fix. Gated by
`tests/cases/model/composed/` (a three-layer composition, which `std` does in 40 places and
had no test for). One item remains open: listing a model's obligations up front, below.

**When you transfer a theorem whose own proof is a transfer, the outer model must discharge
every axiom the INNER proof reaches — not only the axioms its statement mentions.** That is
correct behaviour. The defect WAS the diagnostic, which said nothing about the missing
discharge; it now names it, and the fix below records how.

## The failure mode

`std/rational/polynomial.b4m`'s `theMonomialShift` cites
`fieldpoly.theMonomialShiftsEveryCoefficient`, which is itself a one-line transfer of
`ring_mono.aMonomialShiftsEveryCoefficient`. `RationalPolynomials` mapped the polynomial
symbols but omitted the F-level algebra facts that `FieldPolyModelsRingPoly` discharges onto
`ring_poly` — `addZeroLeftF`, `mulAddDistribLeftF`, `addIsAssociativeF` and five more.
Supplying those eight lines fixed it.

Omitting such a discharge does not say *"undischarged axiom"*. It surfaces far away, as a
sort mismatch inside the SOURCE theory's own proof — a file the author may never have opened.

## What was done

**(1) DONE — the diagnostic names the cause.** Two sibling failures, since "the model does not
map it" has two shapes, and they take different fixes:

| shape | where | the message |
|---|---|---|
| undischarged AXIOM | `Prove.zig`, schema-instance value-param check (`322c31a`) | "this step cites a fact the model does not discharge … add that fact's `<-` obligation" |
| unmapped SYMBOL | `Elab.zig`, call-argument check | "'mop' is not mapped by the model … add its `:` mapping" |

Both use the same test, which needs no bookkeeping: the proof is a transfer, and the model
maps the sort the site WANTED onto the sort it GOT. Only the overlay relates a pair that way,
so the mismatch IS the unmapped entity. Scoped to fire only under a model and only on that
exact pair, so a genuine type error is untouched — the whole suite is unchanged apart from
the fixtures.

Composition is what makes the SYMBOL half the common case: the callee is often a middle
layer's symbol the outer model never mentioned.

## What a fix should still do

1. **Consider listing a model's obligations.** A `debug model <Name>` printing what a model
   must discharge for a given citation would turn this into a checklist; the information is
   all present at elaboration time.
2. Composition itself needs no change — `std` composes models routinely (40 citations whose
   source theorem is itself a transfer: ℚ → F → ring, and the same for ℝ and ℂ).

## Also affected

A ℤ[x]-onto-a-cut-of-ℚ[x] model (`sort IntPolyCut = QPoly where hasIntegerCoefficients`) hits
the same pattern: the sort mapping is accepted, then failures surface one unmapped symbol at a
time. Not carried to completion, so `std/rational/gauss-cut.b4m` still duplicates ℤ[x].

Related: the same family of defect, where the guard is owed by a tactic's GENERATED terms
rather than by author-written ones, was fixed in `Prove.syntheticObligations` (`43f63f3`) —
the obligation becomes a stated antecedent the call site discharges. Gated by
`tests/cases/tactics/guard/`.
