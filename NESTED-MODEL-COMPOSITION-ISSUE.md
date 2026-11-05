# An incomplete model discharge reports as a sort mismatch in an unrelated file

**When you transfer a theorem whose own proof is a transfer, the outer model must discharge
every axiom the INNER proof reaches — not only the axioms its statement mentions.** That is
correct behaviour. The defect is the DIAGNOSTIC.

## The failure mode

`std/rational/polynomial.b4m`'s `theMonomialShift` cites
`fieldpoly.theMonomialShiftsEveryCoefficient`, which is itself a one-line transfer of
`ring_mono.aMonomialShiftsEveryCoefficient`. `RationalPolynomials` mapped the polynomial
symbols but omitted the F-level algebra facts that `FieldPolyModelsRingPoly` discharges onto
`ring_poly` — `addZeroLeftF`, `mulAddDistribLeftF`, `addIsAssociativeF` and five more.
Supplying those eight lines fixed it.

Omitting such a discharge does not say *"undischarged axiom"*. It surfaces far away, as a
sort mismatch inside the SOURCE theory's own proof — a file the author may never have opened.

## What a fix should do

1. **Report the missing discharge where it happens.** When a transfer's re-elaboration reaches
   a symbol or axiom the active model does not map, say so — naming the model, the unmapped
   name, and the citation being elaborated — instead of letting it fall through to a sort check
   in an unrelated file.
2. **Consider listing a model's obligations.** A `debug model <Name>` printing what a model
   must discharge for a given citation would turn this into a checklist; the information is
   all present at elaboration time.
3. Composition itself needs no change — `std` composes models routinely (40 citations whose
   source theorem is itself a transfer: ℚ → F → ring, and the same for ℝ and ℂ).

## Also affected

A ℤ[x]-onto-a-cut-of-ℚ[x] model (`sort IntPolyCut = QPoly where hasIntegerCoefficients`) hits
the same pattern: the sort mapping is accepted, then failures surface one unmapped symbol at a
time. Not carried to completion, so `std/rational/gauss-cut.b4m` still duplicates ℤ[x].

Related: `SIMPLIFY-ISSUES.md` — the same family, where the guard is owed by a tactic's
generated terms rather than by author-written ones.
