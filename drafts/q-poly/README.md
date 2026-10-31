# ℚ[x] by modelling — it works, and what it costs

`probe2.b4m` is strict-green: **ℚ[x] exists as its own sort with F[x]'s corpus transferred
onto it.** `probe.b4m` is the failed first attempt, kept because its error message is the
whole lesson.

## I was wrong about why the first attempt failed

I said: *"`sort F = field.Field` is an alias, so `Poly` is declared over the abstract field
and can't be re-pointed at `Q` by a model."*

**That is false, and aliasing has nothing to do with it.** The real rule is the one the R[x]
→ F[x] transfer already taught earlier in the session:

> A model must map **every symbol the transferred proof mentions** — not just the ones in the
> theorem's statement.

`probe.b4m` mapped `field.Field → Q` and the field axioms, but left `fieldpoly`'s own `Poly`
and `coeff` unmapped. `coeff(p, i)` returns `F`, so re-checking the proof hit
`expected sort 'Q', got 'Field'`. The existing `FieldPolyModelsRingPoly` block
(`std/field/polynomial.b4m:1482`) shows the correct shape: it maps `ring_poly.Poly: Poly` and
`ring_poly.coeff: coeff` explicitly, alongside the coefficient ring.

## The working shape

`probe2.b4m` declares ℚ[x] as **its own** sort and operations, then maps the whole layer:

```
sort QPoly
func qcoeff(p: QPoly, i: Nat) => Q
const QZEROP: QPoly
func qaddP / qnegP / qmulP

model RationalPolynomials {
  fieldpoly.F: Q              fieldpoly.Poly:  QPoly
  fieldpoly.zeroF: …          fieldpoly.coeff: qcoeff
  fieldpoly.addF:  …          fieldpoly.ZEROP: QZEROP
  …                           fieldpoly.addP:  qaddP   …
  fieldpoly.polyExtensionality <- qPolyExtensionality
  fieldpoly.addPolyCoeff       <- qAddPolyCoeff
  fieldpoly.negPolyCoeff       <- qNegPolyCoeff
}
```

Each **axiom** of `field/polynomial.b4m` that a transferred proof touches must be restated
over ℚ[x] and discharged. The probe needed three; the file has **23 axioms** in total, so a
full ℚ[x] restates however many the target corpus reaches.

Two mechanical notes the engine enforced:

- `model` maps **axioms only** — it rejected `field.recipMulLeft` with *"is a theorem — it
  materializes through the mapped axioms, so drop this mapping"*. Useful: the error names the
  rule rather than just failing.
- Transfers **chain**, and a chained transfer re-checks the inner one. `polyAddIsCommutative`
  is itself proved by `model(FieldPolyModelsRingPoly)`, so carrying it to ℚ[x] re-checks that
  inner transfer and demands `ring_poly`'s layer as well. Theorems proved *directly* in
  `field/polynomial.b4m` (like `subPolyCoeff`) travel with only the field+polynomial layer.

## What this means for Lemma 17.12

The ℤ-in-ℚ half needs **no new work at all**: `std/rational.b4m:905` already carves
`sort Integer = Q where isInteger` and runs `model IntegersInRational`, transferring ℤ's
whole corpus onto the cut. The header documents the idiom.

So 17.12's two stated obstacles both dissolve:

| claimed obstacle | reality |
|---|---|
| family gcd | built — `std/integer/family-gcd.b4m`, relationally |
| ℚ[x] with integer coefficients | the mechanism works (`probe2.b4m`); ℤ-in-ℚ already exists |

What remains is **volume, not mechanism**: restating the axioms of
`std/field/polynomial.b4m` over ℚ[x], then transliterating his proof (clear denominators
over the index range, divide by the family gcd, reduce `d/(c_0⋯c_n)` to lowest terms). The
`c_0 ⋯ c_n` product has `std/integer/product.b4m`, and the gcd has `family-gcd.b4m`.

**Next step if picked up:** build `std/rational/polynomial.b4m` as the probe does, mapping
the layer and discharging the axioms the 17.12 proof actually reaches — not all 23 up front.
