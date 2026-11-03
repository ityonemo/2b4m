# Nested guarded models cannot compose — and that is an engine defect

**Status: OPEN. Diagnosed 2026-11-03, not fixed.** The user's ruling on finding it:
"if that doesn't work then we've done something wrong in 2b4m."

## The one-line statement

Two models that each transfer correctly cannot be CHAINED. 2b4m re-checks an inner transfer
in the outer model's sort space instead of composing the two interpretations, so a transfer
whose source theory was itself reached by transfer is inexpressible.

## The concrete case that surfaced it

AATA's Gauss's Lemma (§17.3, Theorem 17.14/17.15) needs ℤ[x] as a SUBRING OF ℚ[x] — the
statement "f ∈ ℤ[x] factors over ℚ ⟹ it factors over ℤ" quantifies over objects that are
simultaneously a ℤ[x] element and a ℚ[x] element. 2b4m has no sort subsumption and the
number-tower refactor deliberately dropped the `from*` coercions, so two separate sorts
cannot express it.

The natural construction is a cut plus a model:

```
sort IntPolyCut = QPoly where hasIntegerCoefficients   // ℤ[x] inside ℚ[x]
model IntegerPolynomialsOnTheCut {
  intpoly.IntPoly: IntPolyCut                          // ℤ[x]'s sort onto the cut
  intpoly.Int:     Integer                             // ... and its COEFFICIENTS onto ℚ's
  ...
}
```

so that `std/integer/polynomial.b4m`'s finished ℤ[x] corpus lifts onto the cut.

**Why it fails.** `std/integer/polynomial.b4m:27` is `sort Int = integer.Int` — ℤ[x]'s
coefficient sort is hard-aliased to `std/integer.b4m`'s `Int`. So mapping `IntPoly` onto a
cut of `QPoly` forces mapping `icoeff`'s result sort too: `integer.Int: Integer`, where
`Integer = Q where isInteger` (`std/rational.b4m:1088`). That is exactly the existing guarded
model `IntegersInRational`. The polynomial transfer therefore becomes a NESTED guarded
transfer — ℤ[x] → cut-of-ℚ[x], whose coefficient leg is itself ℤ → cut-of-ℚ — and it dies as

```
expected sort 'Int', got 'Q'
```

The direction we want it most is the direction that needs composition, because most
interesting ℤ[x] theorems were themselves obtained by transferring `ring_poly`. So the chain
is three deep: `ring_poly` → ℤ[x] → cut-of-ℚ[x].

## Why "reprove on the cut" is not an acceptable permanent answer

It is the current workaround (see `[[guarded-model-transfer-fixed]]`, which recommends it),
and it does work: ℚ[x] as a whole is a ring, so `RationalPolynomialsOverARing` is UNGUARDED
and composes freely; every generic R[x] theorem lands on `QPoly` with no guard, and
`hasIntegerCoefficients` rides along as an ordinary predicate rather than a sort refinement.

But the cost is structural duplication, which is the thing the model system exists to prevent.
`std/rational/gauss-cut.b4m` is ~3000 lines of ℤ[x]-inside-ℚ[x] that cannot cite the
standalone ℤ[x] for anything. Worse, the duplication is invisible to `--library`: both files
check green, and nothing reports that they are the same mathematics.

## What a fix has to do

The model mechanism already says a model is a FULL OVERLAY over the universe
(`[[model-source-theory-only]]`), and that one block may map several sibling namespaces at
once. Composition is the missing piece of exactly that story: given `M1: A → B` and
`M2: B → C`, a citation `[using model(M2) ...]` of a theorem whose proof used
`[using model(M1) ...]` should interpret the inner transfer THROUGH M2 rather than re-checking
it in A's sorts.

Open design questions, not yet settled:

- Does composition get named at the citation site (`[using model(M2 . M1) thm]`), inferred
  from the demand graph, or declared once as a composite model?
- Guard relativization has to compose too: a doubly guarded binder owes both memberships, and
  the dischargers live in different files.
- `[[required-on-model-primitive]]`'s "prove-if-modeled" flavor interacts with this — a source
  declaration that is axiomatic standalone and an obligation when modeled needs a defined
  behaviour when it is modeled TWICE.

## Immediate decision taken (2026-11-03)

Per the user, pending a real fix:

1. `std/integer/polynomial.b4m` stays STANDALONE — its own sort, its own corpus. It is the
   honest ℤ[x] and nothing about the cut should contort it.
2. The integer-cut-of-ℚ[x] construction is a SEPARATE construction, renamed to
   **`std/rational/gauss-cut.b4m`** so the filename says it is Gauss's scaffold rather than a
   second ℤ[x]. Its header carries a boxed TEMPORARY note pointing here.

   It STAYS IN `std/`. Moving it to `aata/` was considered and rejected: `std/rational/
   gauss-reduction.b4m` (900 lines) sits between the cut and `aata/17.3` and imports the cut,
   so relocating only the cut would make a `std/` file import from `aata/` — inverting the
   dependency direction and making `check std --library` depend on the textbook tree. Both
   files are single-theorem scaffolding, but they are scaffolding that other `std/` files
   consume, so `std/` is where they belong until the model fix lets them collapse.

Related: `[[guarded-model-transfer-fixed]]`, `[[model-source-theory-only]]`,
`[[required-on-model-primitive]]`, `[[sort-parameterization-via-model]]`,
`POLYNOMIAL-GENERICIZATION.md`.
