# Bézout on ℚ's integer cut — what's measured, what's left

**Status 2026-11-01.** Chapter 17's remaining chain is `division algorithm → Bézout →
17.14 → 17.15`, all on ℚ's `isInteger` cut. Euclid's Lemma itself is DONE
(`euclidFromBezoutOnTheCut`, 8 axioms, no holes) — it takes the Bézout certificate as a
hypothesis, so it needed none of this.

## Measured, not assumed

| claim | verdict |
|---|---|
| `euclidFromBezout` needs `div`/`mod`/`gcd` mapped | **FALSE.** 15 axioms, all mapped by `IntegersInRational`; `divides` is a `define` (a macro — nothing to map). My earlier cost estimate read the FILE's symbol table instead of the theorem's dependency set. |
| so it transfers | **NO**, but for an unrelated reason: its proof uses bare `[using polynomial]`, whose hardcoded rule set cites ring lemmas with SOURCE-SPACE formulas. Under a transfer the cite claims a guard-free universal while the resolved theorem is relativized. |
| `lessThanIntro`/`lessThanElim` block the cut | **FALSE.** `IntegerOrderOnTheCut` already discharges both (2026-10-30) — that was the hard part and it is done. |
| `coprimeBezout` transfers | **NO.** `std/peano.b4m:857: expected sort 'Int', got 'Q'` — the documented nested-transfer wall (ℕ → ℤ's NonNeg → ℚ's isInteger cannot compose). Same for `divisionAlgorithmExists`. |

So the blocked thing is specifically the **construction** (Bézout, division algorithm), not
the *consequence* (Euclid). Both must be proved natively on the cut.

## The route

1. **Division algorithm on the cut** — `∀a,b; 0 < b → ∃q,r; a = b·q + r ∧ 0 ≤ r < b`.
   Engine: `naturalWellOrdering` from `std/rational/natural-wellordering.b4m`, well-ordering
   `{a − b·q ≥ 0}`. ℚ's cut is discrete (`theIntegersInRationalAreDiscrete`), which is what
   makes the least element behave.
2. **Bézout on the cut** — well-order the positive values of `a·r + b·s`, take the least `g`;
   division-with-remainder shows `g` divides both; quantified coprimality then forces `g = ±1`.
3. **17.14** — feed the certificate to `euclidFromBezoutOnTheCut` against the two end-splits
   already proved (`theClearedSumSplitsOffTheConstantTerm` / `…TheLeadingTerm`), which
   deliver `r | a_0·s^(n+1)` and `s | a_n·r^n`.
4. **17.15** — the minimal-index argument, sharing step 3's Euclid use.

## Engine fix landed on the way

`f41c60f`: `produceSimplify` never called `paramGuards`, so a `simplify` whose rewrite set
mentions a lemma quantified over a model-refined sort could not transfer AT ALL. The
mechanism existed but was wired only into `finishReorder`. Also `paramGuards` read the
SOURCE binder's refinement, which is `none` when the model is what introduces it.

**Still open, same family:** the `polynomial` case above — a cite of a relativized theorem
claiming the unrelativized formula. Different mechanism (citation, not param guard), and
`polynomial`'s hardcoded rule set makes it a design question rather than a one-liner.
