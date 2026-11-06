# Polynomial genericization — what the four layers taught, and what to do next

Written 2026-11-02, after building `R[x]`'s negation algebra at the ring layer and transferring
it into `F[x]`. This is a findings document, not a plan: the measurements are real, the
recommendation at the end is a proposal.

## The current shape

| layer | file | lines | theorems | axioms | models |
|---|---|---|---|---|---|
| `R[x]` over a commutative ring | `std/ring/polynomial.b4m` | 2186 | 30 | 18 | 0 |
| `F[x]` over a field | `std/field/polynomial.b4m` | 7325 | 91 | 22 | 1 |
| `ℚ[x]` | `std/rational/polynomial.b4m` | 3253 | 32 | 37 | 3 |
| `ℤ[x]` as a cut of ℚ[x] | `std/rational/integer-polynomial.b4m` | — | 25 | — | — |
| `ℤ[x]` standalone | `std/integer/polynomial.b4m` | 1000 | 11 | 13 | 1 |
| `ℤ_n[x]` | `std/integer/mod-n-polynomial.b4m` | — | 3 | 12 | 1 |

Plus `std/ring/polynomial-leading.b4m` and `std/field/polynomial-associativity.b4m`.

Each carrier re-declares the same primitives — `coeff`, `ZEROP`, `addP`, `negP`, `mulP`, a
`convolution` with its two recursion clauses, `degreeAtMost`, extensionality. That repetition
is **forced** and is not the problem: there are no parameterized sorts, so `Poly` over a
mapped coefficient ring is a different sort from `QPoly`, and a model maps symbols rather than
instantiating a functor. See [[sort-parameterization-via-model]].

The problem is the *theorems*.

## Measurement 1: the duplication is real and it is avoidable

Normalizing theorem names across layers (stripping the `q`/`poly`/`the`/`i` prefixes each
carrier uses), `std/ring/polynomial.b4m` and `std/field/polynomial.b4m` now share **19 names**
— and every one of those is a one-line `using model(FieldPolyModelsRingPoly)` transfer in
`F[x]`. That is the mechanism working as intended.

`ℚ[x]` shares **four**, and none of them is a transfer:

| ℚ[x] theorem | lines of proof |
|---|---|
| `theNegationPullsOutOfTheConvolution` | 161 |
| `theTwoNegationsCancelInAProduct` | 79 |
| `theNegationPullsOutOfTheProduct` | 58 |
| `qMulIsCommutative` | 7 |
| **total** | **305** |

Only 5 of ℚ[x]'s 32 theorems are model transfers at all.

## Measurement 2: it was never a mapping gap

The obvious explanation would be that ℚ[x]'s model is too weak to carry these. **It is not.**
`RationalPolynomialsOverARing` already maps the full `ring` + `ring_poly` vocabulary — 40-odd
lines of `:` and `<-`. I tested the counterfactual directly:

```2b4m
theorem probeTransfer: forall p, q: qpoly.QPoly;
  qpoly.qmulP(qpoly.qnegP(p), q) = qpoly.qnegP(qpoly.qmulP(p, q))
proof
  @conclusion |
    forall p, q: qpoly.QPoly;
      qpoly.qmulP(qpoly.qnegP(p), q) = qpoly.qnegP(qpoly.qmulP(p, q))
    [using model(qpoly.RationalPolynomialsOverARing)
      ring_poly.negationPullsOutOfTheProduct]
qed
```

`OK: 620 declarations, 1 theorems proven`, strict.

So those 305 lines could have been four one-line transfers **the whole time**. The only reason
they were written by hand is that `std/ring/polynomial.b4m` did not yet carry the theorems, and
nobody looked down a layer before inducting.

**This is the finding that matters.** The cost of a missing generic theorem is not "someone
proves it twice" — it is that the second proof is written at the *wrong layer*, by induction,
and then every later carrier faces the same choice again. ℚ[x] paid 305 lines; F[x] would have
paid a comparable amount had the ring layer still been empty when §17.2 needed it.

## Measurement 3: right-hand companions go missing in pairs

Closing AATA §17.2 required four lemmas that did not exist at the ring layer *even though every
left-handed form did*: `polyAddNegRight`, `polyAddZeroRight`, `polyMulAddDistribRight`,
`aSumCancelsItsRightSummand`. Each is two lines from its left twin plus commutativity.

The mechanism is clear in hindsight: a layer gets built to satisfy one consumer, that consumer's
proofs happen to be left-handed, and the right forms are never written. The same thing had
happened at the scalar layer — `Ring` had no additive left-swap (`addLeftSwapLocal`), which is
the third argument `assoc_commut`'s explicit form requires, so the AC tactic was unusable over
`Ring` addition.

**Cheap rule:** when adding a directional lemma, add both directions. Two lines each, and the
absence is invisible until it blocks something.

## The hard constraint: `polynomial` is a SCALAR-layer tactic

This is the single most important thing to know before planning polynomial work, and it took a
wrong turn to discover.

`polynomial` binds `add`/`mul`/`ZERO`/`succ` by **well-known name**. Over a carrier whose
operations are `addP`/`mulP`, it reports `the goal has no add/mul structure`. I checked every
use in the corpus: each `using polynomial(...)` sits over `field` or `rational` — the
**coefficient** ring — and not one is over polynomial operations.

So a polynomial ring identity cannot be discharged by a tactic. Judson's one-line

> `b = p − ad = p(1 − ar) + q(−as)`

became four lemmas and about a dozen explicit steps: distribute `a` over the inner sum, split
the negation of a sum, reassociate each term, fold the leading `p` into its coefficient.

**Consequence for any new polynomial layer:** budget for stating distributivity, identity,
associativity and negation lemmas by hand. No accelerant will supply them. This is also why
`polynomial-associativity.b4m` exists as its own file — the associativity identity is a
double-sum reindexing that nothing automates.

A tempting fix is to make `polynomial` accept an operation-name mapping. I have not costed
that, and it interacts with the `--fast` trust boundary (the tactic's decision binds vocabulary
by name precisely so a misbound operator is caught by the certificate, not the decision — see
`design/acceleration.md`). Flagging it, not proposing it.

## What is genuinely carrier-specific

Not everything should move down. Classifying ℚ[x]'s 32 theorems by the vocabulary their proofs
actually cite:

**Genuinely ℚ-specific (stay):**
- `everyCoefficientIsARatioOfIntegers` — cites `everyRationalIsAQuotientOfIntegers`, `recip`,
  `isInteger`. This is ℚ's fraction structure; no ring has it.
- `aPowerCancelsTheReciprocalsPower` — cites `fieldInverse`, `recip`. Field-only.
- `aNonzeroScalingReflectsTheVanishing` / `...TheDegreeBound` — cite `noZeroDivisors`. An
  **integral domain** fact, not a general-ring one. These could live at a domain layer if one
  existed; they cannot live at `ring`.
- the `isInteger`-flavoured cut theorems, and the `clearedSum` family (17.12's machinery).

**Generic, and currently misplaced:** the negation family (measured above), plus five more
confirmed by discharge set rather than by eye — `theNegationsCoefficientFlips`,
`theNegationIsTheMinusOneScaling`, `scalingByAConstantScalesTheCoefficients`,
`theConstantMonomialProductAgreesCoefficientwise`, `negationPreservesTheDegree`. Running
`--axioms` on each returns **zero** field axioms, zero domain axioms, and zero ℚ-cut axioms:
they rest only on ring and Peano facts. Each is a candidate to move down and transfer back.

**The dividing line that actually predicts it:** what the proof *cites*, not what the statement
mentions. A statement over `qcoeff` and `rational.mul` looks ℚ-specific; if its proof only ever
cites ring axioms, it is generic. `--axioms <file> <theorem>` answers this in one command and
should be the test, because the naming does not reveal it.

## The layer that is missing

Three of the misplaced-but-not-ring theorems above need `noZeroDivisors`. That is the signature
of an **integral domain** layer sitting between `ring` and `field`:

- `ring` — has `mulZeroLeft`/`mulZeroRight`, no cancellation.
- *(missing)* `domain` — adds `noZeroDivisors`; gets degree additivity, cancellation, the
  scaling-reflects-a-degree-bound family, "a nonzero multiple has at least the degree".
- `field` — adds inverses.

Several `F[x]` theorems **state** domain facts — `aNonzeroMultipleHasAtLeastTheDegree`,
`aSmallDegreeMultipleIsTheZeroMultiple`, `anEqualDegreeCofactorIsConstant` — and ℤ[x] and
ℤ_n[x] (for prime n) would get them free from a domain layer.

But note what `--axioms` says about the first one: it rests on **`fieldInverse`**, not on
`noZeroDivisors`. As *written* it is a field proof, because inverses were available and were
the shortest route. So moving it down is not a relocation — it is a **re-proof** from the
weaker axiom. That is the real cost of this item, and it is why I am ranking it below the
mechanical moves: the statements are domain statements, the proofs are not.

I have not built this. It is the natural next genericization step and it is *larger* than the
negation work, because degree additivity is where the real content is.

## Recommendation

In priority order, each stated with its evidence:

1. **Move ℚ[x]'s generic theorems down and transfer them back.** 305 measured lines of
   duplication, and the counterfactual transfer is verified to work. Mechanical, low risk,
   immediately shrinks the largest offender. Do the five ring-vocabulary-only theorems in the
   same pass.
2. **Add the missing right-hand companions wherever a left form exists**, at both `ring` and
   `ring_poly`. Two lines each; four were needed this session alone.
3. **Introduce `std/domain.b4m` + `std/domain/polynomial.b4m`.** Clears the
   `noZeroDivisors`-dependent theorems out of ℚ[x] and F[x], and is what ℤ[x] needs to stop
   re-deriving. Bigger job — degree additivity is the substance.
4. **Decide the `polynomial` tactic question deliberately.** Either accept that polynomial
   identities are hand-written (and then document it in `GUIDE.md`, where it currently is not
   said), or cost an operation-name mapping against the `--fast` boundary. Right now the
   limitation is folklore discovered by hitting it.

**The process rule worth keeping regardless:** *before inducting over a polynomial recursion,
check whether the fact belongs one layer down.* ℚ[x] built the negation algebra by hand during
§17.3; that was the signal that `ring_poly` was missing it, and it was missed. The check is one
`--axioms` call and a grep of the layer below.

See [[generic-polynomial-negation-algebra]], [[sort-parameterization-via-model]],
[[std-file-layout-principle]].
