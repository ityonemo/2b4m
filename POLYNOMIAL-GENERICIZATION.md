# Polynomial genericization — what is left

**Recommendations 1 and 2 are DONE** (2026-11-25). All six of ℚ[x]'s misplaced-but-generic
theorems now live at the ring layer and transfer back in one line each; ℚ[x] shrank 365 lines,
6618 → 6253. The right-hand companion lemmas exist. Two recommendations remain.

## THE TEST, which is the reusable part

**What the proof CITES, not what the statement mentions.** A statement over `qcoeff` and
`rational.mul` looks ℚ-specific; if its proof only ever cites ring axioms, it is generic.
`check --axioms <file> <theorem>` answers it in one command, and the naming never reveals it.

**Its limit, measured:** `--axioms` sees what a proof cites, not how much unported scaffolding
sits beneath. `negationPreservesTheDegree` read as generic and was — but porting it meant
first porting a 75-line helper. Survey the dependency chain, not just the axiom list.

**And a survey goes stale from your own work.** An agent surveying six dependencies up front
ported one of them mid-run, then reported the original count — concluding wrongly that a
three-deep chain blocked it, when five of six were by then already in place. Re-check
immediately before acting.

## THE HARD CONSTRAINT: `polynomial` is a SCALAR-layer tactic

`polynomial` binds `add`/`mul`/`ZERO`/`succ` by **well-known name**, so over a carrier whose
operations are `addP`/`mulP` it reports `the goal has no add/mul structure`. All 176
`using polynomial(...)` sites pass `field` or `rational` — the **coefficient** ring — and not
one is over polynomial operations.

So a polynomial ring identity cannot be discharged by a tactic. `std/field/polynomial.b4m`'s
`polyMulIsAssociative` is a double-sum reindexing nothing automates.

**The cost is step-specific, not uniform.** Porting `theNegationIsTheMinusOneScaling` turned
one `[using polynomial(rational)]` into two explicit steps; the last two ports needed none,
being pure coefficientwise reasoning. Budget per scalar-tactic step in the proof being moved,
not per proof. (PAINPOINTS 22 carries this, with the parked idea of letting `polynomial`
synthesize over a MODEL — which would read ring structure through the model's own `:` map, so
a misbound operator becomes a model error rather than a silently wrong normalization.)

## RULING: the polynomial layering STOPS at ring (user, 2026-11-25)

`std/domain.b4m` landed and stays. **`std/domain/polynomial.b4m` will NOT be built**, and the
three F[x] degree theorems stay where they are.

**Why, and it is an argument about the whole hierarchy rather than about D[x].** The algebraic
chain does not stop at domains — `ring ⊃ domain ⊃ UFD ⊃ PID ⊃ euclidean domain ⊃ field` — and
each has polynomial facts that genuinely need its own axioms (Gauss's lemma wants a UFD, the
division algorithm a euclidean domain). One polynomial layer per structure means six or more
`*[x]` files, each re-declaring the same primitive surface to add a handful of theorems. The
structural cost grows with the hierarchy while the mathematics added per layer stays small,
which is the opposite of what a layering should do.

**Measured, which is what settled it.** `FieldPolyModelsRingPoly` maps **64 entries** — not the
arithmetic core alone but the whole surface: the `triple*` family, `cappedRun`, `monus`,
`segment`/`rsegment`, `tailConvolution`, `theCofactorIndex`. Twelve are RECURSIVE, so each
needs a `termination:` declaration plus a proved obligation at the new layer. A faithful D[x]
is 1,500–2,000 lines, under 10% of it new mathematics. (An earlier estimate of ~250 lines was
taken from the arithmetic core rather than the model's actual surface — count the model.)

**WHAT TO DO INSTEAD: declare the polynomial sort at the concrete carrier.** That is already
the repo's pattern — `std/integer/polynomial.b4m` declares ℤ[x] over `Int` with its own
`IntegerPolynomials` model into R[x], never routing through an abstract intermediate. A
concrete domain wanting polynomials does the same and proves its domain-dependent facts
locally from its OWN zero-divisor theorem. One file.

The abstract layer's only value would be sharing proofs between concrete domains, and there
are two (ℤ and ℤ_p) each wanting about one lemma.

**The scalar hierarchy is different and stays cheap.** `std/domain.b4m` is 11 theorems with no
primitive duplication, because a scalar sort is one symbol rather than a 64-entry surface. A
field models it and inherits `cancelMulLeft` as a transfer instead of a reciprocal argument.
Extend the SCALAR tower freely; stop at `ring` for polynomials.

**What the degree facts needed, recorded since it was measured and is not obvious.**
`field.noZeroDivisors` enters the chain at exactly one step (`std/field/polynomial.b4m:6649`,
inside `aProductOfNonzerosIsNonzero`, where the source itself comments *"a field has no zero
divisors"*). Everything around it is already generic and already at the ring layer. So should
ℤ[x] ever want degree additivity, it is one lemma from ℤ's own zero-divisor fact — which does
not yet exist in `std/integer*` and would be the prerequisite, reachable from the sign
trichotomy at `std/integer/order.b4m:1141`.

## Still open

**Decide the `polynomial`-tactic question deliberately.** Either accept that polynomial
identities are hand-written and say so in `GUIDE.md` (where it still is not), or cost the
model-synthesis idea against the `--fast` boundary, where `model` already drops the per-axiom
obligation-coverage check. PAINPOINTS 22 carries the idea.

## The process rule worth keeping regardless

*Before inducting over a polynomial recursion, check whether the fact belongs one layer down.*
One `--axioms` call and a grep of the layer below.

**And when adding a directional lemma, add both directions.** The gap mechanism is
predictable: a layer gets built to satisfy one consumer, that consumer's proofs happen to be
left-handed, and the right forms are never written — invisible until something blocks. Found
three times in this work alone (`std/ring.b4m` had no `neg(ZERO) = ZERO`, hence no
nonzero-negation fact; and `negationOfZeroIsZero` was never re-exported into
`ring/polynomial.b4m`). The same gap at the scalar layer still leaves `Ring` without an
additive left-swap, which `assoc_commut`'s explicit form needs.

See `[[generic-polynomial-negation-algebra]]`, `[[sort-parameterization-via-model]]`,
`[[std-file-layout-principle]]`.
