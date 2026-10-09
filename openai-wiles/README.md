# openai-wiles — a formalization of the withdrawn Weil-classes manuscript

> A `2b4m` formalization of OpenAI's withdrawn manuscript *"Algebraicity of Weil classes on
> split abelian eightfolds"*, built as **TWO CHAINS** that differ in exactly one mathematical
> input: the reverse stabilization-trace sign of §3.4.
>
> ```
> 2b4m check openai-wiles/architecture-right.md theWeilPlaneIsSpannedByAlgebraicClasses  # PASSES
> 2b4m check openai-wiles/architecture-wrong.md theWeilPlaneIsSpannedByAlgebraicClasses  # FAILS
> ```
>
> The `-right` chain carries **[6]'s sign** (`+1`, as arXiv:1303.0588v2 Lemma 3.4's *proof*
> states it, and as the manuscript's (3.6) quotes it): the count closes to zero,
> [9, Thm 2.3] applies, Lemma 3.6 goes through, Theorem 1.1 follows.
>
> The `-wrong` chain carries the sign **OpenAI's withdrawal notice** says is correct in the
> manuscript's convention (`−1`): the count is `I(f₁) + I(f₁) = −2m`, provably nonzero, so
> [9, Thm 2.3]'s hypothesis cannot be met and Lemma 3.6 is unprovable. Strict check fails
> naming that step, with the blast radius up to Theorem 1.1.
>
> `./diff-chains.sh` shows the difference. Four of the six duplicated files differ **only** in
> an import path; the mathematics diverges in exactly two places — `traces-*.b4m`'s sign axiom
> and `stabilization-traces-*.md`'s arithmetic.
>
> **READ THE AUDIT FIRST.** This directory's earlier headline finding — that §3.4 is
> *circular* — was **WRONG**, and rested on a hypothesis this formalization invented and
> attributed to [6]. See "What was gotten wrong". Neither chain decides which convention is
> right; between them they show the sign is the hinge.

## Why two chains and not one parameterized body

`import` names a fixed path, so a shared file cannot choose which sign module it pulls — and
an attempt to have the two roots inject the sign downward fails because the shared consumer
would have to name one root. (Cyclical *imports* are allowed; it is cyclical *dependencies*
that are not. The cycle works for one root, but it does not branch.)

So the chain is duplicated from the sign up to Theorem 1.1: six files, four of which differ by
one import line. `diff-chains.sh` makes that auditable rather than asking a reader to trust it.

### The bug this structure exposed

The first attempt at the split **still passed on both signs**, which is worth recording as a
failure mode. `stabilization-traces.md` defined

```
func insertedTotal(n: Int) => Int:
  insertedTotal(n) = n
```

hard-coding "+1 per inserted trace" into the **definition**. The trace sign was therefore
decorative: swapping the module changed nothing downstream. The fix makes the total `n` times
the actual sign, pinned to `traceSign(stabilize(phiZero), phiZero)` by a cited hole, so the
two chains genuinely diverge.

**The general lesson:** a formalization that reproduces a claimed error is only evidence if
flipping the disputed input actually changes the outcome. A green tree can mean the input never
mattered. This is the same shape as an earlier round here, where strict check reported a repair
step **dead** because nothing consumed the sign it established.

## What was gotten wrong

Stated first, because it is the most useful thing here.

For most of this exercise the directory asserted a confident diagnosis: that §3.4 is
**circular** — that [6] grants the `+1` reverse-trace sign only when the target link is
loose, that §3.4's outermost trace targets the given link `φ₀`, that nothing establishes its
looseness, and that §3.4 presents looseness as the *output* of the very insertion the sign
justifies. The checker appeared to confirm it:

```
error: cannot discharge the guard premise 'isLoose(phiZero)' at this call site
```

**That diagnosis was wrong, and the error was manufactured here.** The looseness guard on
`reverseTraceSign` was never in [6]. It was written into `legendrian/traces.b4m` with a
confident justification ("[6]'s proof obtains these traces (its G2/G4) through Corollary 2.5,
which destabilizes a loose knot") that is false. Reading Lemma 3.4's **proof** — which had
not been read; only its statement had — settles it. [6] builds four immersions and assigns:

| trace | direction | index at `k = 4` |
|---|---|---|
| `G₁` | `φ → φ₁` (stabilize) | `(−1)^{k−1} = −1` |
| `G₂` | `φ₁ → φ` (**reverse**) | `(−1)^k = +1` |
| `G₃` | `φ₋₁ → φ` (from destabilization) | `(−1)^{k−1} = −1` |
| `G₄` | `φ → φ₋₁` (**destabilize**) | `(−1)^k = +1` |

Looseness gates `G₃`/`G₄` — the destabilization direction, which needs Corollary 2.5 to
produce `φ₋₁`. The reverse trace `G₂` needs none: `φ₁` is a stabilization and hence already
loose, and `G₂` comes from Lemma 2.1 applied to the same homotopy as `G₁`. The manuscript
quotes all of this correctly in its equation (3.6).

So the manuscript's step is fine as cited, and the "repair" this directory applied repaired
nothing. The `openai-erratum` companion — which existed solely to hold the unrepaired step
and emit that error — has been removed.

### What OpenAI actually says, and why it is still unresolved here

The [withdrawal notice](https://github.com/openai/math/blob/main/preprints/Algebraicity-of-Weil-classes-on-split-abelian-eightfolds-September-18-2026/README.md)
states a different defect:

> The proof assigns each reverse stabilization trace sign `+1` and therefore claims that
> inserting `m` such traces makes the signed count zero. Accounting for the opposite source
> orientations of the two branches of the standard cusp gives sign `−1` for each reverse
> trace in this convention. The resulting count is therefore `I_new = I(f₁) − m = −2m ≠ 0`.

This is where the `−2m` figure comes from — it is the miscomputed count, not a commenter's
handle, which is how it was misread here for a while.

**This directory neither confirms nor refutes it.** [6] plainly assigns `I(G₂) = (−1)^k = +1`
in *its* convention, so the notice is asserting a **convention mismatch** between [6]'s index
and the manuscript's signed double-point count — not an error inside [6]. Adjudicating that
means comparing two orientation conventions, which is unformalized work. The axiom
`reverseTraceSign` carries [6]'s sign, as [6] states it, with the caveat recorded at the
declaration.

### The methodological finding

This is the part worth generalizing past this paper.

**The reference was axiomatized from the citing paper's rendering of it, not from the
reference.** A formalization built that way inherits exactly the error it was meant to
detect: a convention mismatch between source and citer is invisible to it by construction.
Checking *"does the manuscript quote [6] accurately"* — which it does — is not the same as
checking *"does [6]'s sign mean the same thing in the manuscript's convention"*, and only the
second would have caught the defect OpenAI reports.

Two failure modes compounded:

1. **Reading statements, not proofs.** Lemma 3.4's statement is a disjunction of two cases;
   which case applies to which trace is settled three paragraphs later, in the proof.
2. **A comment asserting verification that had not happened.** `traces.b4m` carried the line
   "verified against the source" above a claim that contradicted the source. Nothing in the
   toolchain can catch that — a false axiom with a confident comment checks green.

The audit that found all of this is a **source-by-source reading of every axiom's statement
against the cited text**, below. It found four citation errors in 29 axioms. None was
detectable by `2b4m check`.


## What is here

| file | contents |
|---|---|
| `architecture.md` | **the main thrust** — Theorem 1.1 from the four stages of §1.3, built top-down with `hole`s |
| `construction/marked-class.md` | Proposition 12.3, quarantined: the one assumption that swallows the paper |
| `parity.b4m` | 𝔽₂, the field the paper's sign exponents live in, plus exhaustion as a schema |
| `signs.md` | the sign identities of Section 6, quoted from the paper and proved |

Run `2b4m check openai-wiles` to verify. For the assumption set behind the main theorem:

```
2b4m check --axioms openai-wiles/architecture.md theWeilPlaneIsSpannedByAlgebraicClasses
```

which reports **29 erratum-specific axioms**, each a result the manuscript cites. The audit
below reads every one of their statements against that rule, and records the three that
failed it on an earlier pass.

## Method: holes first, then axioms

`architecture.md` is built the way a conditional result should be: state Theorem 1.1, make
every premise a `hole`, prove the theorem, then drive each hole back until it is either
provable or a result the paper *cites* — and only then flip it to an `axiom`.

The order matters. Writing the axioms first lets the formalizer **choose** convenient
premises, and a convenient premise is how you assume the thing you meant to check. An earlier
axioms-first attempt at this file was discarded after strict check caught it asserting a
class algebraic at one period while deriving it at another — see "What the checker caught".

Default `2b4m check` **rejects any surviving hole**, so the pass is only finished when the
hole count reaches zero. It did: `architecture.md` has none.

The source text is recovered from commit `adc7f1241b` (the pre-withdrawal state) at
`preprints/Algebraicity-of-Weil-classes-on-split-abelian-eightfolds-September-18-2026/paper.pdf`.
It is absent from the current catalogue — withdrawal removed the entries rather than
annotating them, so `CONTENTS.md` on `main` no longer lists these three titles.

## Why it is formalizable without the Hodge tower

The theorem statement needs machinery `std` does not have and will not soon: vector spaces,
sheaves, cohomology, complex manifolds, Chow groups, the cycle class map. But the paper is
mostly symplectic topology, and the part that failed is narrower again. Section 6 opens
*"Throughout this section all sign exponents are read modulo two"* — so every sign claim in
it is a polynomial identity over 𝔽₂, which is finite and decidable.

The method is therefore: **axiomatize the interface, formalize the arithmetic.** The paper
names its own imports —

> We use established immersion and embedding results, the ordinary family Floer theorems,
> and standard algebraic and analytic geometry with their hypotheses stated at the point of
> use.

— and those become axioms. What the paper claims to *prove* becomes theorems.

## The limitation, stated plainly

This can catch an error in the sign **arithmetic**. It cannot catch an error in the
**inputs** to that arithmetic: if the paper miscounts how many times two determinant lines
cross, or imports a cited lemma's sign convention backwards, then faithfully formalizing its
stated numbers reproduces the mistake.

That matters more than usual here, because the error is *known to exist*. A formalization
that goes through has most likely assumed it away rather than vindicated the paper. Every
axiom below is a result the paper **cites**; none is a step the paper claims to prove. Where
that line is uncomfortable, `signs.md` says so at the step.

## What the checker caught

Two things, neither of which I would have caught reading.

**A period mismatch in my own model.** I wrote `polarizationPower` as a function of the
period, so `θ⁴` differed from fiber to fiber. Strict check rejected the subtraction step:
the class spread to fiber `q` carried `p`'s `θ⁴`, while only `q`'s was known algebraic
there. Reading §2 settled it — *"The principal polarization has class θ, identified with ψ₀
in the fixed torus marking"* — the polarization is **one class** across the family, and
§12.4 spreads "the FIXED marked class". The paper was right and my model was wrong.

**That `polynomial` cannot do 𝔽₂.** Idempotence (`a·a = a`) is not a ring identity, so a
polynomial normalizer has no way to know it; strict check rejects
`[using polynomial(parity)]` on `mul(a, a) = a` with *"sides expand differently"*. Its
residue on the Lemma 6.2 collapse is a sum of **doubled** terms — `r + r`, `a + a + a`,
`pz·a + pz·a` — which is exactly the characteristic-two cancellation it is missing. Every
𝔽₂-specific step therefore goes through `exhaustion`.

## The axiom audit

Queried, not remembered:

```
2b4m check --axioms openai-wiles/architecture.md theWeilPlaneIsSpannedByAlgebraicClasses
```

**Zero holes, 40 axioms — 29 erratum-specific plus 11 from std's ℤ.** `openai-wiles` passes
plain `2b4m check`, not `--draft`.

Zero holes is a cheap number if you reach it by relabelling, so the audit that matters is not
the hole count but a reading of every axiom's *statement* against the rule: **`axiom` is for
results the paper cites; the paper's own mathematics must be proved.** That audit failed
twice, and both failures are recorded below because the pattern is the point.

### Round two: the citation audit

Every axiom's statement was then read against the **cited text itself** — the manuscript, [6]
(arXiv:1303.0588v2), [9] (arXiv:1303.0586v1) — rather than against the manuscript's prose
about them. Four errors, all introduced here, none visible to `2b4m check`:

| axiom | the error | status |
|---|---|---|
| `reverseTraceSign` | carried an `isLoose` guard **not in [6]**; see "What was gotten wrong" | guard removed; [6]'s G1–G4 table transcribed |
| `exactCancellation` | comment read "[6, Thm 3.6] = the manuscript's [9, Thm 2.3]" — **two different results in two different papers**: [6] Thm 3.6 is about a *conical point*, [9] Thm 2.3 about an immersion *cylindrical at −∞*. The manuscript cites [9], and its hypothesis list matches [9] | re-attributed to [9] Thm 2.3, quoted verbatim; content was already right |
| `aStabilizationIsLoose` | attributed to [6] Lemma 2.2, which says *"if χ(U) = 0, then Λ and Λ_U are formally Legendrian isotopic"* — a formal-isotopy claim with a hypothesis, not a looseness claim | re-attributed to [6] §2.2, which is where looseness is defined |
| `membershipInTheSpanForcesAnnihilation` | decomposed into "every test object pairs to zero against every power", which is **false in the manuscript's setting** — it says *"The leading intersection factor is nonzero because `l` is ample"*. A *determination* argument had been replaced by a *vanishing* argument | rebuilt as (10.16)'s polynomial-interpolation argument: the pairings for all `k` force `ζ_s = ν Σ e^{−jl}`, which fails the test against `P_C` |

Verified correct against source, with the quotations that settle them:

- `forwardTraceSign` — [6] Lemma 3.4, `I(G₁) = (−1)^{k−1}`. ✓
- `theExtraObjectDetectsTheExceptionalPart`, `aScalarGraphAnnihilatesTheExceptionalPart` —
  §10.6: *"Here α = α_ex + g₁ + g₂ + g₃, g_k · α_ex = 0, and c · α_ex ≠ 0."* ✓
- `everyPeriodIsHitByTheComponent` — §12.4: *"Thus H → U is surjective."* ✓
- `aRationalAlgebraicClassIsACombinationOfSubvarieties`,
  `aNonzeroWeilProjectionSelectsAMarkedConstituent` — Prop 12.3: *"Express a cycle … as a
  finite rational linear combination of integral codimension-four subvarieties. At least one
  constituent has a nonzero Weil projection."* ✓
- `remmertProperMapping` — Lemma 12.1: *"Remmert's proper mapping theorem makes their images
  closed analytic [15]."* ✓
- `theEigenvaluesAreNonrealConjugates` — re-verified numerically, `d = 1..39`: with
  `m = ⌊√d·cot(π/8)⌋+1`, `arg(m+i√d) ∈ (0, π/8)` and `(m+i√d)⁸` is nonreal; the floor itself
  fails the bound. No violations. ✓
- The remaining citations (base change and Betti–étale [20], Baire, formula (2.3),
  `ch₄(O_Z) = [Z]` of [14], Hilbert schemes [16]) match the manuscript's own attributions. ✓

### What round one caught

Three axioms were doing the paper's work while wearing a citation's name. Each is now a
theorem, and the decomposition is what added the axiom count from 13 to 29 — more axioms, but
every one of them smaller and genuinely cited.

| axiom that failed the rule | why it failed | now |
|---|---|---|
| `aCycleClassDecomposesIntoIntegralSubvarieties` | read like a citation but its *statement* produced the whole marked-class existential — the same swallow as the forbidden `theConstructionDeliversAMarkedClass`, renamed | **theorem**, from `aRationalAlgebraicClassIsACombinationOfSubvarieties` (the definition of the image of `CH⁴ ⊗ ℚ`) + `aNonzeroWeilProjectionSelectsAMarkedConstituent` (linear algebra on §2's decomposition) |
| `theConjugationEndomorphism` | asserted spanning outright, which left `eigenvalues/independence.md`'s proof **orphaned** — the eigenvalue work was decorative | **theorem**, from `theConjugationIsAlgebraic` (standard) + `theConjugationProducesASpanningPartner`, now **proved** in `eigenvalues/independence.md` from the eigenvalue distinctness |
| `theMarkedClassIsConstantAcrossTheFamily` | carried Lemma 12.1's surjectivity and §12.4's spreading; its own comment admitted "NOT a citation" | **theorem**, from `theMarkedClassSpreadsAcrossTheParameterSet` (proved in `construction/chern-constancy.md`) + one Lemma 12.1 citation |

A fourth, `membershipInTheSpanForcesAnnihilation`, was the paper's computation (10.16). It is
now a **theorem** from two citations: bilinearity of the Euler pairing over the span, and the
pullback identification of §10 (Lemma 7.4 + Prop 10.2) under which every test object pairs to
zero against every power of `l`.

The orphan case is the one worth generalizing. `independence.md` *proved* the eigenvalue
argument, and `architecture.md` *assumed* the conclusion it feeds — so the proof existed and
carried no weight. Nothing in the hole count detects that; only reading the axiom's statement
against the theorem it was supposed to consume does.

### The 29 erratum axioms

Standard mathematics, cited by the manuscript:

| axiom | source |
|---|---|
| `theAlgebraicClassesFormASubspace` | the image of `CH⁴(A) ⊗ ℚ → H⁸(A, ℚ)` is a ℚ-subspace |
| `aPowerOfThePolarizationIsAlgebraic` | `θ` is a divisor class |
| `theCycleClassMapIsFunctorial` | functoriality under an algebraic correspondence |
| `theConjugationIsAlgebraic` | an integral matrix commuting with every period in `U` defines an algebraic endomorphism |
| `selfConjugateIsReal` | `z = z̄ ⇒ z ∈ ℝ` |
| `theEigenvaluesAreNonrealConjugates` | `arg(m + i√d) ∈ (0, π/8)` under the paper's bound (checked numerically, `d = 1..39`, bound tight) |
| `proportionalityForcesBothEigenvalues` | linear algebra on an eigenspace decomposition |
| `nonProportionalClassesSpan` | `dim W_K(A_Π) = 2` (§2) |
| `chernCharactersAgreeAlongAPath` | homotopy invariance of `ch` |
| `anyTwoPointsOfTheComponentAreJoined` | connected + locally path connected |
| `equalChernCharactersGiveEqualClasses`, `aMarkedClassIsAlgebraicAtItsOwnPeriod` | `ch₄(O_Z) = [Z]` of [14], both halves |
| `everyPeriodIsHitByTheComponent`, `anAlgebraicClassAtAGoodPeriodIsMarkedByTheComponent` | Lemma 12.1: `H → U` is surjective, and the Hilbert family covers every closed subscheme of every fiber ([16] + [15]) |
| `remmertProperMapping`, `aProperClosedAnalyticSubsetHasEmptyInterior`, `theHilbertParameterSpacesExist` | Remmert; Baire-style interior; Hilbert schemes [16] + base change [15] |
| `aRationalAlgebraicClassIsACombinationOfSubvarieties` | the definition of the image of `CH⁴ ⊗ ℚ` |
| `aNonzeroWeilProjectionSelectsAMarkedConstituent` | pick a constituent with nonzero Weil projection, split off `θ⁴`: §2's decomposition `H⁸ = ⟨θ⁴⟩ ⊕ W_K ⊕ rest` |
| `baseChangeTransportsSpanMembership`, `theComparisonTransportsSpanMembership` | [20]: smooth proper base change; Betti–étale comparison |
| `anAlternatingChernCharacterIsAlgebraic` | Prop 11.4's rationality input |
| `baireSuppliesAGoodPeriod` | Baire category on the parameter space |
| `outsideTheSpanForcesANonzeroWeilProjection` | formula (2.3) of §2 |
| `exactCancellation` | [6, Thm 3.6] = the manuscript's [9, Thm 2.3], with **both** hypotheses |
| `aStabilizationIsLoose`, `forwardTraceSign` | [6] Lemma 2.2; Lemma 3.4's `(−1)^{k−1}` case, "for any φ" |
| `theCountIsTheSum`, `theRepairedInsertionTotal` | the count is `I(f₁) +` Σsigns; `(m+1) + (−1) = m` |

Geometry of the paper, cited as such — §10's Euler-pairing identities:

| axiom | what it carries |
|---|---|
| `theExtraObjectDetectsTheExceptionalPart`, `theExtraObjectDetectsTheDetectedClass` | §2's construction of `α`: `c · α_ex ≠ 0`, and `⟨C, ζ_s⟩ ≠ 0` |
| `aScalarGraphAnnihilatesTheExceptionalPart` | `g_k · α_ex = 0` |
| `pairingOnTheSpanIsDeterminedByThePowers` | bilinearity of `χ(P, −)` over the span |
| `thePowersDoNotSeeTheExceptionalPart` | Lemma 7.4 + Prop 10.2: the powers of `l` are pulled back from the polarized quotient |

### So: did we fix the theorem?

**No, and there was nothing here to fix.** The §3.4 defect this directory claimed to repair
was manufactured by a fabricated axiom. What survives is narrower:

> Every step from §3.4 up to Theorem 1.1 is kernel-checked, and each remaining assumption is
> a result the manuscript cites — with the four citations above corrected after being read
> against their sources.

On OpenAI's stated reason for withdrawal — the reverse-trace sign being `−1` rather than `+1`
in the manuscript's convention — this directory is **silent**. It carries [6]'s sign as [6]
states it. Deciding the question requires comparing orientation conventions, which is not
formalized here.

What is **not** claimed: that Sections 4–11's symplectic topology is correct. Those sections
are the origin of the cited geometric inputs above (`anAlternatingChernCharacterIsAlgebraic`,
the Euler-pairing identities), and the formalization takes them at their word. What changed in
this round is that they are no longer hidden inside one all-swallowing axiom — each enters by
name, at the point it is used, and `--axioms` lists it.

Two things the checker caught that are worth recording:

- When the count became a proved theorem, the forward-trace step went **dead** — strict check
  reported it unused, meaning the repair was decorative. Making `theRepairedInsertionTotal`
  conditional on the trace sign fixed that. A repair nothing consumes is not a repair.
- The `openai-erratum` companion directory has been **removed**. It existed to hold the
  manuscript's §3.4 step unrepaired so the checker would reject it. Since the rejection came
  from a fabricated guard (see below), there was nothing left for it to demonstrate.

## Findings so far

Five of the paper's sign claims have been checked. **All five are valid.**

- **Lemma 6.2's permutation collapse** — the four determinant-line crossings sum to
  `A + (pz + C)R`, and then to equation (6.3). Kernel-verified over all 16 corners
  (`theCrossingSignsCollapse` in `signs.md`).
- **Lemma 6.4's cyclic sign** — checked exhaustively for arities 2 through 6; no mismatch.
- **Section 6.2's reduction** of equation (6.8) to
  `v + w + c + (c+q)(v+w+1) + (v+w)(c-1-q) + q = 0`; valid over all 16 assignments.
- **Lemma 6.2's second step** — `A + (pz+C)R` to equation (6.3) under `l = i − 1`; valid
  over all 256 assignments of its eight parities.
- **Lemma 7.4's intersection sign** — that the local intersection sign at a transverse point
  is `(−1)^|x|`. The chain is: the orientation discrepancy has exponent `|x| − n`, the
  concatenation contributes `(−1)^(n(n−1)/2)`, and at `n = 8` those compose to `(−1)^|x|`.
  Valid — and note the paper flags its own dimension-sensitivity ("Since eight is even");
  the same argument is false at `n = 9`.

So the error is **not** in the sign algebra of Section 6. That leaves two possibilities, and
the second is the one the method cannot reach:

1. A step not yet formalized — Sections 7 through 12, or the stabilization traces of §3.4.
2. A sign **convention** mismatched against a cited source. The paper's §3.4 reads
   *"We use the stabilization traces of [6, Lemma 3.2 and proof of Lemma 3.4]"* and derives
   `φ → φ₁ : −1`, `φ₁ → φ : +1` at k = 4. That arithmetic is internally consistent, and the
   downstream use is consistent with it. If the imported convention is the other way round,
   every local check still passes.

Possibility 2 is what OpenAI's own description points at — a *stabilization-trace*
cancellation — and it is exactly what axiomatizing an interface hides. Which is the honest
result of this exercise so far: the formalization is real and the arithmetic is sound, and
that is not the same as the paper being right.

Worth noting independently: the paper's §6.2 says *"We check this cancellation without
specifying the bare signs."* Verifying sign *differences* rather than absolute signs is
precisely how a global `+1`/`−1` flip survives local verification.
