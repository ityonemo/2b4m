# openai-fixed — the same manuscript, with the §3.4 defect repaired

> This is `../openai-erratum/` with the §3.4 circularity removed. Plain `2b4m check` — not
> `--draft` — passes it with **zero holes**, resting on 29 erratum-specific axioms, every one
> a result the manuscript cites. See "The axiom audit" for a statement-by-statement reading
> against that rule, including the three axioms that failed it on an earlier pass.
>
> **WHAT IS FIXED: the `isLoose` problem, and only that.** The manuscript's outermost trace
> `φ₁ → φ₀` uses the `+1` sign, which [6] grants only when the target link is loose — and
> looseness is what §3.4 claims to *produce*. Two routes out, both taken here: stabilize `φ₀`
> first (free, by [6] line 462, and then loose by Lemma 2.2), and make the outermost trace
> FORWARD (granted "for any φ", no looseness needed). Either breaks the circle; the count
> stays zero at `I(f₁) + (m+1) − 1 = 0`, and `exactCancellation` now carries **both** of
> [6, Thm 3.6]'s hypotheses rather than just the count.
>
> **Do not read this as "the paper is fixed."** [6] itself notes that any Legendrian can be
> made loose by one extra stabilization, so this gap was always trivially closable; and a
> published account describes a different, worse error (possibly spurious, or about another
> theorem — it is unresolved). Note that OpenAI's withdrawal is not evidence of severity:
> these manuscripts have no human author who could act on a margin
> note. See the contested-diagnosis note below.

On **6 October 2026** OpenAI published 722 machine-generated mathematics manuscripts to
`github.com/openai/math`. On **7 October** three were withdrawn. From their
[`history.md`](https://github.com/openai/math/blob/main/history.md):

> In "Algebraicity of Weil classes on split abelian eightfolds" a sign error invalidates a
> stabilization-trace cancellation argument and the construction used by two dependent
> papers. As a result, we have withdrawn the following three manuscripts:
> - Algebraicity of Weil classes on split abelian eightfolds
> - Algebraicity of Kuga–Satake Correspondences for K3 Surfaces
> - The rational Hodge conjecture for products of K3 surfaces

The three form a tower. Weil classes are the canonical test case for the Hodge conjecture;
the Kuga–Satake construction attaches an abelian variety to a K3 surface, so algebraicity for
abelian eightfolds is what makes that correspondence algebraic; and the Hodge conjecture for
products of K3 surfaces follows from the correspondence. One sign error at the base took
down the headline claim — a case of a Millennium Problem — two levels up.

**None of the three had a Lean formalization.** At the time of withdrawal roughly 42% of
top-line results in the repo did.

## The diagnosis is contested

Stated up front because it bears on everything below.

OpenAI's notice says only: *"a sign error invalidates a stabilization-trace cancellation
argument and the construction used by two dependent papers."* It does not say which sign.

**What this formalization found:** [6, Lemma 3.4]'s third bullet grants the `(−1)^k` trace
sign only *"if in addition φ is assumed to be a loose Legendrian knot"*. §3.4's outermost
inserted trace is `φ₁ → φ₀`, whose target is the **given** standard real-plane link, and the
manuscript establishes no looseness for it — it treats looseness as the *output* of the
insertion ("The negative link is now loose"). Checking Theorem 1.1 reports exactly that:

```
error: cannot discharge the guard premise 'isLoose(phiZero)' at this call site
```

**A published account says something different.** One secondhand summary describes the error
as: *"with initial signed count −m, the reverse traces contribute −m, giving −2m rather than
zero."* That requires equation (3.6) to be **backwards**. Checked against the vendored source:

- [6] is explicit — `G₁: φ → φ₁` has `I(G₁) = (−1)^{k−1}`; `G₂: φ₁ → φ` has `I(G₂) = (−1)^k`.
- At `k = 4` that is `φ → φ₁ : −1` and `φ₁ → φ : +1`, which is **what (3.6) says**. The
  manuscript's quotation of its source is correct.
- To get `−m` the traces would have to run `φ_j → φ_{j+1}`, i.e. ordered `φ₀` innermost to
  `φₘ` outward — the opposite of the manuscript's stated ordering.

So the `−2m` account cannot be reconciled with [6] plus the manuscript's own ordering. Three
possibilities, undecided here: the summary is garbled; OpenAI calls the other direction
"reverse"; or **the diagnosis below is wrong**, in which case the looseness gap is a second,
independent defect rather than the one that caused the withdrawal.

What is not in doubt: the looseness precondition in [6] is real, the manuscript does not
establish it, and it uses the sign that requires it.

### Sharpened: the defect is a CIRCULARITY, not just a missing hypothesis

Reading further into [6] strengthens the finding, and changes its character.

[6]'s **Theorem 3.6** is the result the manuscript invokes (as [9, Thm 2.3]):

> Let `f₀ : L → X` be a Lagrangian immersion with a conical point … **If the Legendrian link
> of `f₀` at `p` is loose and if `I(f₀) = 0`,** then there exists a Hamiltonian regular
> homotopy … connecting `f₀` to a Lagrangian **embedding**.

Two independent hypotheses: **looseness** and **zero index**. And [6]'s Theorem 3.7 — which
does precisely what §3.4 attempts, reducing `|I|` by inserting Lemma 3.4 traces — likewise
takes looseness as a *hypothesis*, never deriving it.

So the structure [6] actually supports is:

    link loose                 ⇒ (Thm 3.7) reduce to SI = |I|
    link loose AND I = 0       ⇒ (Thm 3.6) obtain an EMBEDDING

§3.4 needs the second. Its problem is the order of justification:

- The `(−1)^k = +1` trace sign it uses is available **only if the target link is loose**.
- It uses those `+1` signs to drive the count to zero.
- It presents looseness as the **output** of that same insertion: *"The negative link is now
  loose and the total signed double count is `I(f₁) + m = 0`."*

Looseness is needed to license the signs that establish the count, but is offered as a
consequence of the construction those signs justify. That is circular, and it is a stronger
objection than "a hypothesis is missing" — a missing hypothesis can be supplied, whereas
circular justification has to be re-ordered.

**It is still repairable**, and by the same move: make `φ₀` loose *first* (free, by [6] line
462 — any Legendrian can be made loose by one extra stabilization without changing its formal
isotopy class), *then* every trace's `+1` is licensed and the count closes. `openai-fixed/`
takes the other available route — one forward trace, which needs no looseness at all — and
reaches zero as well. Either breaks the circle.

What this does **not** settle is whether the circularity is what OpenAI withdrew over. It
remains compatible with both candidate diagnoses.

### Most likely: this is a SECONDARY gap, trivially fixable

The evidence points against the finding below being *the* error that caused the withdrawal.

**[6] makes looseness free.** Line 462 of the source: *"Any Legendrian submanifold Λ ⊂ Y can
be made loose by stabilizing it in arbitrarily small neighborhood of a point. Moreover, it
can be made loose even without changing its formal Legendrian isotopy class."* So if you need
`φ₀` loose, you stabilize once more — which is repair (C), arrived at from the other side.
The gap is presentational: a referee writes "insert `m+2`" in the margin and moves on.

**The withdrawal says nothing about severity.** An earlier draft of this note argued that
withdrawing rather than repairing implies the defect was not locally fixable. That inference
is wrong. These manuscripts are machine-generated — roughly three hours of model compute
each, with no human author who has verified the argument. "Insert `m+2` traces" is a margin
note a referee can act on; it is not something OpenAI can act on, because acting on it means
a human taking authorship of a repair inside an 80-page symplectic-topology argument nobody
there has checked. Withdrawal is the only available move whether the gap is two traces or
a broken convention.

So the withdrawal is not evidence either way, and the two candidate diagnoses sit roughly
even. What remains true is the first point: **[6] makes looseness free, so the gap below is
trivially closable** — which makes it the kind of thing a human reader skims past and a
checker catches, a decent advertisement for formalization and a weak one for this particular
diagnosis being *the* error.

What `openai-fixed/` demonstrates is therefore narrower than "the paper is repaired": it
shows that *this* gap closes without disturbing the count, and that the architecture above
§3.4 is unaffected. If the real error is the inverted convention, the repair here does not
touch it.

## What is here

| file | contents |
|---|---|
| `architecture.md` | **the main thrust** — Theorem 1.1 from the four stages of §1.3, built top-down with `hole`s |
| `construction/marked-class.md` | Proposition 12.3, quarantined: the one assumption that swallows the paper |
| `parity.b4m` | 𝔽₂, the field the paper's sign exponents live in, plus exhaustion as a schema |
| `signs.md` | the sign identities of Section 6, quoted from the paper and proved |

Run `2b4m check openai-erratum` to verify. For the assumption set behind the main theorem:

```
2b4m check --axioms openai-erratum/architecture.md theWeilPlaneIsSpannedByAlgebraicClasses
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
2b4m check --axioms openai-fixed/architecture.md theWeilPlaneIsSpannedByAlgebraicClasses
```

**Zero holes, 40 axioms — 29 erratum-specific plus 11 from std's ℤ.** `openai-fixed` passes
plain `2b4m check`, not `--draft`.

Zero holes is a cheap number if you reach it by relabelling, so the audit that matters is not
the hole count but a reading of every axiom's *statement* against the rule: **`axiom` is for
results the paper cites; the paper's own mathematics must be proved.** That audit failed
twice, and both failures are recorded below because the pattern is the point.

### What the audit caught

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

**We fixed §3.4, and we checked everything above it.** That is a narrower claim than "the
theorem is proved", and the difference is worth stating precisely:

> Every step from §3.4 up to Theorem 1.1 is kernel-checked, and each remaining assumption is
> either textbook or a clearly-identified geometric input the manuscript cites. §3.4's
> circularity is removable without disturbing anything above it.

What is **not** claimed: that Sections 4–11's symplectic topology is correct. Those sections
are the origin of the cited geometric inputs above (`anAlternatingChernCharacterIsAlgebraic`,
the Euler-pairing identities), and the formalization takes them at their word. What changed in
this round is that they are no longer hidden inside one all-swallowing axiom — each enters by
name, at the point it is used, and `--axioms` lists it.

Two things the checker caught that are worth recording:

- When the count became a proved theorem, the forward-trace step went **dead** — strict check
  reported it unused, meaning the repair was decorative. Making `theRepairedInsertionTotal`
  conditional on the trace sign fixed that. A repair nothing consumes is not a repair.
- `openai-erratum` was re-synced to carry the *same* decomposed axiom set as `openai-fixed`,
  differing only in `legendrian/stabilization-traces.md`. It still fails with
  `cannot discharge the guard premise 'isLoose(phiZero)'` — so the §3.4 error is not an
  artifact of a convenient assumption elsewhere.

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
