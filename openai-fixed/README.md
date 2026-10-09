# openai-fixed — the same manuscript, with the §3.4 defect repaired

> This is `../openai-erratum/` with one change: §3.4 inserts `m+2` stabilization traces
> instead of `m`, with the outermost one FORWARD. `2b4m check openai-fixed` is GREEN and
> Theorem 1.1 goes through with no holes.
>
> **The repair:** the manuscript's outermost trace `φ₁ → φ₀` needs `isLoose(φ₀)`, which [6]
> requires and nothing supplies. Using `m+1` reverse traces (every target a stabilization,
> hence loose by [6] Lemma 2.2) plus one outermost forward trace (granted "for any φ", no
> looseness needed) keeps the signed double count at zero: `I(f₁) + (m+1) − 1 = 0`. So
> [9, Thm 2.3] still applies, and every trace now has its hypothesis.
>
> **Do not read this as "the paper is fixed."** [6] itself notes that any Legendrian can be
> made loose by one extra stabilization, so this gap was always trivially closable; and a
> published account describes a different, worse error. Note that OpenAI's withdrawal is not
> evidence of severity — these manuscripts have no human author who could act on a margin
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

which reports **six axioms** — four genuine citations and two that are the paper's own work.

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

Nine axioms. **Six are genuine citations. Three are not**, and saying otherwise would be
exactly the failure this exercise exists to expose — so they are labelled.

### Genuine citations (six)

| axiom | source |
|---|---|
| `theAlgebraicClassesFormASubspace` | the image of `CH⁴(A) ⊗ ℚ → H⁸(A, ℚ)` is a ℚ-subspace |
| `aPowerOfThePolarizationIsAlgebraic` | `θ` is a divisor class, so `θ⁴` is an intersection of divisors |
| `theCycleClassMapIsFunctorial` | functoriality under an algebraic correspondence |
| `exactCancellation` | Eliashberg–Murphy, *Lagrangian caps*, [9, Thm 2.3] — the manuscript's own citation |
| `forwardTraceSign` | [6, Lemma 3.4] third bullet, `(−1)^{k−1}` case, stated "for any φ" — verified against arXiv:1303.0588v2 |
| `chernCharactersAgreeAlongAPath`, `anyTwoPointsOfTheComponentAreJoined` (in `construction/chern-constancy.md`) | homotopy invariance of the Chern character; connected + locally path connected ⇒ path-joined |

### Not well-known (three)

| axiom | what it actually assumes |
|---|---|
| `theConstructionDeliversAMarkedClass` | **Sections 4–11** of the manuscript — the weighted Floer module, the theta section ring, mirror symmetry, the alternating Chern character. Stated as an implication from Lemma 3.6, so Lemma 3.6 itself is *not* assumed; everything above it is. |
| `theMarkedClassIsConstantAcrossTheFamily` | Lemma 12.1's construction of the Hilbert parameter spaces, plus the bridge from Lemma 12.2's constancy to algebraicity on every fiber. Lemma 12.2's own constancy claim **is** now proved (`construction/chern-constancy.md`). |
| `theRepairedCountIsZero` | the repaired arithmetic `I(f₁) + (m+1) − 1 = 0`. Elementary, but it is a restatement of the paper's counting for the repaired insertion, not a citation. |

And one that is mixed: `theConjugationEndomorphism` bundles a standard fact (an integral
matrix commuting with every period in `U` is an algebraic endomorphism) with the paper's own
eigenvalue computation `λ± = (m ± i√d)⁸`. The computation is elementary and was checked
numerically for `d = 1..39`, including that the bound `m > √d·cot(π/8)` is tight — but it is
the paper's step, not a citation, so the bundle is not purely well-known either.

### What that means

The claim this formalization supports is therefore narrow and conditional:

> **If** Sections 4–11 deliver a marked class from Lemma 3.6, and **if** Lemma 12.1's
> parameter spaces exist, **then** Theorem 1.1 follows — and in `openai-fixed`, the repaired
> §3.4 supplies Lemma 3.6 without the unjustified looseness hypothesis.

It does **not** support "the paper is correct", and it cannot: the three axioms above are
where the mathematics lives. What it does establish is that the *architecture* composes, that
the §3.4 defect is real and reaches the top, and that repair (C) removes it.

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
