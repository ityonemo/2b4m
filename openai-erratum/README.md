# openai-erratum — formalizing the sign bookkeeping of a withdrawn manuscript

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
