# openai-wiles — the withdrawn Weil-classes manuscript, formalized two ways

A `2b4m` formalization of OpenAI's withdrawn preprint *"Algebraicity of Weil classes on split
abelian eightfolds"* ([pre-withdrawal PDF](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Algebraicity-of-Weil-classes-on-split-abelian-eightfolds-September-18-2026/paper.pdf),
[withdrawal notice](https://github.com/openai/math/blob/main/preprints/Algebraicity-of-Weil-classes-on-split-abelian-eightfolds-September-18-2026/README.md)).

## What 2b4m is, and why this is checkable by hand

[**2b4m**](https://github.com/ityonemo/2b4m) ("too big for margin", after Fermat) is a proof
checker designed on an unusual premise: proofs are *not* expected to be written by humans, but
they are expected to be **extremely easy for humans to check**. It is built for exactly the
situation this directory is in — a machine-generated argument that someone needs to audit.

Three design choices matter for reading what follows, and none of them require you to learn
the language first.

**Proofs are explicit named steps.** Every step states its formula in full and names the rule
and the earlier steps that justify it. There is no proof search, no hidden context, no tactic
that silently does three things. What is written is exactly what the checker checked:

```
theorem theExtraObjectIsNotAScalarGraph: not isAScalarGraph(theExtraObject)
proof
  @given-it-were-a-scalar-graph |
    assume isAScalarGraph(theExtraObject) {
      @it-is-a-scalar-graph |
        isAScalarGraph(theExtraObject)
        [by hypothesis given-it-were-a-scalar-graph]
      @then-it-annihilates |
        pair(theExtraObject, exceptionalPart) = zeroPairing
        [using specialize aScalarGraphAnnihilatesTheExceptionalPart(theExtraObject)
          it-is-a-scalar-graph]
      @but-it-detects |
        pair(theExtraObject, exceptionalPart) != zeroPairing
        [by cite theExtraObjectDetectsTheExceptionalPart]
    }
  @conclusion |
    not isAScalarGraph(theExtraObject)
    [by not_intro given-it-were-a-scalar-graph then-it-annihilates but-it-detects]
qed
```

That is the whole proof, verbatim from `detection/nonpolarization.md`, and you can read it as
what it is: *suppose it were a scalar graph; then it annihilates the exceptional part; but it
detects it; contradiction.* The step labels
are the argument's outline — `2b4m query outline <file> <theorem>` prints just that column.
Connectives are words (`and`, `or`, `not`, `->`, `iff`), every name is greppable, and
diagnostics quote surface syntax back at you. **A mathematician with no proof-assistant
experience should be able to follow it and object to it.** That is the design goal, and it is
the reason this audit is worth publishing rather than just asserting a conclusion.

**Shimming in a borrowed fact is one line.** A formalization of a paper's *architecture* does
not want to redevelop Hodge theory or Floer homology — it wants to assume the cited results
and check how they compose. In 2b4m that assumption is a first-class declaration:

```
hole remmertProperMapping
  cites "Grauert-Remmert, Coherent Analytic Sheaves [15]: proper mapping theorem":
  forall h: AnalyticSpace; isProperOverTheBase(h) -> isClosedAnalytic(imageInTheBase(h))
```

A `hole` is an unproved step. A **cited** hole is one assumed on an external authority: the
checker still treats it as an assumption, still lists it, and prints its locator on every run —
but it does not block a strict check, because the one thing a proof checker cannot do is
confirm that Grauert–Remmert says what that line claims. An *uncited* hole does block. So the
assumption set is always visible and always attributed, and you can audit the formalization by
reading 36 one-line citations instead of trusting a 5,000-line development.

Deliberately, `axiom` is reserved for a theory's own primitives (𝔽₂'s ring laws, here) and
`axiom ... cites` is a hard error — so a borrowed theorem cannot be quietly relabelled as a
local axiom, which is how an unproved step stops being visible.

**The strategy, then:** axiomatize the interface, formalize the architecture. What the paper
*cites*, we cite. What the paper claims to *prove*, we prove — and if it does not go through,
the checker names the step and everything resting on it.

## The two chains

It exists as **two chains** that differ in exactly one mathematical input — the reverse
stabilization-trace sign of §3.4 — and run that difference all the way to Theorem 1.1.

```
2b4m check openai-wiles/architecture-right.md theWeilPlaneIsSpannedByAlgebraicClasses  # PASSES
2b4m check openai-wiles/architecture-wrong.md theWeilPlaneIsSpannedByAlgebraicClasses  # FAILS
```

| chain | reverse-trace sign | outcome |
|---|---|---|
| `-right` | `+1`, as **[6]** states it (arXiv:1303.0588v2, Lemma 3.4's *proof*, p. 14) — which the manuscript's (3.6) quotes correctly | count closes to `0`, [9, Thm 2.3] applies, Lemma 3.6 and Theorem 1.1 follow |
| `-wrong` | `−1`, as **OpenAI's withdrawal notice** says it should be in the manuscript's convention | count is `I(f₁) + I(f₁) = −2m`, *proved* nonzero, so [9, Thm 2.3]'s hypothesis cannot be met and Lemma 3.6 is unprovable |

Run `./diff-chains.sh` to see the difference. Six files are duplicated; **four differ only in
an import line**. The mathematics diverges in exactly two places: `traces-*.b4m`'s sign axiom
and `stabilization-traces-*.md`'s arithmetic.

**Neither chain decides which convention is right.** [6] assigns `I(G₂) = (−1)^k = +1` in *its
own* convention; the notice asserts a **mismatch** between that index and the manuscript's
signed double-point count — not an error inside [6]. Adjudicating it means comparing two
orientation conventions, which is unformalized here. What the pair establishes is that this
sign is the hinge: everything above §3.4 is kernel-checked and indifferent to it, and §3.4
itself is decided by it.

## What the withdrawal notice says

> The proof contains a sign error in the stabilization-trace argument used to obtain negative
> double points. In the manuscript's signed double-point convention, write `I(f₁) = −m` with
> `m > 0`. The proof assigns each reverse stabilization trace sign `+1` and therefore claims
> that inserting `m` such traces makes the signed count zero.
>
> Accounting for the opposite source orientations of the two branches of the standard cusp
> gives sign `−1` for each reverse trace in this convention. The resulting count is therefore
> `I_new = I(f₁) − m = −2m ≠ 0`.
>
> The Eliashberg–Murphy cancellation theorem invoked at this step requires zero signed
> double-point count, so its hypothesis is not met.

The `-wrong` chain is that paragraph, machine-checked.

## Layout

| file | contents |
|---|---|
| `architecture-{right,wrong}.md` | Theorem 1.1 from §12.4 — the spanning pair of algebraic Weil classes |
| `legendrian/traces-{right,wrong}.b4m` | reference **[6]**'s stabilization traces. **The only file where the two chains differ mathematically at the leaf** |
| `legendrian/stabilization-traces-{right,wrong}.md` | §3.4 and Lemma 3.6 — the insertion argument and its count |
| `construction/marked-class-{right,wrong}.md` | Proposition 12.3, the marked class `aθ⁴ + w` |
| `construction/chern-constancy-{right,wrong}.md` | Lemma 12.2 and §12.4's spreading step |
| `construction/hilbert-parameters.md` | Lemma 12.1's exceptional loci |
| `detection/nonpolarization.md` | Proposition 10.7 — `ζ_s` is outside the span of the polarization powers |
| `detection/transport.md` | Props 11.3, 11.4 and §12.3's Baire choice |
| `eigenvalues/independence-{right,wrong}.md` | §12.4's eigenvalue argument for the second class |
| `parity.b4m`, `signs.md` | 𝔽₂, and the Section 6 sign identities |
| `diff-chains.sh` | prints the right/wrong comparison |

## Section 6's sign algebra checks out

Five of the paper's sign claims were verified independently of the trace question. **All five
are valid** — so the defect is not in Section 6.

- **Lemma 6.2's permutation collapse** — the four determinant-line crossings sum to
  `A + (pz + C)R`, then to equation (6.3). Kernel-verified over all 16 𝔽₂ corners
  (`theCrossingSignsCollapse` in `signs.md`).
- **Lemma 6.2's second step** — `A + (pz+C)R` to (6.3) under `l = i − 1`; valid over all 256
  assignments of its eight parities.
- **Lemma 6.4's cyclic sign** — exhaustive for arities 2 through 6; no mismatch.
- **Section 6.2's reduction** of (6.8) to `v + w + c + (c+q)(v+w+1) + (v+w)(c−1−q) + q = 0`;
  valid over all 16 assignments.
- **Lemma 7.4's intersection sign** — that the local sign at a transverse point is `(−1)^|x|`.
  The orientation discrepancy has exponent `|x| − n`, concatenation contributes
  `(−1)^(n(n−1)/2)`, and at `n = 8` those compose to `(−1)^|x|`. Valid — and the paper flags
  its own dimension-sensitivity ("Since eight is even"); the same argument is false at `n = 9`.

Two observations that explain how a sign error survives this kind of checking:

1. §6.2 says *"We check this cancellation without specifying the bare signs."* Verifying sign
   *differences* rather than absolute signs is exactly how a global `+1`/`−1` flip passes every
   local check.
2. A **convention** imported from a cited source is invisible to any formalization that
   axiomatizes that source *from the citing paper's rendering of it* — it inherits the very
   error it was meant to detect.

## Assumptions

Every unproved step is a `hole` carrying a citation, so strict `check` passes while printing
each locator:

```
2b4m check --axioms openai-wiles/architecture-right.md theWeilPlaneIsSpannedByAlgebraicClasses
```

36 cited holes, drawn from arXiv:1303.0588v2 and arXiv:1303.0586v1, Fulton [14],
Grauert–Remmert [15], Grothendieck [16], Milne [20], and quoted manuscript lines. The only
`axiom`s are 𝔽₂'s theory in `parity.b4m` — a theory's own primitives — plus one predicate
definition. **A citation is not a verification:** the checker cannot confirm that a source says
what a locator claims, which is why it prints them all rather than going quiet.

## Caveats

- **§3.4 is not circular, and `reverseTraceSign` carries no looseness hypothesis.** [6]'s
  Lemma 3.4 *proof* assigns the looseness condition to the destabilization traces `G₃`/`G₄`,
  not to the reverse trace `G₂` — `φ₁` is a stabilization and hence already loose. The
  manuscript's step is sound as cited; the dispute is only about the sign's value.
- **Sections 4–11's symplectic topology is not verified.** Those sections are the origin of
  several cited inputs here (`anAlternatingChernCharacterIsAlgebraic`, §10's Euler-pairing
  identities), and the formalization takes them at their word.
- What is formalized is the **architecture**: Theorem 1.1 from §12.4 downward, plus §3.4's
  count. Not the Hodge-theoretic or Floer-theoretic machinery.
