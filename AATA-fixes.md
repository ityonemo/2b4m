# AATA transcription audit — defects to fix

**Status: AUDIT ONLY. Nothing in this list has been fixed.** Temporary working file.

Audited all 40 files in `aata/` against the vendored book source
(`vendor/aata/src/*.xml`) for two defect classes the user named:

1. **Class 1 — a `fact X = module.y` alias (or a theorem whose whole proof is a
   one-line `[using import(I) thm]` / `[by cite I.thm]` re-export) standing in for a
   proof Judson gives in the running text.** The transcription must reproduce
   *Judson's own proof structure*. Aliasing the **objects** he has in hand (sorts,
   constants, operations, background ring/order algebra) is fine; aliasing the
   **theorems he develops** is not.
2. **Class 2 — prose that is mine rather than Judson's.** The inter-theorem content
   must be a transcription of his exposition, in his order — not a summary, a
   paraphrase, or commentary about the formalization.

### The only legitimate uses of "Judson …" in prose

- **(a)** marking something we **cannot state** (a language limit — e.g. no sort of
  groups, so `≅` cannot be named).
- **(b)** marking a **calculation infeasible** under current arithmetic.
- **(c)** a **deliberate strategy divergence**: must read "Judson does X, we are doing
  Y" **and** sit in a markdown aside (blockquote), not inline.

Everything else is a defect — including import-horizon justifications
("which Judson has in hand by this point"), library-architecture description, and
notes about what the formalization chose. That reasoning belongs in a painpoints file.

**Attribution headers stay** (the "of Thomas W. Judson's *Abstract Algebra*" provenance
block at the top of each file — 96 lines, excluded from all counts below).

## STAGE 0 FINDINGS (2026-10-18) — two things the audit missed

### 1. TEN CHAPTERS PROVE ZERO THEOREMS

Measured per file with `2b4m check <file>`:

    3.2-groups.md            0 theorems proven   (28 declarations)
    6.1-cosets.md            0                   (15)
    6.2-lagranges-theorem.md 0                   (18)
    6.3-fermat-and-euler.md  0                   (6)
    7.2-public-key-crypto.md 0                   (3)
    9.1-definition-and-ex.md 0                   (28)
    9.2-direct-products.md   0                   (23)
    10.2-simplicity-of-An.md 0                   (27)
    4.3-repeated-squares.md  0                   (0)  <- legitimately has no code
    4.3-…-exercises.md       0                   (0)  <- same

`9.1` contains ONE `proof` block in 199 lines and it is a prose word, not a block: every
fenced block in the file is a declaration or an alias. So in these chapters Class 1 is not a
fidelity problem, it is **vacuity** — the corpus's "331 theorems proven" comes entirely from
the other chapters.

**ACCEPTANCE METRIC for the sweep**: a chapter is done when its theorem count is > 0 and
matches the number of results it states. This is the check that would have caught all ten.

### 2. A CHAPTER IMPORTED A FILE THAT DOES NOT EXIST — and `check` passed

`aata/6.2:22` read `import group_lagrange <<< "std/group/group_lagrange.b4m"`. No such file;
the real one is `std/group/lagrange.b4m`. `check` reported `OK: 19 declarations, 0 theorems
proven` because an uncited `fact` alias is never resolved, so the bad import was never opened.

FIXED in Stage 0, along with three imports whose NAME disagreed with their TARGET
(`3.2:21` named `power.b4m` but imported `std/group.b4m`; `4.2:23` named `modulus.b4m` but
imported `std/complex.b4m`; `3.1:24` named `divides` but imported `std/integer.b4m`).

**BUT FIXING THE PATH BUYS NO VERIFICATION.** Tested directly: with the import corrected,
`fact lagrange = group_lagrange.noSuchTheorem` STILL passes `check`. The alias is only
resolved when something cites it. This is [[uncited-fact-alias-proves-nothing]] operating at
chapter scale, and it is why ten chapters could be empty without the gate noticing.

**OPEN ENGINE QUESTION (not fixed here, needs a ruling):** should `check` fail on an
unresolvable import even when no alias from it is cited? Today it does not. Options are to
resolve every import eagerly, or to resolve every `fact` alias at declaration rather than on
first citation. The second is the stronger fix and would also retire the aliasing loophole
that Class 1 depends on.

## Mechanical inventory (whole corpus)

| | count |
|---|---|
| `fact X = module.y` aliases | 561 |
| theorems whose entire proof is a one-line re-export | 67 (34 in main text) |
| Judson-invocation lines in body prose (line > 12) | 252, across 34 files |

Class 2 density, worst first: 5.1 (31), 10.2 (26), 2.3 (20), 2.2 (13), 4.1 (12),
9.1 (10), 11.2 (10), 6.2 (9), 5.2 (9), 3.3 (9), 3.2 (8).

---

# Chapters 3–4

Counts: Class 1 / Class 2 (OK-AS-IS marked separately).

| file | C1 | C2 | note |
|---|---|---|---|
| 3.1-integers-mod-n.md | 0 | 7 (1 ok) | aliases all legit; §3.1 proposition really proved |
| 3.1-integers-mod-n-exercises.md | 0 | 3 | |
| 3.2-groups.md | **12** | 9 (1 ok) | **entire "Basic Properties" subsection is aliases** |
| 3.2-groups-exercises.md | 6 | 5 | |
| 3.3-subgroups.md | **7** | 9 (1 ok) | **every theorem is a one-line re-export** |
| 3.3-subgroups-exercises.md | 0 | 5 | forwards correctly |
| 4.1-cyclic-subgroups.md | **0** | 9 (2 ok) | **CLEAN on Class 1 — the model to copy** |
| 4.1-cyclic-subgroups-exercises.md | 0 | 7 (2 ok) | forwards correctly |
| 4.2-complex-multiplicative-group.md | **11** | 6 (2 ok) | **all 11 theorems are one-line re-exports** |
| 4.2-…-exercises.md | 0 | 2 (1 ok) | |
| 4.3-repeated-squares.md | 0 | 3 (1 ok) | no code at all |
| 4.3-repeated-squares-exercises.md | 0 | 1 (1 ok) | |

## 3.2-groups.md — Class 1 (12)

Every result Judson proves in `groups-subsection-basic-properties` is an alias. All are
real theorems in `std/group.b4m` from the same five axioms, so in-place proofs are
**feasible** (the proof text exists and would be transcribed):

- `:206` `identityUnique` ← `group.identityUnique` — uniqueness of identity.
  Judson `groups.xml` `<proposition>` 684, `<proof>` 693–704 ("$e = ee' = e'$"). std:127
- `:221` `inverseUnique` ← `group.inverseUnique` — Judson `<p>` 706–715
  ("$g' = g'e = g'(gg'') = (g'g)g'' = eg'' = g''$"). std:154
- `:234` `invProduct` ← `group.invProduct` — $(ab)^{-1}=b^{-1}a^{-1}$.
  `<proposition groups-proposition-inverse-of-products>` 726, `<proof>` 734–742. std:203
- `:249` `invInvolution` ← `group.invInvolution` — `<proposition>` 745, `<proof>` 753–762. std:240
- `:266` `solutionExists` + `:273` `solutionUnique` ←
  `<proposition groups-proposition-group-equations>` 773, `<proof>` 781–795. std:267, 295
- `:286` `cancelRight` + `:292` `cancelLeft` — Judson **states** (`<proposition>` 798) and
  forwards to Ex. 30; the exercises file forwards *back* here, so the chapter has **no
  proof at all**. std:363, 418
- `:322/324/326/328` the four Laws of Exponents ← `group_power.power*`
  (`<theorem groups-theorem-exponent-laws>` 827, left as Ex. 29; exercises forward here).
  Heaviest to prove (bidirectional integer induction) but same forwarded-exercise rule.

LEGIT, do not touch: `:24–32` sort/const/op/inv + the five group axioms; `:35–39` Int objects.

## 3.2-groups.md — Class 2 (9)

- `:190–194` "**here each is presented in the book's notation and argument, and aliased to
  its library proof — so this transcription shows *what* Judson proves and *why*, while the
  checked derivation lives in the library**" — the Class-1 defect announced as policy.
- `:200–203` "**The book argues**: … **We capture uniqueness as** any left identity…" —
  his proof paraphrased in one clause, then replaced by a description of the library
  statement. Also a real divergence (two-identity vs "any left identity equals e") stated inline.
- `:215–218` "The proof is **the book's own chain**…" — false of this file; the block is an alias.
- `:230–231`, `:245–246`, `:262–263`, `:269–270`, `:282–283`, `:289` — descriptions of
  proofs the file does not contain ("Formally: we compute…", "Left cancellation is the
  mirror image"). `:245` also silently diverges from his multiply-both-sides argument.
- `:311–318` "**Judson leaves the proof as Exercise 29.** … **We import the four results here.**"
- `:62–70` library description; `:178–184` editorial; `:280` paraphrase of "We leave the
  proof as an exercise."
- OK-AS-IS(a): `:42–46` the §3.1 sort-limit note — **but** it says §3.1 is "not
  transliterated as formal content", which is false: `aata/3.1-integers-mod-n.md` exists.

## 3.3-subgroups.md — Class 1 (7, plus a theorem→axiom conversion)

All seven theorems are a single `[using import(subgroup) …]` step. All targets are real
theorems in `std/subgroup.b4m`; each is a handful of steps, **feasible**:

- `:91` `closedUnderDivide` ← `subgroupClosedDivide` —
  `<proposition groups-proposition-subgroup>` 1155, `<proof>` 1164–1170. std:148
- `:119/126/133` `oneStepGives{Identity,Inverses,Products}` — same `<proof>`, the three
  computations "$gg^{-1}=e$", "$eg^{-1}=g^{-1}$", "$h_1(h_2^{-1})^{-1}=h_1h_2$". std:188, 215, 249
- `:157/164/171` the three intersection conditions — Judson's Ex. 45; the exercises file
  forwards here, so the chapter has no proof. std:308, 322, 378

**STRONGEST DEFECT IN THE FILE — a proved theorem converted to axioms.** The three-condition
subgroup criterion (`<proposition>` 1103 with a full `<proof>` 1130–1152: $e_H=e$ by right
cancellation, closure, $h'=h^{-1}$ by uniqueness) is **not stated as a theorem at all**.
`:39–43` and `:69–72` declare it *taken as the axioms* of `std/subgroup.b4m`.
Recommended split: the **converse** half is expressible today — prove it; the **forward**
half needs "H is a group in its own right" (no sort of groups) — mark as a language limit
naming exactly what it needs.

## 3.3-subgroups.md — Class 2 (9)

- `:10–13`, `:39–43`, `:61–65`, `:69–72`, `:78–80`, `:82–84`, `:146–151` — library
  description and the alias strategy; `:39–43` ends "**the results derive from it exactly as
  the book derives them from the definition**", which is false (he derives the criterion
  *from* the definition; here it *is* the definition). `:61–65` and `:146–151` cite **raw XML
  line numbers** in transcribed prose.
- `:17–22` (iii) the Definition paragraph is a paraphrase: his `<p>` 930–941 (with the
  $2\mathbb{Z}$ motivating example) is compressed to three sentences, the example **dropped**,
  and "$H \le G$ / $H < G$" notation added that he does not use here.
- `:47–59` (iii) his five `<example>` blocks (943, 978, 987, 1025, 1058 — $\mathbb{Q}^*$ with
  four verifications, $\{1,-1,i,-i\}$, $SL_2(\mathbb{R})$, the $GL_2\not\le M_2$ non-example
  with explicit matrix sum, $\mathbb{Z}_4$ vs $\mathbb{Z}_2\times\mathbb{Z}_2$ with its table
  and three subgroups) → a **four-bullet list of one-line gists**.
- `:141–142`, `:179–180` the conclusions "so $K \le G$" written as prose because the step is
  unprovable (criterion is an axiom) — gap unmarked.
- OK-AS-IS(a): `:99–112` "`2b4m` cannot quantify over subsets" — real limit, load-bearing.

## 4.2-complex-multiplicative-group.md — Class 1 (11)

All 11 theorems are one-line re-exports of `std/complex/{modulus,polar}.b4m`; all **feasible**:

- `:158` **`deMoivre`** ← `polar.deMoivrePolar` — **the clearest defect in the file**: the one
  §4.2 theorem with a complete in-text proof (`<theorem><title>DeMoivre</title>` 544,
  `<proof>` 560–574, angle-addition written out line by line) is a one-line citation. polar:624
- `:96` `modulusMultiplicative` ← `absMul` — the load-bearing result; his circle-group
  proposition is stated as "a direct result of" polar multiplication. modulus:204
- `:74` `conjugateProduct` (modulus:69), `:85` `modulusOfConjugate` (modulus:116)
- `:135` `cisProduct` + `:142` `polarProduct` ←
  `<proposition cyclic-proposition-polar-mult>` 524. polar:376, 518
- `:150` `modulusOfCis` (polar:492)
- `:201` `rootAngleExists` + `:208` `rootsOfUnity` ← roots-of-unity theorem 631,
  `<proof>` 644–656. polar:831, 769
- `:215/222/229` the three circle-group subgroup conditions ← `<proposition>` 612. polar:886, 911, 961

## 4.2-complex-multiplicative-group.md — Class 2 (6)

- `:6–12` **factually wrong**: "the analytic material (polar form, DeMoivre's theorem, the
  roots of unity) needs trigonometry that `2b4m` does not yet have, and is transliterated as
  prose" — the file **does** formalize all three (`:135–163`, `:201–213`). Contradicted by
  `:116–122`, which says the trigonometry *is* adjoined.
- `:14–19` "**By Chapter 4 the reals and the field axioms are in hand**…" — import-horizon.
- `:56–59`, `:63–68` library mapping + "proved elsewhere, stated here".
- `:116–122` reveals an **undisclosed divergence**: the trig identities DeMoivre needs are
  **axioms** in `std/real/trig.b4m`; his proof assumes none. Not marked as a divergence.
- `:179–195` interleaves a real OK-AS-IS(a) limit note (all roots of $z^n=1$ forwards to the
  degree-$n$ root bound, a later chapter — he defers too) with the circle-group sketch,
  losing his exposition order.
- (iii) **largest omission set in the scope, all unmarked**: `cyclic-example-complex-add`
  ($z=2+3i$, $w=1-2i$), the rectangular representation `<p>` + figure, the polar-coordinates
  `<p>` (with $0\le\theta<2\pi$ well-definedness), `cyclic-example-polar` (both directions),
  `cyclic-example-polar-mult`, the $(1+i)^{10}=32i$ example, the $H=\{1,-1,i,-i\}$/$z^4=1$
  paragraph, and `example-roots_unity` (8th roots + figure). `:43–54` compresses three `<p>`s
  into one; `:106–114` compresses the polar `<p>`, the proposition and the whole DeMoivre
  proof into one paragraph.

## 3.1, 3.2-exercises, 3.3-exercises, 4.1, 4.1-exercises, 4.3 — selected

**3.1-integers-mod-n.md** C1 clean (the proposition parts 1 and 6 are really proved,
including Bézout). C2: `:11–14`, `:18–20` ("**which Judson has in hand by this point in the
book**"), `:35` and `:78–80` import-horizon/formalization notes; `:105–111` pure
project-status commentary ("a dedicated exercises pass … not yet run"); `:144–147`
**misstates the source** — attributes "the recurring move in Judson's proof of (1)–(5)" to
him, but he proves only (1) and (6) and his (1) argument is about *remainders*, not
differences being 0; `:485–490` a correct divergence (dropping his "nonzero $b$") but stated
inline with "Judson says". (iii) **the entire §3.1 symmetries subsection**
(`groups-subsection-symmetries` 230–345: symmetries of the triangle, $S_3$/$D_3$, the Cayley
table) is **absent from a file titled "…and Symmetries"**, as are two examples
(`groups-example-zn-addition`, `groups-example-zn-arithmetic-laws`), with no deferral note.

**3.2-groups-exercises.md** C1 (6): `:30–33` re-export main-text results (`cancelLeft/Right`,
`invProduct`, `invInvolution`) — once 3.2 proves them these should cite the main text;
`:685/687` **Exercise 31 is "answered" by two bare `fact` aliases with no theorem and no
proof** — a real proof is trivial (two steps from `inverseUnique` + `invProduct`, exactly as
`:679–682` describes). C2: `:96–104`, `:161–167`, `:202–207`, `:259–266`, `:693–701`
library-architecture paragraphs; `:243–253` a **tool-limitation bug report** inside the
transcription (`simplify` cannot discharge a guard premise) carrying a project to-do.

**3.3-subgroups-exercises.md** C1 clean; forwards correctly — but `:533–535` points at a
main-text section whose own proof is an alias, so **the pointer resolves to nothing proved**.
C2: `:48–56` Ex. 34 a genuine divergence (he asks for the subgroups, we prove the exponent
inequality) stated inline, not as an aside; `:2100–2108` Ex. 50 proves *unboundedness*, not
infinitude — real divergence, inline; `:2549–2552` "**which Judson has by §3.2; we cite it
from `std/subgroup.b4m` … rather than re-deriving it**" — refinement-1 pattern exactly.

**4.1-cyclic-subgroups.md** — **C1 CLEAN, the model for the rest of the corpus.** Every §4.1
result is a real transcribed proof (⟨a⟩ is a subgroup, cyclic ⇒ abelian, subgroups of cyclic
are cyclic, the order/divisibility propositions); no `fact` aliases at all. C2 (9): `:11–17`
an **entire paragraph of import-horizon reasoning** attributed to Judson; five "**Judson's
proof:**" attribution tags (`:75`, `:261`, `:364`, `:700`, `:920`) prefixed to otherwise
faithful transcriptions — should just be **Proof.**; `:376–380` + `:494–497` an **unmarked
divergence**: he *derives* $m$ from well-ordering, here $m$'s existence and minimality are
**axioms**, and `wellordering` is imported at `:24` but never used, making the gap look
closed; `:926–931` + `:950` same shape — `axiom cofactorBezout` with prose claiming "which
holds because $d=\gcd(k,n)$", but **there is no `gcd` in the file**; (iii) his four cyclic
examples (incl. the $U(9)$ power table and the $S_3$ subgroup lattice) compressed to one
paragraph. **OK-AS-IS(c) — the best-formed note in the scope**: `:382–391` the
`memberPowerInH` blockquote, explicitly "Judson writes … in one breath; for a machine-checked
proof that elision has to be discharged". Only quibble: it claims to be "the only step …
elided in the book and spelled out here", contradicted by the two axiomatizations above.
OK-AS-IS(a) `:83–86` (no quantification over predicates; phrasing nit — it says "over group
elements").

**4.1-cyclic-subgroups-exercises.md** C1 clean, forwards correctly (Ex. 32, 35, 36, 38).
C2: `:12–23` twelve lines of library design (the `hasOrder` relation vs an `ord` function);
`:678–695` **eighteen lines of model architecture**, the densest instance; `:593–599` Ex. 27
and `:918–926` Ex. 37 are real, honestly-disclosed divergences (a weakened hypothesis for
Ex. 37: cyclic subgroups only, since quantifying over subgroups is not expressible) but
**stated inline, not in asides**; `:511` "the criterion behind Judson's corollary" silently
supplies a main-text result the main text leaves as prose. OK-AS-IS: `:648–657` (divisor-lattice
distributivity missing from `std/integer` — correctly scoped), `:408–413` (b).

**4.3-repeated-squares.md** C1 clean (no code). C2: `:6–9` corpus-coverage commentary;
`:48–61` the "cannot currently be encoded" block is **the right form** and its core is
OK-AS-IS(a/b) — but it (a) invokes Judson's footnote to justify *our* coverage decision,
(b) carries a project roadmap note, (c) says the ℤ_n sort is "within reach" when 3.1/3.2
exercises **already use** `std/integer/mod-n.b4m`. (iii) his opening ($2^{2^{1,000,000}}$,
"thousands or even millions of digits") compressed; the worked example's intermediate
arithmetic and the identity $(a^{2^n})^2 \equiv a^{2^{n+1}}$ dropped.
**4.3-exercises** C2: `:7–13` OK-AS-IS(b) core, but trailing meta-commentary about "the
corpus's treatment of brute numeric exercises" and it inherits §4.3's inaccurate ℤ_n claim.

## Cross-cutting (chapters 3–4)

1. **Import-path mismatches** — prose describes a dependency the code does not have:
   `3.2-groups.md:21` imports `std/group.b4m` while its comment and the whole Laws-of-Exponents
   discussion say `std/group/power.b4m`; `4.2:23` imports `std/complex.b4m` where the prose says
   `std/complex/modulus.b4m`; `3.1:24` `import int_divides <<< "std/integer.b4m"`.
2. **Two files in one chapter give opposite accounts of the trigonometry gap** —
   `4.2-…-exercises.md:5–15` defers exercises on "the absent trigonometry" while
   `4.2-…-group.md:116–122` says it is adjoined and uses it to prove `cisProduct`/`deMoivre`.

---

# Chapters 1–2

| file | C1 | C2 | note |
|---|---|---|---|
| 1.2.1-sets.md | 0 | 15 (1 ok) | all 14 theorems proved from scratch — correct |
| 1.2.1-sets-exercises.md | 0 | 5 + 6 omissions | **every exercise number is wrong** |
| 1.2.2-functions.md | 0 | 9 | `:52–157` is **the target standard** |
| 1.2.2-functions-exercises.md | 0 | 5 + 7 omissions | every exercise number wrong |
| 1.2.3-relations.md | 0 | 6 + 4 omissions | 4 examples silently dropped |
| 1.2.3-relations-exercises.md | 0 | 5 (1 ok) | |
| 1.2.3-partitions.md | 0 (+2 adj) | 11 + 5 omissions | 2 shipped "(Proof to fill:)" TODOs |
| 2.1-induction.md | **2** | 6 | **Judson's §2.1 prose almost entirely absent** |
| 2.1-induction-exercises.md | 0 | 4 | |
| 2.2-division-algorithm.md | **0** | 9 | **C1 exemplary** — proves the Division Algorithm in full |
| 2.2-…-exercises.md | 0 | 5 | |
| 2.3-primes.md | **3** | 22 | ~zero transcribed Judson prose outside 4 blockquotes |
| 2.3-primes-exercises.md | 1 | 5 | |

## Class 1 — all six instances, all chapter 2, none blocked

- `2.1:237–238` `nonnegStrongInduction` + `nonnegWellOrdering` ← `wellordering.*`.
  **Judson proves both in-text**: `integers.xml <lemma integers-lemma-smallest-number>`
  ("PMI implies 1 is the least positive natural number", full proof) and
  `<theorem integers-theorem-pmi-implies-pwo>` ("PMI implies Well-Ordering", full proof).
  **Neither is stated anywhere in `aata/`** (grep-verified). Proofs exist in
  `std/integer/wellordering.b4m:492`; his PWO proof is an induction on the bound, mirroring
  `strongInduction`. **The clearest Class-1 defect in the audit** — two named in-text
  results reduced to two alias lines.
- `2.3:36–37` `divisionAlgorithmExists` + `divisionAlgorithmUnique` ← `int_divides.*`.
  **Pure redundancy**: the sibling `2.2-division-algorithm.md:645/289` proves both in full.
  **Trivially fixable** — cite the §2.2 theorems instead of the library duplicate.
- `2.3:143` `nonnegWellOrdering` — same defect as `2.1:237`, inherited.
- `2.3:1154` `primeFactorExists` ← `sequence.*` — **borderline, needs a ruling**: Judson
  does not state it separately (his FTA-existence case derives it inline from
  Well-Ordering), so importing is defensible; but it is that proof's load-bearing step and
  `ftaExistence` leans on it.
- `2.3-primes-exercises.md:32` `divisionAlgorithmExists` — mildest (exercise file, `std`
  permitted), but should point at §2.2's proof.

## Class 2 — the dominant failure is structural, not phrase-level

In `2.1`, `2.2`, `2.3-primes`, `1.2.3-relations` and `1.2.3-partitions`, the inter-code prose
is **a narration of our proof architecture with Judson's text absent entirely**. Grepping
"Judson" finds symptoms; the disease is the missing exposition.

**The target standard** (do not change these): `1.2.2-functions.md:52–157` — Judson's §1.2.2
transcribed verbatim and in order (Cartesian product, $A^n$, relations/mappings/domain/range,
the cube remark, well-defined $p/q$, onto/injective/bijective, composition, $4x^2+20x+25$,
linear maps, permutation π), with the figure honestly marked using the XML's own
`<description>`. Also `1.2.1-sets.md:40–160`.

### 2.1-induction.md
- `:8–20` **two near-duplicate paragraphs**, both opening "The integers are the axiomatic
  theory `std/integer.b4m`…" — an editing artifact.
- `:74–75` "Judson takes induction directly on $\mathbb Z$; we ground it in Peano $\mathbb N$
  instead." — **the best-worded divergence in chapters 1–2**, exactly the (c) form, but
  **inline**. Promote to a blockquote and it conforms.
- `:84–89` substitutes our $3\mid4^n-1$ for his `integers-example-induction-divisible`
  ($9 \mid 10^{n+1}+3\cdot10^n+5$) and **justifies the swap by convenience**; his example is
  never transcribed (it is Ex. 5 in the exercises file, so a pointer would do).
- `:224–230`, `:248–257` library commentary standing exactly where his Lemma and Theorem belong.
- (iii) **Judson's §2.1 prose almost entirely absent** (grep-verified): the motivating opening
  ("impossible to verify for all natural numbers on a case-by-case basis"), the worked $(n+1)$
  derivation, "This method of proof is known as mathematical induction",
  `integers-example-induction-greater-than` ($2^n>n+4$),
  `integers-example-binomial-theorem` (the full induction), and the closing "Induction can
  also be very useful in formulating definitions" with the two factorial definitions.
  **The two blockquoted Principles are the only Judson text in the file.**

### 2.2-division-algorithm.md — Class 1 exemplary, Class 2 not
- `:8–17` the governing defect: "*What we import is only what '**Judson already has in hand**'
  at this point in the book*" — import-horizon reasoning verbatim, opening the file where his
  "An application of the Principle of Well-Ordering that we will use often is the division
  algorithm" should stand.
- `:17` and `:105` **text corruption**: a global replace turned the English word into the
  identifier — "are transcribed as real proofs **less_than**." and "lies strictly
  **less_than** $b$". `:17` is ungrammatical.
- `:90–97`, `:128–138`, `:456–467` his `<proof>` **summarized** rather than transcribed, then
  sliding mid-paragraph into our lemma names. His opener — "This is a perfect example of the
  existence-and-uniqueness type of proof…" — is never transcribed (grep-verified).
- `:103–110`, `:116–120` "the one **Judson invokes when he writes**…", "**Judson also uses**…"
  — quoting him to introduce library lemmas.

### 2.3-primes.md — 22 passages, ~zero transcribed prose
- `:250–257` and a second instance at `:1337–1341`: "**TEMPORARY placement:** … the
  model-spaces refactor … will move it back" — **a repo roadmap note shipped in the
  transcription**.
- `:410, 412, 428, 2030, 2668, 3747` **six more `less_than` corruptions** ("`−1` is
  *less_than* zero", "the Well-Ordering instance **less_than consumes**"); `:428` is ungrammatical.
- `:1419–1425` "`ℤ`'s **intuitionistic kernel offers no free excluded middle**" and
  `:1593–1599` "**Judson takes `gcd(a,p)=1` for granted** … so we prove it" — real divergences,
  inline, (c)-eligible but non-conforming.
- `:1268–1275, 1298, 1343, 1350–1353, 1409–1413` six consecutive tactic/accelerant-internals
  passages ("**deliberately NOT by an `arithmetic` step**, since that certifier resolves
  `mulOneLeft` among its own ring lemmas").
- `:2025–2031, 2616–2622, 2736–2739, 2851–2854, 3000–3008, 3739–3749, 3914–3924, 4394–4406,
  4804–4806, 4845–4849, 4915–4917, 4958–4975, 6336–6356, 6593–6596` — **fourteen further
  passages** of proof-architecture narration keyed to our identifiers. Judson has no counterpart.
- (iii) **invented and colliding result numbers** (the XML carries **none**): "Theorem 2.10"
  (`:529`) collides with "Definition 2.10" (`:1120`); "Corollary 2.11" (`:958`) collides with
  "Lemma 2.11" (`:1815`).
- (iii) **his definitional paragraph dropped entirely** — $a\mid b$, **common divisor**,
  **gcd**, $\gcd(24,36)=12$, $\gcd(120,102)=6$, **relatively prime**; "composite" never
  appears in the file. His §2.2.1 Euclidean Algorithm subsection (the 945/2415 worked example,
  back-substitution to $r=-5,s=2$, the $r_1>r_2>\cdots>r_n=d$ display) is absent — "945"
  occurs nowhere. Historical Note (Fermat, Euler's $2^{2^5}+1$, Goldbach) absent.

### Chapter 1 — three FALSE statements, all independently verified
These are wrong regardless of prose policy:
- `1.2.2-functions.md:600` marks the backward direction "which `2b4m` cannot yet encode" —
  **but `:858` proves `bijectiveImpliesInvertible` in full.** A fabricated language limit
  contradicting the file's own content.
- `1.2.1-sets-exercises.md:104–106` defers $A\subset B\iff A\cap B=A$ because
  "`std/set.b4m` does not yet model $\subset$" — **`std/set.b4m:58` defines `subset`.** Feasible.
- `1.2.2-functions-exercises.md:30–35` says "`std/function.b4m` does not package it"
  (`composeAssoc`) — **`std/function.b4m:108` provides it.**
- Also stale: `1.2.3-relations.md:27–36` "What this file does NOT reach is … equivalence
  classes and partitions" — **falsified by `1.2.3-partitions.md`**, which does exactly that;
  the exercises file at `:93` even says "Now done".

### Chapter 1 — other items
- **Every exercise number is wrong in both ch-1 exercise files.** Verified against the XML:
  `1.2.1-sets-exercises.md` labels $(A\cup B)\setminus B=A\setminus B$ "Exercise 8" when
  Judson numbers it **13** (his 8 is the subset biconditional); "6"→**10**, "10"→**14**,
  "11"→**15**, "12"→**16**. `1.2.2-functions-exercises.md:103` labels Judson's **19** as 25.
- `1.2.3-partitions.md:484` **`axiom quotientContains` is a new axiom invented in a
  transliteration**, self-justified at `:476–480` ("This is honest"). Judson needs none —
  $\{[x]:x\in X\}$ is comprehension. Per the repo's own axiomatization rule this should be a
  `hole`, not an `axiom`.
- `1.2.3-partitions.md:822–824` the Theorem's **converse**, which Judson proves in-text
  (`<proof>` ¶2), is dropped with "it is left to a later section" — **false; §1.2.3 has no
  later section**. Feasible: define `related(x,y) := ∃s; contains(s,P) and member(x,s) and
  member(y,s)`; the three properties follow from `covers`/`pairwiseDisjoint`, already imported.
- `1.2.3-partitions.md:103, 276` **two shipped authoring TODOs**: "**(Proof to fill: …)**".
- `1.2.3-partitions.md:275–277` **Judson's named `<corollary>`** ("Two equivalence classes are
  either disjoint or equal") **is never stated** — it survives as a lower-case clause in our prose.
- `1.2.3-partitions.md:9–26` ~18 lines of library architecture **displacing** his partition
  definition, his equivalence-class definition $[x]=\{y\in X: y\sim x\}$, and "whenever a
  partition of a set exists, there is some natural underlying equivalence relation".
- (iii) **nine of Judson's ten §1.2.3 examples silently dropped**, no marker. Worst:
  `sets-example-congruent-integers` — the definition of $r\equiv s\pmod n$, $41\equiv17\pmod 8$,
  the explicit reflexive/symmetric/transitive verification ($r-t=kn+ln=(k+l)n$), the $[0]/[1]/[2]$
  mod-3 display, and the forward reference to the division algorithm. **Not blocked** —
  `aata/3.1-integers-mod-n.md` formalizes this relation today, and the prose needs no proof.
- `1.2.1-sets.md:1182–1187` the file's worst: a **summary of** his De Morgan `<proof>`
  substituting for it; his two paragraphs (incl. the $A\cup B=\emptyset$ special case) never appear.
- `1.2.1-sets.md:164–183` checker-engineering commentary ("so that closing the second with
  `generalize` does not trip the eigenvariable escape check") and tactic-selection meta-prose.
- `1.2.2-functions-exercises.md:37–99` `composeAssoc` is **re-proved verbatim** from the main
  text; the guide says a main-text-proved result gets a prose pointer, not a re-proof.
- `1.2.2-functions.md:493–510, 1067–1069` his two `<proof>` texts *are* transcribed well — but
  placed **after** all the formal proofs and pre-empted by our paraphrases; his order is lost.

**No `hole`s anywhere in chapters 1–2** (verified across all 13 files) — the guide's no-holes
rule is respected.

---

# Chapters 5–7

| file | C1 | C2 defect | C2 ok |
|---|---|---|---|
| 5.1-permutation-groups.md | 7 | **24** | 3 |
| 5.1-permutation-groups-exercises.md | 1 | 6 | 0 |
| 5.2-dihedral-groups.md | 1 | 9 | 1 |
| 5.2-dihedral-groups-exercises.md | 2 | 3 | 0 |
| 6.1-cosets.md | 5 | 8 | 2 |
| 6.2-lagranges-theorem.md | 7 | 9 | 2 |
| 6.3-fermat-and-eulers-theorems.md | 4 | 6 | 2 |
| 7.1-private-key-cryptography.md | **0** | 4 | 1 |
| 7.2-public-key-cryptography.md | 2 | 4 | 2 |
| **total** | **29** | **73** | **13** |

**Chapter 6 is systematically aliased: §6.1 + §6.2 + §6.3 contain 19 `fact` aliases and ZERO
transcribed proofs** — while quoting Judson's proofs verbatim in the prose immediately above
each alias. Every underlying std theorem is proved, in the 24–214 line range.
**§7.1 next door contains a hand-written 95-line kernel proof of a lesser result**, so the
Chapter 6 aliasing is a choice, not a capability limit. §7.1 is the Class-1 model for the corpus.

## 6.2-lagranges-theorem.md — Class 1 (7): the title theorem as a one-liner

- `:75` **`lagrange`** ← `group_lagrange.lagrange` — **Lagrange's Theorem itself**
  (`cosets.xml <theorem cosets-theorem-lagrange>`). Its two-line Judson proof is **quoted at
  `:66–67`** and then aliased. **`std/group/lagrange.b4m`, 73 lines.** The single most
  conspicuous Class-1 defect in the whole audit.
- `:57` `everyCosetIsListedByTheSubgroupsLength` — **Lemma 6.8**
  (`<proposition cosets-theorem-4>`), full Judson proof, **quoted at `:45–50`** then aliased. 214 lines.
- `:82` `theSubgroupsLengthDividesTheGroups` — the second half of Lagrange's statement. 92 lines.
- `:103` `theOrderDividesTheGroupsLength` — **Corollary 6.10**; he states it without proof
  (immediate from Lagrange), so defensible — but it is what 6.11 and §6.3 both rest on, and
  nothing in the chapter proves it. 92 lines.
- `:116` `primeOrderGroupIsGeneratedByAnyNonIdentity` — **Corollary 6.11**, which he proves;
  proof **quoted at `:111–113`**, then aliased. 150 lines.
- `:139` `indicesMultiplyAlongAChain` — **Corollary 6.12**, proof quoted at `:129–131`, then aliased. 66 lines.
- `:90` `anyTwoGroupListingsHaveTheSameLength` — **LEGITIMATE** (an artifact of the listing
  encoding, not a Judson result). Do not fix; listed for completeness.

## 6.1-cosets.md — Class 1 (5)

- `:103` **`cosetsAreEqualOrDisjoint`** — **Theorem 6.4**, which he proves in the running text
  (`<theorem cosets-theorem-theorem-2>`). **The .md quotes that proof verbatim at `:91–96`**
  and then replaces it with a one-line alias. 71 lines.
- `:54` `elementIsInItsOwnCoset` — the covering half of 6.4's partition. **24 lines.**
- `:74`, `:82` the two Lemma 6.3 equivalences — he leaves 6.3's proof as an exercise and there
  is **no §6.1 exercise file**, so by the guide these are forwarded results owed a main-text
  proof. **Borderline** — but §6.1 then contains no mathematics at all. 111 and 130 lines.
- `:128, 135, 136, 137` the four translation/listing facts — **Lemma 6.8**, whose proof he gives
  in full; aliased here **and again at `6.2:57`**.

## 6.3 and 7.2 — Class 1

- `6.3:55` `anElementToTheGroupsLengthIsTheIdentity` — **the whole mathematical content of
  Theorem 6.16 (Euler's Theorem)**, proof **quoted at `:40–42`**, then aliased. 74 lines.
  With `:63` and `:69`, **Euler's Theorem is three aliases and no transcribed proof.**
- `6.3:29` `unitsAreListed` ← `mod_n_listing.znSplitsAtUnits` — a **statement/alias mismatch**:
  the aliased statement is a listing-split, not Theorem 6.15 ($|U(n)|=\varphi(n)$). The file
  says as much at `:21–23`. He states 6.15 without proof, so report as mismatch, not stolen proof.
- `7.2:46` `anExponentOneAboveAMultipleOfTheOrderIsTheIdentityMap` — **the RSA correctness
  argument**, which he writes out ($y^D=(x^E)^D=x^{km+1}=(x^{\varphi(n)})^kx=x \bmod n$).
  **Quoted at `:224–228`**, then aliased. 76 lines.
- `7.2:53` `anElementToTheGroupsLengthIsTheIdentity` — Euler again, **the third alias of the
  same theorem** in the scope.

## 5.1-permutation-groups.md — Class 1 (7)

- `:206` `symmetricGroupHasFactorialManyElements` — $|S_n|=n!$. He forwards it ("We leave the
  proof that $|S_n|=n!$ as an exercise") and it recurs as Ex. 28, so **the guide requires a
  main-text proof**. `std/permutation/count.b4m:2268`; `:187–197` already narrates the argument.
- `:275` `disjointCyclesCommute` — **he proves this in full** (`<proposition>` in
  `permute-subsection-cycle-notation`, a three-case proof on where $x$ lies). **The
  transcription has no trace of the case split.** `std/permutation.b4m:490`.
- `:281` `everyPermutationIsAProductOfDisjointCycles` — he proves it in the running text (build
  $X_1=\{\sigma(1),\sigma^2(1),\dots\}$, take the first $i\notin X_1$, iterate).
  `std/permutation/decomposition.b4m:1617`.
- `:478–484` `identityIsEvenLength` — **a one-line re-export of Judson's Lemma**
  (`<lemma permute-lemma-identity-even-trans`), **whose four-case proof he writes out over four
  paragraphs**. The central lemma of the section. `std/permutation/parity.b4m:5493`.
- `:309` `cycleIsAProductOfTranspositions` — borderline (it is `cycle`'s library definition) but
  the §5.1 claim is a stated result. `:310` is defensible (he gives no proof) **except both its
  inputs are aliases**, so none of the chapter's development is reproduced.
- `:1395–1397` the three listing facts carrying Judson's $|A_n|=n!/2$ bijection argument.
  Mildest — `alternatingGroupHasHalfTheElements` does assemble a real proof — but the
  bijection-gives-equal-counts step, which **is** his argument, is the aliased piece.

## 5.1 — Class 2 (24): the file contradicts itself about its own lemma

**HIGHEST-PRIORITY ITEM IN THE SCOPE.** `:322–343` asserts Judson's Lemma is out of reach and
axiomatized — "*Three things put this out of reach … So the lemma is assumed here exactly as
Judson states it … `2b4m check --axioms` discloses it, so nothing is hidden*" — while **the
code comment at `:465–474` says it was proved on 2026-09-30 and that those three obstacles
were "illusory"**, and `:478` cites a real proof. Two mutually contradictory accounts of the
same lemma in one file. The stale prose should be deleted; its replacement is the transcription
of his four-case proof.

- `:10–15` "**Import horizon.** By Chapter 5 Judson has, and we import: …" — refinement-1 pattern.
- `:17–31` "What this section can and cannot encode" — **stale twice over**: the cycle results
  ARE now encoded (`:275`, `:281`) and the lemma is NOT taken as stated.
- `:329–333` his **four-paragraph** `<proof>` compressed to five lines of reported speech.
- `:1348–1360` 13 lines describing the *encoding*, his own proof reduced to one clause.
- `:2460–2467` "**Note the two places where the transliteration must say more than the book
  does**" — explicit formalization commentary naming our lemma names.
- `:231–241`, `:295–302`, `:69–73`, `:1023–1024`, `:64–67`, `:192` — library internals and
  reported speech; `:295–302`'s "exactly as Judson's do" justifies a formalization shape.
- `:222–223` **a silent definitional divergence presented as his text**: the .md defines
  "disjoint" by *support*-disjointness (the library's form); Judson writes "$a_i\neq b_j$ for
  all $i$ and $j$" (index form). Not flagged anywhere.
- (iii) **omissions, no marker**: `permute-example-s5` (the $4\times4$ table),
  `permute-example-s4-nonabelian`, three cycle examples, the transposition computation
  $(1\,6)(2\,5\,3)=\ldots$, `permute-example-s4` ($A_4$'s twelve elements, "there is no
  subgroup of order 6. Does this surprise you?"), the Cauchy Historical Note, the
  `<remark>` "we often denote the identity permutation by $(1)$", **his Theorem
  `permute-theorem-even-and-odd` statement** (surfaces only as code at `:847`), and **the
  even/odd definition** (only as a code comment at `:486`).
- (iii) **the most consequential omission in the scope**: his `<remark>` fixing the composition
  convention — "*We will adopt the convention of multiplying permutations right to left*" —
  is **absent**, while the whole chapter's `compose` usage silently assumes it.

## 5.2, 6.x, 7.x — Class 2 selected

**5.2-dihedral-groups.md** C1: `:41` `dihedralGroupHasTwiceNElements` — **his first §5.2
theorem** ($D_n \le S_n$ of order $2n$, whose $2n$ count he derives), aliased wholesale;
`std/permutation/dihedral.b4m:6059`, and `:20–33` already narrates the argument.
C2: `:54–58` a real divergence (he derives the relations geometrically; **we postulate them as
`axiom`s at `:88–89`**) stated **inline**, with editorializing ("the part of the theorem with
mathematical content"); `:211–224` an entire section of commentary on our own four lemmas;
`:20–33` 14 lines of formalization prose; `:50–52` his multi-paragraph `<proof>` of
`permute-theorem-dn-generator` paraphrased in one sentence; `:8–16` **renumbers the vertices
$1..n \to 0..n-1$ without saying so**; `permute-example-d4-group` (all eight elements of $D_4$)
dropped. OK-AS-IS(a): `:244–251` the cube note — exactly the prescribed form.

**5.2-exercises** C1: `:229–230` Ex. 37(a) $srs=r^{-1}$ — he **explicitly forwards it from the
main text**, so the guide requires a main-text proof with a pointer here. Instead the main text
makes it an **axiom** (`5.2:89`) and the exercise aliases the concrete version — **neither slot
proves it**, and `:217–226` discloses this as if it were fine.

**6.1** C2: `:6–8` "with a machine-checked `2b4m` proof following each result" — **false on
both counts** (all aliases; Theorem 6.7 dropped). `:116–129` **Theorem 6.7 is stated and then
never addressed** — his full `<proof>` (the $\phi(gH)=Hg^{-1}$ bijection) replaced by an
explanation of our file organization. `:45–49` his two full coset examples compressed to one
referring sentence, the $\mathbb{Z}_6$ one dropped entirely. Both index examples dropped.
OK-AS-IS(a): the no-set-of-elements-sort and no-cardinality cores.

**6.2** C2: `:6–8` same false claim. `:69–72` his proof described, our library's strategy
described, **neither transcribed**. `:142–145` his `<remark>` **and** his
`<proposition cosets-proposition-theorem-10>` (the full $A_4$ conjugation proof,
$(1\,2\,4)(1\,2\,3)(1\,2\,4)^{-1}=(2\,4\,3)$, concluding $H$ has ≥7 elements) compressed to two
sentences — and **misdescribed** as "by exhaustion over $A_4$'s elements" when it is a
conjugation-closure argument. **His `<theorem cosets-theorem-cycle-length-theorem>` (two cycles
have the same length iff conjugate, two-paragraph proof) is absent entirely, no marker.**

**6.3** C2: `:72–78` "**the whole of Judson's proof** — is machine-checked above" — **overclaim**;
what is above is three aliases. `:91–93` **our own argument for $b^p\equiv b$ presented as
transcription** (he states it with no proof there). `:44–47` a real divergence (he proves Euler
in $\mathbb{Z}_n$; we prove a general group fact) stated inline.

**7.1** — **C1 CLEAN and the model**: nine aliases are all $\mathbb{Z}_n$ background; the one
§7.1 result is **proved in full (`:80–175`, 95 lines)**. C2: `:49–52` invokes Judson to justify
that choice and names the library alternative we rejected — the *right* choice wrongly explained
in prose. `:8–10` scoping commentary; the monoalphabetic `<p>` and `crypt-example-help` dropped.

**7.2** C2: `:252–257` **truncates his second RSA case to its first sentence**, dropping the
rest ($r<q$ with $x=rp$, $x^{km}=1+tq$, the final $y^D=x+trn=x \bmod n$) and mischaracterizing
it as merely needing CRT. `:264–269` six lines of to-do notes **self-admittedly not a limit**
("Connecting the two is a short proof that has not been written") — disqualified from (a)/(b)/(c).
`:259–262` cites **`CHAPTER7-PAINPOINTS` by name inside the transcription** — exactly where that
content should have gone. `:217–220` replaces his explicit $D=191$ and verifying computation
with a vague clause.

---

# Chapters 9–11

| file | C1 | C2 defect | C2 ok |
|---|---|---|---|
| 9.1-definition-and-examples.md | **18** | 10 | 3 |
| 9.2-direct-products.md | 11 | 6 | 2 |
| 10.1-factor-groups-and-normal-subgroups.md | 2 | 8 | 2 |
| 10.2-the-simplicity-of-the-alternating-group.md | 10 | **21** | 3 |
| 11.1-group-homomorphisms.md | 16 | 11 | 1 |
| 11.2-the-isomorphism-theorems.md | 18 | 12 | 3 |
| **total** | **75** | **68** | **15** |

**No file in scope is clean. `9.1` and `10.2` contain NO `proof`/`qed` blocks at all** — 199
and 303 lines of prose and aliases. `10.1`, `11.1`, `11.2` have 5, 16 and 18 theorems, **every
one a one-line re-export**. **Not one of Judson's in-text proofs in chapters 9–11 is reproduced
anywhere in `aata/`.** The mathematics lives in `std/group/{isomorphism,product,normal,factor,
homomorphism,first-isomorphism,correspondence}.b4m`, `std/subgroup/product.b4m`,
`std/permutation/{alternating,alternating-identities,simplicity}.b4m`.

**The one-line-re-export shape is documented as intentional** — `10.1:122–124` states the rule
("An uncited `fact` alias is never resolved … so these are re-exported as THEOREMS with
one-line proofs") and CHAPTER11-PAINPOINTS says "Every re-export in aata/11.1 and 11.2 is
written that way." The checker observation is correct, but it solves *verification of the
alias*, not the guide's requirement that the chapter carry Judson's proof structure.

## Class 1 — the headline results

- `10.2:149` **`judsonsLemmaTenTen`** — **Lemma 10.10, his longest in-text proof in the
  chapter** (four XML paragraphs of explicit cycle computation). Fully proved in
  `std/permutation/alternating-identities.b4m` (145 theorems); **the aata chapter carries none
  of it.** The single largest Class-1 defect in the audit.
- `10.2:150` `theAlternatingGroupIsSimple` — **Theorem 10.11**, his three-sentence proof.
- `10.2:81` `everyEvenPermutationIsAProductOfThreeCycles` — **Lemma 10.8**; `:63–71` already
  describes the proof's shape in detail.
- **`10.2` Lemma 10.9 is NOT EVEN ALIASED.** `:85–101` states it and narrates its proof in
  prose; `:194–229` and `:282–298` narrate it again at length. **No `2b4m` block anywhere in
  the file carries it** — despite `:282` asserting "**Lemma 10.9 is now complete**". A result
  claimed complete with no artifact in the chapter.
- `9.1:112` `abelianTransfers` — **Theorem 9.6(3), the one assertion he proves in the running
  text.** `:107–109` says "the proof follows his chain exactly" and **the chain is not in the
  file**. `std/group/isomorphism.b4m:206`; it is five rewrites.
- `9.1:172–184` the five Cayley steps — each a line he writes out in full ("suppose
  $\lambda_g(a)=\lambda_g(b)$. Then $ga=gb$, hence $a=b$"; "Let $b=g^{-1}a$";
  "$\varphi(gh)=\lambda_{gh}=\lambda_g\lambda_h$"). `isomorphism.b4m:273–523`.
- `9.1:67, 68, 76, 104, 131–142` — Theorem 9.6(1), 9.10's three parts, the identity
  preservation whose argument `:71–73` **spells out and then aliases**.
- `11.1:78–213` **all sixteen**: Proposition 11.4's four parts (he proves each: "$e'\varphi(e)
  =\varphi(e)=\varphi(ee)=\varphi(e)\varphi(e)$. By cancellation, $\varphi(e)=e'$";
  "$xy^{-1}=\varphi(a)[\varphi(b)]^{-1}=\varphi(ab^{-1})$";
  "$\varphi(g^{-1}hg)=[\varphi(g)]^{-1}\varphi(h)\varphi(g)\in H_2$") and **Theorem 11.6**, the
  section's named theorem.
- `11.2:103–314` **all eighteen**: the First Isomorphism Theorem's three steps (the
  well-definedness chain he proves at greatest length — the chapter's own `:90–93` says it "is
  three rewrites"), the Second's six, the Correspondence's seven.
- `10.1:72` `conjugationLandsInTheSubgroupIffCosetsCoincide` — **Theorem 10.3**, his
  three-paragraph (1)⇒(2)⇒(3)⇒(1) proof; `:65–69` already narrates both directions.
- `10.1:100` `theFactorOperationIsWellDefined` — **Theorem 10.4's hinge**, his
  $acN=bn_1dn_2N=\ldots=bdN$ chain.
- `9.2:56–96` eleven — Proposition 9.13 (he proves each clause) and Theorem 9.17's structural
  core. `:96` `cubeIsIdentityComponentwise` is **a $k=3$ instance standing in for a general
  theorem**, which CHAPTER9-PAINPOINTS itself calls "the tell that the general version was
  wanted and skipped".
- **Duplicated re-exports**: `10.1:158–176` and `11.2:44–57` are the same two.

## Class 1 — results dropped with no alias and no note

- **`9.1`: Theorem 9.7** (all infinite-order cyclic groups ≅ ℤ, **with a complete in-text
  proof**), **Theorem 9.8**, **Corollary 9.9** — not aliased, not stated, not deferred.
  **NOT BLOCKED**: `std/group/generated.b4m` has `hasInfiniteOrder` (`:1139`) and
  `equalPowersHaveEqualExponents` (`:1266`), which **is** his injectivity argument;
  `generatorIsGenerated`/`inGenerated` give surjectivity. The painpoints file never claims
  these are blocked.
- **`9.2`: Theorem 9.24** (internal direct product) absent, `:120–127` prose only. The claimed
  blocker is the `≅` limit — but **his two proved steps (uniqueness of the $h,k$ decomposition;
  $\varphi(g_1g_2)=\varphi(g_1)\varphi(g_2)$) are not `≅` statements** and are expressible with
  `std/subgroup.b4m` predicates. A feasible proof hidden behind a limit covering only the last line.
- **`9.2`: Theorem 9.17** not proved (only its structural half aliased). Claimed blocker needs
  `power` over `Pair` + lcm minimality; the painpoints text says "Neither connection is made",
  **not that it cannot be** — and `model ProductGroup` makes `std/group/power.b4m` available
  while `std/integer/lattice.b4m` has lcm minimality. **Should be probed, not asserted.**
- **`11.2`: the Correspondence Theorem's last two paragraphs** (normal subgroups of $G$
  containing $N$ ↔ normal subgroups of $G/N$), which he proves — absent, while the summary
  table at `:347–353` **marks Correspondence complete**.
- **`10.2`: Lemma 10.8's four auxiliary identities** discussed at `:290` but never stated or aliased.
- **`11.1`: his ℤ → G example** is **explicitly admitted available** ("`std/group/generated.b4m`
  has `power`") and still skipped under a "not transliterated" heading (`:247–255`).

## Class 2 — 10.2 is the worst file in the corpus

**~150 of its 303 lines are formalization commentary, and ~200 lines come AFTER the last code
block** — the file ends in a long engineering retrospective rather than Judson's text.

- `:257–275` **the worst passage in the audit**: three `rewrite`/`arithmetic(peano)` **tool
  gotchas** transcribed into a book chapter ("note that `rewrite` rewrites a *formula* with an
  equation rather than conjuring the formula, so a spelling change plus an equation is two
  steps, not one"; "because `arithmetic(peano)` treats `succ` opaquely and an index fact with a
  variable under it comes back 'the statement is false'").
- `:282–298` **generated-line counts and a `drafts/` path**: "**844 generated lines, and the
  generator is kept in `drafts/selector-generator/` so it is regenerable.**"
- `:218–229` **a breadth-first search over our own lemma space** ("BFS over all twenty 3-cycles
  on five points under that move gives diameter 3") — no counterpart anywhere in Judson.
- `:117–121` **checker output quoted in the book prose**: "`2b4m check --axioms` … reports
  **41 axioms and zero holes**".
- `:167–192` **a retrospective on the author's own earlier wrong claims** ("Both reasons
  originally recorded here for why it could not start have since been retired … both were wrong
  in the same way"). Internally inconsistent too: "41 theorems" where the file has 145.
- `:277–280` a cross-reference to the engineering log inside the chapter.
- `:158–165` a section heading plus a naming-disclaimer about our own identifiers.
- `:194–216` proof-engineering narration naming six library identifiers — **and contradicting
  `:282`**: "Lemma 10.9's conjugation step is now *half* proved" vs "Lemma 10.9 is now complete".
- `:141, 152` code comments; `:300–303` his Historical Note (Jordan, Dickson, Burnside's
  conjecture, Gorenstein's program, the Monster, the 26 sporadic groups) **compressed to three
  sentences**.
- **OK-AS-IS**: `:131–135` "**This is Judson's own assertion** … he lists them without
  argument — it is the one step of his proof that is a claim rather than a computation, so it
  is where the formalization stops." Verified against `normal-lemma-3-normal-3cycle`: **he does
  list the five shapes with no exhaustiveness argument.** The one legitimate Judson-attribution
  in the file. Also `:14–17` (no sort of subgroups) and `:125–127`.

## Class 2 — the rest

**11.2** `:317–324` **the clearest single instance in the file**: an author's-process
retrospective with a `drafts/` path ("When this chapter was first surveyed I recorded that …
Probing settled it … **The error was reasoning about what `std` *has* rather than what the
language can *express***. See `drafts/chapter11-probes/README`") — the identical paragraph
already appears in CHAPTER11-PAINPOINTS. `:147–150` and `:152–155` **verbatim painpoints
material** (`assoc` cannot insert a cancelling pair; the normality-orientation mismatch) — and
`:150`'s "The cancellation is written out in each case" is **false**: the theorems are aliases.
`:345–356` a **formalization-status dashboard** ("proved" / "not nameable" / "not
transliterated") as the chapter's conclusion, where he ends with
`homomorph-example-third-isomorphism`. `:22–27` cross-chapter progress tracking.
OK-AS-IS(a): `:60–70` the `≅` limit — real, and stating it once is the right economy — but the
heading "stated once", "the mathematical content complete", and "one limit appearing four
times, not four limits" are all (i), and it is a full prose section, not an aside.

**11.1** `:72–75` "Parts (1) and (2) **transliterate directly**" — a claim the file does not
honour (they are aliases). `:247–255` an entire section whose subject is our to-do list.
`:218–223` verbatim from CHAPTER11-PAINPOINTS' `--library` gate discussion. `:16–19` his
quotation is correct but framed as reportage; his even/odd table and all four kernel examples
dropped. OK-AS-IS(a): `:27–32` the two-groups and φ-is-primitive limits (both verified real —
`std/function.b4m:34` is single-sorted) — but duplicated at `9.1:19–24` and `9.1:48–52`.

**9.1** `:195–199` the worst form: **it invents a Judson-style "left to the reader"** ("Closure
under inverses … is left to the reader, **as Judson leaves the remaining assertions of Theorem
9.6**") **to cover a gap he himself fills** — his Cayley `<proof>` ¶2 computes
$(\lambda_{g^{-1}}\circ\lambda_g)(a)=a$ explicitly. `:54–59` **one sentence replaces five full
`<example>` blocks** (ℤ_4≅⟨i⟩, (ℝ,+)≅(ℝ⁺,·), ℤ_8/ℤ_12 + U(8)≅U(12), and the **S_3-vs-ℤ_6
non-isomorphism worked contradiction**). `:162–167` "All of this is machine-checked" +
library-design commentary, displacing his Cayley lead-in ("Cayley's Theorem is what we call a
representation theorem…"). `:115–119` "reachable, not built" — self-assessment already in
CHAPTER9-PAINPOINTS verbatim. Omitted: "We are now in a position to characterize all cyclic
groups", "it makes sense to consider two groups to be the same if they are isomorphic", the
closing "classifying all groups *up to isomorphism*", `isomorph-example-cayley`, the left
regular representation paragraph, the Cayley Historical Note.

**10.1** `:103–111` **a changelog of the formalization's own history** ("This note previously
read '…'. There is now: `std/group/factor.b4m` builds G/N as a genuine sort…").
`:122–124` **a checker-mechanics note that explicitly announces the Class-1 pattern as a design
choice**. `:18–21` the predicate limit is OK-AS-IS(a) but "**which is exactly how Judson uses
it**" is refinement-1's exact target. `:65–69` **silently merges two of his three numbered
statements** — a substantive change presented as his. `:119–120` calls Lagrange "still not
transliterated" while saying it is proved in §6.2 — a connection not made, not a limit.
Omitted: "the elements in a factor group are *sets of elements* in the original group" (a
load-bearing remark), `normal-example-factor-s3` ("The information captured in G/N is parity"),
`-factor-z3`, `-factor_dn`, the chapter introduction.

**9.2** `:82–84` a reframing that **replaces his actual proof** (the two-inequality squeeze
"$n$ must divide $m$ … both $r$ and $s$ must divide $n$ … Consequently $m=n$") — his squeeze is
nowhere in the file. `:104–107` labelled a "*Proof sketch*" when **his proof is complete and
short**, and the converse half is dropped. `:90–93` "has not been connected" is an admission,
not a limit — **not (b)**: it is unbuilt machinery. `:116–118` compresses two separate examples
into one line, losing the *reason* (every non-identity element of ℤ_2×ℤ_2 has order 2).
Omitted: `isomorph-example-r2-product`, `isomorph-example-z2n` (ℤ_2^n as binary tuples/XOR with
its coding-theory remark), the n-fold product paragraph, two corollaries, the forward reference
to the classification of finite abelian groups.

## Verified-real limits in this scope (do not re-litigate)

`≅` cannot be named (no sort of groups); `std/function.b4m` is single-sorted
(`apply(f: Fn, x: Element) => Element`, `:34`); `std/integer/mod-n.b4m`'s modulus is a single
`const N` (`:49`); no sort of subgroups/predicates to quantify over; **Judson genuinely asserts
Lemma 10.10's five-case list without proving exhaustiveness.**

## Claimed limits that do NOT hold up

(a) `9.1`'s Theorems 9.7/9.8/9.9 — dropped with no limit claimed, and the machinery exists;
(b) `9.2`'s Theorem 9.24 — its proved parts are not `≅` statements;
(c) `11.2`'s "what remains is its `≅` step" for the Second Iso Thm also hides his onto and
homomorphism proofs, which are not `≅` statements;
(d) `11.1`'s ℤ → G example — explicitly admitted available and still skipped;
(e) `11.2:332–343`'s Third Iso blocker is a **tooling** limitation (the model system), which is
neither (a) a language limit nor (b) arithmetic — and "a thing to fix rather than a thing to
state" is roadmap language.

## ZERO asides in chapters 9–11

The blockquote convention **is** established elsewhere — `aata/4.1-cyclic-subgroups.md:382–391`
is a near-model (c) note (names what Judson elides, what we do instead, and why, inside a `>`
block). **No file in chapters 9–11 uses it.** So **no finding in this scope qualifies for
exception (c)**; the four genuine divergences are all defects on form:
`10.2:63–66` (proved-vs-asserted trichotomy), `10.2:205–216` (uniform conjugator),
`10.2:230–235` (point values instead of cycle type — the most substantive, and it almost says
"Judson does X, we do Y", but is framed as a correction of the author's own earlier misreading
and buried 230 lines in), `11.2:90–93` (quotient sort instead of coset predicates).

---

# Cross-corpus synthesis

## Totals

| | C1 | C2 defect | C2 OK-AS-IS |
|---|---|---|---|
| ch 1–2 | 6 | ~96 | ~20 |
| ch 3–4 | 36 | ~57 | ~9 |
| ch 5–7 | 29 | 73 | 13 |
| ch 9–11 | 75 | 68 | 15 |
| **total** | **146** | **~294** | **~57** |

## The files that already meet the standard — copy these

- **`aata/4.1-cyclic-subgroups.md`** — Class 1 CLEAN. Every §4.1 result is a real transcribed
  proof; no `fact` aliases at all. Also holds the corpus's **only near-conforming (c) aside**
  (`:382–391`).
- **`aata/7.1-private-key-cryptography.md`** — Class 1 CLEAN, with a hand-written 95-line kernel
  proof. Proof that Chapter 6's wholesale aliasing was a choice, not a capability limit.
- **`aata/2.2-division-algorithm.md`** — Class 1 exemplary: proves the Division Algorithm and its
  uniqueness in full, independently.
- **`aata/1.2.2-functions.md:52–157`** and **`1.2.1-sets.md:40–160`** — the Class 2 target
  standard: Judson's prose verbatim and in order, figures marked using the XML's own
  `<description>`.

## Class 1 priority order

1. **`10.2` Lemma 10.10 + Theorem 10.11 + Lemma 10.9** — the chapter's entire content; 10.9 has
   **no artifact at all** while the prose claims it complete.
2. **`6.2` Lagrange's Theorem** — the title theorem, two-line Judson proof, 73-line std proof,
   quoted-then-aliased.
3. **`11.1` + `11.2`** — 34 one-line re-exports covering Proposition 11.4, Theorem 11.6 and all
   three Isomorphism Theorems.
4. **`9.1`** — 18 aliases + **three silently dropped theorems that are not blocked** (9.7/9.8/9.9).
5. **`3.2` Basic Properties + `3.3` all seven + `4.2` all eleven** (incl. **De Moivre**).
6. **`6.1`, `6.3`, `7.2`** — Theorem 6.4, Euler, RSA correctness; all quoted-then-aliased.
7. **`5.1`** — $|S_n|=n!$, disjoint-cycle and transposition decompositions, and his four-case Lemma.
8. **`2.1`/`2.3`** — the six chapter-2 aliases; `2.3:36–37` is pure redundancy (cite §2.2).

**Special case — a theorem converted into axioms**: `3.3-subgroups.md:39–43, 69–72` take
Judson's three-condition subgroup criterion (which he **proves**, `groups.xml` 1130–1152) as the
*axioms* of `std/subgroup.b4m`. Recommended split: prove the **converse** (expressible today);
mark the **forward** direction as a language limit naming what it needs ("H is a group in its
own right" ⇒ a sort of groups). Same shape at `5.2:88–89`, where his geometrically-derived
dihedral relations are `axiom`s.

## Class 2 priority order

1. **Delete the engineering retrospectives.** `10.2:158–298` (~140 lines), `11.2:317–324`,
   `10.1:103–124`, `9.1:115–119`, `2.3:250–257`+`:1337–1341`. All of it is painpoints-file
   content, much of it **already duplicated there verbatim**. Includes tool gotchas, BFS search
   results, checker output, generated-line counts, `drafts/` paths, and author's-process
   narratives.
2. **Fix the five FALSE statements** (all independently verified) — these mislead regardless of
   prose policy:
   - `1.2.2-functions.md:600` calls the backward direction unencodable; **`:858` proves it**.
   - `1.2.1-sets-exercises.md:104–106` defers for a missing `subset`; **`std/set.b4m:58` defines it**.
   - `1.2.2-functions-exercises.md:30–35` says `composeAssoc` is unpackaged; **`:108` has it**.
   - `1.2.3-relations.md:27–36` says classes/partitions are out of reach; **`1.2.3-partitions.md`
     does them**.
   - `4.2-…-group.md:6–12` says polar/DeMoivre/roots-of-unity are prose-only; **the file
     formalizes all three**, and `:116–122` contradicts it. Its exercises file disagrees too.
   - Related: **`5.1:322–343` vs `:465–474`** — two contradictory accounts of the same lemma
     (axiomatized-and-unreachable vs proved-and-"illusory") **in one file**.
3. **Restore Judson's exposition.** The dominant failure is structural: in `2.1`, `2.3`,
   `1.2.3-relations`, `1.2.3-partitions`, `9.1`, `10.2` the inter-code prose is a narration of
   our proof architecture **with his text absent entirely**. ~40 `<example>` blocks are dropped
   with no marker, several carrying load-bearing content — most consequentially
   **`5.1`'s right-to-left composition convention remark**, which the whole chapter's `compose`
   usage silently assumes, and **`1.2.3`'s `sets-example-congruent-integers`**, which needs no
   proof at all and which `aata/3.1` already formalizes.
4. **Strip import-horizon justifications** — every "which Judson has in hand by this point",
   "By Chapter 4 the reals are in hand", "Judson would already have". Densest at
   `4.1:11–17`, `2.2:8–17`, `5.1:10–15`, `3.1:18–20`, `3.3-exercises:2549–2552`.
5. **Convert the 11 genuine divergences to conforming (c) asides.** Each must read "Judson does
   X, we are doing Y" **and** sit in a blockquote. None currently conforms; the closest are
   `2.1:74–75` (right wording, inline — just needs wrapping) and `4.1:382–391` (right form, but
   its claim to be "the only step elided in the book" is contradicted by two unmarked
   axiomatizations in the same file). Full list: `2.1:74–75`, `1.2.1-sets:164`,
   `1.2.3-relations-exercises:27–31`, `1.2.3-partitions:102–105`, `2.3:1419–1425`,
   `2.3:1593–1599`, `2.3-exercises:68–72`, `3.1:485–490`, `3.1:105–111`, `3.3-exercises:48–56`,
   `3.3-exercises:2100–2108`, `4.1-exercises:593–599`, `4.1-exercises:918–926`,
   `5.2:54–58`, `5.1-exercises:235–237`, `6.3:44–47`, `7.2:230–234`, `10.2:63–66`,
   `10.2:205–216`, `10.2:230–235`, `11.2:90–93`.
6. **Unmarked axiomatizations presented as closed gaps** — worth a decision each:
   `4.1:494–497` (he *derives* $m$ from well-ordering; here it is an axiom, and `wellordering`
   is imported at `:24` but **never used**, making the gap look closed); `4.1:950`
   (`axiom cofactorBezout`, with prose claiming "because $d=\gcd(k,n)$" when **there is no
   `gcd` in the file**); `1.2.3-partitions.md:484` (`axiom quotientContains` — a **new axiom
   invented in a transliteration**, self-justified as "This is honest"; per the repo's own rule
   it should be a `hole`).

## Mechanical artifacts (quick wins, unrelated to either class)

- **Eight `less_than` text corruptions** from a bad global replace: `2.2:17, 105`;
  `2.3:410, 412, 428, 2030, 2668, 3747`. `2.2:17` ("transcribed as real proofs **less_than**.")
  and `2.3:428` leave ungrammatical sentences.
- **Two shipped authoring TODOs**: `1.2.3-partitions.md:103, 276` — "**(Proof to fill: …)**".
- **Duplicated opening paragraph**: `2.1:8–20`.
- **Every exercise number wrong in both ch-1 exercise files** (verified against the XML):
  `1.2.1-sets-exercises` "8"→13, "6"→10, "10"→14, "11"→15, "12"→16;
  `1.2.2-functions-exercises:103` "25"→19.
- **Invented, colliding result numbers in `2.3-primes.md`** (the XML carries none):
  "Theorem 2.10"(`:529`)/"Definition 2.10"(`:1120`); "Corollary 2.11"(`:958`)/"Lemma 2.11"(`:1815`).
- **Import-path mismatches** — prose describes a dependency the code lacks: `3.2:21` imports
  `std/group.b4m` while the prose says `std/group/power.b4m`; `4.2:23` imports
  `std/complex.b4m` where the prose says `std/complex/modulus.b4m`; `3.1:24`
  `import int_divides <<< "std/integer.b4m"`.
- **Identifiers embedding "judsons"** (`10.2:142–149`: `judsonsLemmaTenTen`,
  `judsonsLongCycleShape`, …) — the Class-2 problem leaking into code and into `std`.
- **Forwarding pointers that resolve to nothing proved**: `3.3-exercises:533–535`,
  `2.1-exercises:637–650` forward to main-text sections whose own proofs are aliases.
- **`1.2.2-functions-exercises.md:37–99`** re-proves `composeAssoc` verbatim from the main text;
  the guide says a main-text-proved result gets a prose pointer, not a re-proof.

## Future work (user-flagged 2026-10-18)

**Teach `2b4m query search` to match modulo variable and sort names.** That subcommand already
does exactly the lookup this catalog wants — give it a statement, get back
`file:line:theorem_name` across a directory, which *is* the aside format. What it cannot do is
alpha-invariance: `query search std "forall g: G; phi(invG(g)) = invH(phi(g))"` finds the
theorem, but renaming the binder to `z` returns "no theorem or axiom matching". So it cannot
answer "is this statement already in std under different variable names". Alpha-normalizing both
the query and the indexed statements before comparing would make the catalog below a one-liner
over the corpus and retire the script. `drafts/aata-audit/dup.py`'s `normalize()` is a working
reference for the needed normalization.

## Two structural observations

- **The `fact`-alias-vs-one-line-theorem distinction is a red herring for this audit.**
  `10.1:122–124` documents the switch to one-line theorems because *an uncited `fact` alias is
  never resolved* — a real checker fact (see memory `uncited-fact-alias-proves-nothing`). But it
  only makes the alias *verified*; it does nothing for the requirement that the chapter carry
  Judson's proof. Both shapes are Class 1.
- **`--library` pressure may be part of the cause.** Several passages explain a formalization
  choice by reference to keeping an axiom load-bearing for the `std --library` gate
  (`10.1:113–117`, `11.1:218–223`). Worth checking whether the gate is pushing proofs out of
  `aata/` and into `std/`.
---

# Catalog: aata theorems that already exist in `std`

**84 of aata's 331 theorems have an exact `std` twin**, matched on the theorem's STATEMENT
modulo variable names, sort names and theorem names. Duplication in `std` is encouraged — this
catalog is a cross-reference, not a delete-list. For each entry, add an aside to the aata
documentation:

> NB: This theorem exists in std in `file:line:theorem_name`

Entries with two `std` rows have the statement in two places (e.g. the homomorphism and
isomorphism theories both carry `phiPreservesIdentity`); cite whichever the chapter is layered on.

**How this was produced** (reproducible): parse every `theorem`/`schema` declaration's statement
from source (`std/**/*.b4m` and the ```2b4m fences of `aata/*.md`), alpha-normalize binder
variables and sorts positionally, and index. Spot-checked against `2b4m query search`, which
agreed on every case tried. Script kept at `drafts/aata-audit/dup.py` if wanted.


## aata/1.2.1-sets-exercises.md — 5

- **`unionMinusRight`** (`aata/1.2.1-sets-exercises.md:42`)
  `forall a, b: Set; difference(union(a, b), b) = difference(a, b)`
  > NB: This theorem exists in std in `std/set.b4m:1261:unionMinusRight`

- **`unionAsThreePieces`** (`aata/1.2.1-sets-exercises.md:54`)
  `forall a, b: Set; union(a, b) = union(union(intersection(a, b), difference(a, b)), difference(b, a))`
  > NB: This theorem exists in std in `std/set.b4m:1268:unionAsThreePieces`

- **`differenceOverUnion`** (`aata/1.2.1-sets-exercises.md:67`)
  `forall a, b, c: Set; difference(a, union(b, c)) = intersection(difference(a, b), difference(a, c))`
  > NB: This theorem exists in std in `std/set.b4m:1277:differenceOverUnion`

- **`intersectionOverDifference`** (`aata/1.2.1-sets-exercises.md:80`)
  `forall a, b, c: Set; intersection(a, difference(b, c)) = difference(intersection(a, b), intersection(a, c))`
  > NB: This theorem exists in std in `std/set.b4m:1286:intersectionOverDifference`

- **`symmetricDifference`** (`aata/1.2.1-sets-exercises.md:94`)
  `forall a, b: Set; union(difference(a, b), difference(b, a)) = difference(union(a, b), intersection(a, b))`
  > NB: This theorem exists in std in `std/set.b4m:1295:symmetricDifference`


## aata/1.2.1-sets.md — 14

- **`unionIdempotent`** (`aata/1.2.1-sets.md:192`)
  `forall a: Set; union(a, a) = a`
  > NB: This theorem exists in std in `std/set.b4m:73:unionIdempotent`

- **`intersectionIdempotent`** (`aata/1.2.1-sets.md:257`)
  `forall a: Set; intersection(a, a) = a`
  > NB: This theorem exists in std in `std/set.b4m:132:intersectionIdempotent`

- **`differenceSelf`** (`aata/1.2.1-sets.md:322`)
  `forall a: Set; difference(a, a) = emptyset`
  > NB: This theorem exists in std in `std/set.b4m:191:differenceSelf`

- **`unionEmpty`** (`aata/1.2.1-sets.md:401`)
  `forall a: Set; union(a, emptyset) = a`
  > NB: This theorem exists in std in `std/set.b4m:256:unionEmpty`

- **`intersectionEmpty`** (`aata/1.2.1-sets.md:475`)
  `forall a: Set; intersection(a, emptyset) = emptyset`
  > NB: This theorem exists in std in `std/set.b4m:321:intersectionEmpty`

- **`unionAssociative`** (`aata/1.2.1-sets.md:553`)
  `forall a, b, c: Set; union(a, union(b, c)) = union(union(a, b), c)`
  > NB: This theorem exists in std in `std/set.b4m:386:unionAssociative`

- **`intersectionAssociative`** (`aata/1.2.1-sets.md:660`)
  `forall a, b, c: Set; intersection(a, intersection(b, c)) = intersection(intersection(a, b), c)`
  > NB: This theorem exists in std in `std/set.b4m:487:intersectionAssociative`

- **`unionCommutative`** (`aata/1.2.1-sets.md:769`)
  `forall a, b: Set; union(a, b) = union(b, a)`
  > NB: This theorem exists in std in `std/set.b4m:588:unionCommutative`

- **`intersectionCommutative`** (`aata/1.2.1-sets.md:850`)
  `forall a, b: Set; intersection(a, b) = intersection(b, a)`
  > NB: This theorem exists in std in `std/set.b4m:663:intersectionCommutative`

- **`unionDistributesOverIntersection`** (`aata/1.2.1-sets.md:934`)
  `forall a, b, c: Set; union(a, intersection(b, c)) = intersection(union(a, b), union(a, c))`
  > NB: This theorem exists in std in `std/set.b4m:738:unionDistributesOverIntersection`

- **`intersectionDistributesOverUnion`** (`aata/1.2.1-sets.md:1055`)
  `forall a, b, c: Set; intersection(a, union(b, c)) = union(intersection(a, b), intersection(a, c))`
  > NB: This theorem exists in std in `std/set.b4m:849:intersectionDistributesOverUnion`

- **`deMorganUnion`** (`aata/1.2.1-sets.md:1190`)
  `forall a, b: Set; complement(union(a, b)) = intersection(complement(a), complement(b))`
  > NB: This theorem exists in std in `std/set.b4m:960:deMorganUnion`

- **`deMorganIntersection`** (`aata/1.2.1-sets.md:1309`)
  `forall a, b: Set; complement(intersection(a, b)) = union(complement(a), complement(b))`
  > NB: This theorem exists in std in `std/set.b4m:1065:deMorganIntersection`

- **`disjointDifferences`** (`aata/1.2.1-sets.md:1442`)
  `forall a, b: Set; intersection(difference(a, b), difference(b, a)) = emptyset`
  > NB: This theorem exists in std in `std/set.b4m:1170:disjointDifferences`


## aata/1.2.2-functions-exercises.md — 1

- **`composeAssoc`** (`aata/1.2.2-functions-exercises.md:39`)
  `forall h, g, f: Fn; compose(compose(h, g), f) = compose(h, compose(g, f))`
  > NB: This theorem exists in std in `std/function/invertible.b4m:36:composeAssoc`


## aata/1.2.2-functions.md — 1

- **`composeAssoc`** (`aata/1.2.2-functions.md:174`)
  `forall h, g, f: Fn; compose(compose(h, g), f) = compose(h, compose(g, f))`
  > NB: This theorem exists in std in `std/function/invertible.b4m:36:composeAssoc`


## aata/11.1-group-homomorphisms.md — 15

- **`phiPreservesIdentity`** (`aata/11.1-group-homomorphisms.md:78`)
  `phi(EG) = EH`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:128:phiPreservesIdentity`
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:130:phiPreservesIdentity`

- **`phiPreservesInverses`** (`aata/11.1-group-homomorphisms.md:85`)
  `forall g: G; phi(invG(g)) = invH(phi(g))`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:154:phiPreservesInverses`

- **`theImageHasTheIdentity`** (`aata/11.1-group-homomorphisms.md:105`)
  `inImage(EH)`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:416:theImageHasTheIdentity`

- **`theImageIsClosedUnderTheOperation`** (`aata/11.1-group-homomorphisms.md:112`)
  `forall x: H; forall y: H; inImage(x) -> inImage(y) -> inImage(opH(x, y))`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:436:theImageIsClosedUnderTheOperation`

- **`theImageIsClosedUnderInverses`** (`aata/11.1-group-homomorphisms.md:120`)
  `forall x: H; inImage(x) -> inImage(invH(x))`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:520:theImageIsClosedUnderInverses`

- **`thePreimageHasTheIdentity`** (`aata/11.1-group-homomorphisms.md:128`)
  `inPreimage(EG)`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:591:thePreimageHasTheIdentity`

- **`thePreimageIsClosedUnderTheOperation`** (`aata/11.1-group-homomorphisms.md:135`)
  `forall a: G; forall b: G; inPreimage(a) -> inPreimage(b) -> inPreimage(opG(a, b))`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:604:thePreimageIsClosedUnderTheOperation`

- **`thePreimageIsClosedUnderInverses`** (`aata/11.1-group-homomorphisms.md:143`)
  `forall a: G; inPreimage(a) -> inPreimage(invG(a))`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:648:thePreimageIsClosedUnderInverses`

- **`thePreimageOfANormalSubgroupIsNormal`** (`aata/11.1-group-homomorphisms.md:151`)
  `(forall x: H; forall y: H; inTarget(y) -> inTarget(opH(opH(x, y), invH(x)))) -> forall g: G; forall n: G; inPreimage(n) -> inPreimage(opG(opG(g, n), i`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:681:thePreimageOfANormalSubgroupIsNormal`

- **`theKernelHasTheIdentity`** (`aata/11.1-group-homomorphisms.md:183`)
  `inKernel(EG)`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:197:theKernelHasTheIdentity`

- **`theKernelIsClosedUnderTheOperation`** (`aata/11.1-group-homomorphisms.md:190`)
  `forall a: G; forall b: G; inKernel(a) -> inKernel(b) -> inKernel(opG(a, b))`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:284:theKernelIsClosedUnderTheOperation`

- **`theKernelIsClosedUnderInverses`** (`aata/11.1-group-homomorphisms.md:198`)
  `forall a: G; inKernel(a) -> inKernel(invG(a))`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:353:theKernelIsClosedUnderInverses`

- **`theKernelIsNormal`** (`aata/11.1-group-homomorphisms.md:207`)
  `forall g: G; forall n: G; inKernel(n) -> inKernel(opG(opG(g, n), invG(g)))`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:211:theKernelIsNormal`

- **`aTrivialKernelMakesPhiInjective`** (`aata/11.1-group-homomorphisms.md:226`)
  `(forall g: G; inKernel(g) -> g = EG) -> forall a: G; forall b: G; phi(a) = phi(b) -> a = b`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:771:aTrivialKernelMakesPhiInjective`

- **`anInjectivePhiHasATrivialKernel`** (`aata/11.1-group-homomorphisms.md:236`)
  `(forall a: G; forall b: G; phi(a) = phi(b) -> a = b) -> forall g: G; inKernel(g) -> g = EG`
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:868:anInjectivePhiHasATrivialKernel`


## aata/11.2-the-isomorphism-theorems.md — 12

- **`theCanonicalMapIsAHomomorphism`** (`aata/11.2-the-isomorphism-theorems.md:44`)
  `forall a: G; forall b: G; cls(opG(a, b)) = opQ(cls(a), cls(b))`
  > NB: This theorem exists in std in `std/group/factor.b4m:341:clsPreservesOp`

- **`theCanonicalMapsKernelIsN`** (`aata/11.2-the-isomorphism-theorems.md:52`)
  `forall g: G; cls(g) = EQ iff inN(g)`
  > NB: This theorem exists in std in `std/group/factor.b4m:365:clsKernelIsN`

- **`etaIsWellDefined`** (`aata/11.2-the-isomorphism-theorems.md:103`)
  `forall a: G; forall b: G; cls(a) = cls(b) -> psi(a) = psi(b)`
  > NB: This theorem exists in std in `std/group/first-isomorphism.b4m:152:etaIsWellDefined`

- **`etaPreservesOp`** (`aata/11.2-the-isomorphism-theorems.md:111`)
  `forall x: Quot; forall y: Quot; eta(opQ(x, y)) = opHH(eta(x), eta(y))`
  > NB: This theorem exists in std in `std/group/first-isomorphism.b4m:194:etaPreservesOp`

- **`etaIsInjective`** (`aata/11.2-the-isomorphism-theorems.md:119`)
  `forall x: Quot; forall y: Quot; eta(x) = eta(y) -> x = y`
  > NB: This theorem exists in std in `std/group/first-isomorphism.b4m:255:etaIsInjective`

- **`hSitsInsideTheProduct`** (`aata/11.2-the-isomorphism-theorems.md:206`)
  `forall h: G2; inH(h) -> inProduct(h)`
  > NB: This theorem exists in std in `std/subgroup/product.b4m:544:hSitsInsideTheProduct`

- **`hOverNHasTheIdentity`** (`aata/11.2-the-isomorphism-theorems.md:256`)
  `inHoverN(EQ)`
  > NB: This theorem exists in std in `std/group/correspondence.b4m:122:hOverNHasTheIdentity`

- **`hOverNIsClosedUnderTheOperation`** (`aata/11.2-the-isomorphism-theorems.md:263`)
  `forall x: Quot; forall y: Quot; inHoverN(x) -> inHoverN(y) -> inHoverN(opQ(x, y))`
  > NB: This theorem exists in std in `std/group/correspondence.b4m:138:hOverNIsClosedUnderTheOperation`

- **`hOverNIsClosedUnderInverses`** (`aata/11.2-the-isomorphism-theorems.md:271`)
  `forall x: Quot; inHoverN(x) -> inHoverN(invQ(x))`
  > NB: This theorem exists in std in `std/group/correspondence.b4m:579:hOverNIsClosedUnderInverses`

- **`thePullbackIsClosedUnderTheOperation`** (`aata/11.2-the-isomorphism-theorems.md:280`)
  `forall a: G; forall b: G; inPullback(a) -> inPullback(b) -> inPullback(opG(a, b))`
  > NB: This theorem exists in std in `std/group/correspondence.b4m:306:thePullbackIsClosedUnderTheOperation`

- **`thePullbackContainsN`** (`aata/11.2-the-isomorphism-theorems.md:288`)
  `forall g: G; inN(g) -> inPullback(g)`
  > NB: This theorem exists in std in `std/group/correspondence.b4m:386:thePullbackContainsN`

- **`thePullbacksImageIsS`** (`aata/11.2-the-isomorphism-theorems.md:296`)
  `forall q: Quot; inPullbackOverN(q) iff inS(q)`
  > NB: This theorem exists in std in `std/group/correspondence.b4m:425:thePullbacksImageIsS`


## aata/2.2-division-algorithm.md — 4

- **`remaindersEqual`** (`aata/2.2-division-algorithm.md:141`)
  `forall b, q1, r1, q2, r2: Int; less_than(ZERO, b) -> is_nonneg(r1) -> less_than(r1, b) -> is_nonneg(r2) -> less_than(r2, b) -> add(mul(b, q1), r1) = a`
  > NB: This theorem exists in std in `std/integer/divides.b4m:1462:remaindersEqual`

- **`divisionAlgorithmUnique`** (`aata/2.2-division-algorithm.md:289`)
  `forall a, b, q1, r1, q2, r2: Int; less_than(ZERO, b) -> a = add(mul(b, q1), r1) -> is_nonneg(r1) -> less_than(r1, b) -> a = add(mul(b, q2), r2) -> is_`
  > NB: This theorem exists in std in `std/integer/divides.b4m:1634:divisionAlgorithmUnique`

- **`remainderSetHasLeast`** (`aata/2.2-division-algorithm.md:470`)
  `forall a, b: Int; (exists n: Int; is_nonneg(n) and (exists k: Int; n = sub(a, mul(b, k)))) -> exists least: Int; is_nonneg(least) and (exists k: Int; `
  > NB: This theorem exists in std in `std/integer/divides.b4m:1976:remainderSetHasLeast`

- **`divisionAlgorithmExists`** (`aata/2.2-division-algorithm.md:645`)
  `forall a, b: Int; less_than(ZERO, b) -> exists q: Int; exists r: Int; a = add(mul(b, q), r) and is_nonneg(r) and less_than(r, b)`
  > NB: This theorem exists in std in `std/integer/divides.b4m:2348:divisionAlgorithmExists`


## aata/2.3-primes.md — 12

- **`dividesElim`** (`aata/2.3-primes.md:99`)
  `forall d, m: Int; does_divide(d, m) -> exists k: Int; m = mul(d, k)`
  > NB: This theorem exists in std in `std/primes.b4m:124:dividesElim`

- **`addLeftSwap`** (`aata/2.3-primes.md:260`)
  `forall a, b, c: Int; add(a, add(b, c)) = add(b, add(a, c))`
  > NB: This theorem exists in std in `std/complex.b4m:230:addLeftSwap`
  > NB: This theorem exists in std in `std/field.b4m:163:addLeftSwap`
  > NB: This theorem exists in std in `std/field/order.b4m:292:addLeftSwap`
  > NB: This theorem exists in std in `std/integer.b4m:2256:addLeftSwap`
  > NB: This theorem exists in std in `std/peano.b4m:989:addLeftSwap`
  > NB: This theorem exists in std in `std/rational.b4m:307:addLeftSwap`
  > NB: This theorem exists in std in `std/real.b4m:342:addLeftSwap`

- **`remainderIsMember`** (`aata/2.3-primes.md:314`)
  `forall a, b, d, r, s, q, remainder: Int; a = add(mul(d, q), remainder) -> d = add(mul(a, r), mul(b, s)) -> remainder = add(mul(a, sub(ONE, mul(r, q)))`
  > NB: This theorem exists in std in `std/integer/divides.b4m:4525:remainderIsMember`

- **`combinationSetNonempty`** (`aata/2.3-primes.md:431`)
  `a != ZERO -> exists n: Int; is_nonneg(n) and (less_than(ZERO, n) and (exists mm: Int; exists nn: Int; n = add(mul(a, mm), mul(b, nn))))`
  > NB: This theorem exists in std in `std/integer/divides.b4m:4619:combinationSetNonempty`

- **`mulOneLeft`** (`aata/2.3-primes.md:1278`)
  `forall n: Int; mul(ONE, n) = n`
  > NB: This theorem exists in std in `std/field/units.b4m:237:unitsIdentityLeft`
  > NB: This theorem exists in std in `std/integer.b4m:2297:mulOneLeft`
  > NB: This theorem exists in std in `std/integer/mod-n.b4m:1163:mulOneLeft`
  > NB: This theorem exists in std in `std/integer/mod-n.b4m:1238:unitsIdentityLeft`
  > NB: This theorem exists in std in `std/peano.b4m:711:mulOneLeft`
  > NB: This theorem exists in std in `std/rational/units.b4m:138:unitsIdentityLeft`
  > NB: This theorem exists in std in `std/real/units.b4m:138:unitsIdentityLeft`

- **`mulLeftSwap`** (`aata/2.3-primes.md:1302`)
  `forall a, b, c: Int; mul(a, mul(b, c)) = mul(b, mul(a, c))`
  > NB: This theorem exists in std in `std/complex.b4m:223:mulLeftSwap`
  > NB: This theorem exists in std in `std/field.b4m:122:mulLeftSwap`
  > NB: This theorem exists in std in `std/field/order.b4m:285:mulLeftSwap`
  > NB: This theorem exists in std in `std/integer.b4m:2215:mulLeftSwap`
  > NB: This theorem exists in std in `std/peano.b4m:1025:mulLeftSwap`
  > NB: This theorem exists in std in `std/rational.b4m:300:mulLeftSwap`
  > NB: This theorem exists in std in `std/real.b4m:335:mulLeftSwap`

- **`negDivides`** (`aata/2.3-primes.md:1356`)
  `forall e, n: Int; does_divide(e, n) -> does_divide(neg(e), n)`
  > NB: This theorem exists in std in `std/primes.b4m:151:negDivides`

- **`dividesDecidable`** (`aata/2.3-primes.md:1428`)
  `forall p, a: Int; less_than(ZERO, p) -> (does_divide(p, a) or (not does_divide(p, a)))`
  > NB: This theorem exists in std in `std/primes.b4m:205:dividesDecidable`

- **`lessThanSuccSelf`** (`aata/2.3-primes.md:2036`)
  `forall k: Int; less_than(k, succ(k))`
  > NB: This theorem exists in std in `std/integer/wellordering.b4m:284:lessThanSelf`
  > NB: This theorem exists in std in `std/peano/order.b4m:876:lessThanSelf`

- **`lessThanMulGreaterThanOne`** (`aata/2.3-primes.md:2742`)
  `forall p, c: Int; less_than(ONE, p) -> less_than(ZERO, c) -> less_than(c, mul(p, c))`
  > NB: This theorem exists in std in `std/primes/classes.b4m:634:factorBelowProduct`

- **`succMonotone`** (`aata/2.3-primes.md:3753`)
  `forall a, b: Int; less_than(a, b) -> less_than(succ(a), succ(b))`
  > NB: This theorem exists in std in `std/peano/order.b4m:92:succPreservesOrder`

- **`succInjective`** (`aata/2.3-primes.md:4809`)
  `forall a, b: Int; succ(a) = succ(b) -> a = b`
  > NB: This theorem exists in std in `std/integer.b4m:75:succInjective`
  > NB: This theorem exists in std in `std/integer/wellordering.b4m:46:succInjective`
  > NB: This theorem exists in std in `std/rational.b4m:677:succInjective`
  > NB: This theorem exists in std in `std/real.b4m:1049:succInjective`


## aata/3.1-integers-mod-n-exercises.md — 1

- **`mulSubtractsRight`** (`aata/3.1-integers-mod-n-exercises.md:115`)
  `forall a, b, c: Int; mul(a, sub(b, c)) = sub(mul(a, b), mul(a, c))`
  > NB: This theorem exists in std in `std/integer/divides.b4m:1101:distributesOverDifference`
  > NB: This theorem exists in std in `std/peano/subtraction.b4m:425:mulSubDistribLeft`


## aata/3.2-groups-exercises.md — 1

- **`affineStarIsAssociative`** (`aata/3.2-groups-exercises.md:114`)
  `forall a, b, c: NotMinusOne; star(star(a, b), c) = star(a, star(b, c))`
  > NB: This theorem exists in std in `std/real/affine-group.b4m:60:starIsAssociative`
  > NB: This theorem exists in std in `std/real/affine-group.b4m:462:starAssociativeOnCut`


## aata/3.3-subgroups-exercises.md — 1

- **`oneIsNotZero`** (`aata/3.3-subgroups-exercises.md:658`)
  `succ(ZERO) != ZERO`
  > NB: This theorem exists in std in `std/rational/examples.b4m:152:successorOfZeroIsNonzero`
  > NB: This theorem exists in std in `std/real/examples.b4m:228:successorOfZeroIsNonzero`


## aata/4.1-cyclic-subgroups-exercises.md — 4

- **`productsHaveSameOrder`** (`aata/4.1-cyclic-subgroups-exercises.md:502`)
  `forall a, b: G; forall n: Int; hasOrder(op(a, b), n) -> hasOrder(op(b, a), n)`
  > NB: This theorem exists in std in `std/group/order.b4m:1280:productsHaveSameOrder`

- **`lcmPowerGeneratesIntoTheIntersection`** (`aata/4.1-cyclic-subgroups-exercises.md:663`)
  `forall a: G; forall m, n: Int; forall x: G; inGenerated(power(a, lcm(m, n)), x) -> (inGenerated(power(a, m), x) and inGenerated(power(a, n), x))`
  > NB: This theorem exists in std in `std/group/generated.b4m:1142:lcmPowerIsInBothSubgroups`

- **`lcmPowerGeneratesTheIntersection`** (`aata/4.1-cyclic-subgroups-exercises.md:670`)
  `forall a: G; hasInfiniteOrder(a) -> forall m, n: Int; forall x: G; (inGenerated(power(a, m), x) and inGenerated(power(a, n), x)) iff inGenerated(power`
  > NB: This theorem exists in std in `std/group/generated.b4m:1346:intersectionOfPowerSubgroupsIsLcmSubgroup`

- **`torsionClosedUnderOpAbelian`** (`aata/4.1-cyclic-subgroups-exercises.md:745`)
  `forall g, h: G; hasFiniteOrder(g) -> hasFiniteOrder(h) -> hasFiniteOrder(op(g, h))`
  > NB: This theorem exists in std in `std/group/order.b4m:1398:productHasFiniteOrderAbelian`


## aata/4.1-cyclic-subgroups.md — 1

- **`cyclicClosedUnderOp`** (`aata/4.1-cyclic-subgroups.md:112`)
  `forall g, h: G; inCyclic(g) -> inCyclic(h) -> inCyclic(op(g, h))`
  > NB: This theorem exists in std in `std/group/order-divides.b4m:80:cyclicClosedOp`


## aata/4.2-complex-multiplicative-group-exercises.md — 1

- **`modulusOfConjugate`** (`aata/4.2-complex-multiplicative-group-exercises.md:45`)
  `forall z: C; abs(conj(z)) = abs(z)`
  > NB: This theorem exists in std in `std/complex/modulus.b4m:116:absConj`


## aata/4.2-complex-multiplicative-group.md — 2

- **`modulusOfConjugate`** (`aata/4.2-complex-multiplicative-group.md:85`)
  `forall z: C; abs(conj(z)) = abs(z)`
  > NB: This theorem exists in std in `std/complex/modulus.b4m:116:absConj`

- **`circleGroupClosedUnderProduct`** (`aata/4.2-complex-multiplicative-group.md:222`)
  `forall z, w: C; onCircle(z) -> onCircle(w) -> onCircle(mul(z, w))`
  > NB: This theorem exists in std in `std/complex/polar.b4m:911:circleClosedUnderProduct`


## aata/5.1-permutation-groups-exercises.md — 1

- **`twoIsSuccSuccZero`** (`aata/5.1-permutation-groups-exercises.md:400`)
  `TWO = succ(succ(ZERO))`
  > NB: This theorem exists in std in `std/group/listing.b4m:997:twoIsSuccSuccZero`


## aata/5.1-permutation-groups.md — 7

- **`composeIsAssociative`** (`aata/5.1-permutation-groups.md:83`)
  `forall h, g, f: Perm; compose(compose(h, g), f) = compose(h, compose(g, f))`
  > NB: This theorem exists in std in `std/function/invertible.b4m:36:composeAssoc`

- **`identityIsAPermutation`** (`aata/5.1-permutation-groups.md:111`)
  `invertible(identityFn)`
  > NB: This theorem exists in std in `std/function/invertible.b4m:201:identityInvertible`

- **`identityActsAsTheGroupIdentity`** (`aata/5.1-permutation-groups.md:118`)
  `forall f: Perm; compose(identityFn, f) = f`
  > NB: This theorem exists in std in `std/function/invertible.b4m:140:composeIdentityLeft`

- **`reversedIndexInRange`** (`aata/5.1-permutation-groups.md:496`)
  `forall n: Nat; forall i: Nat; less_than(i, n) -> less_than(sub(n, succ(i)), n)`
  > NB: This theorem exists in std in `std/permutation/alternating.b4m:201:reversedIndexInRange`

- **`nothingBelowZeroIsATransposition`** (`aata/5.1-permutation-groups.md:1034`)
  `forall s: Seq; forall i: Nat; less_than(i, ZERO) -> isTransposition(at(s, i))`
  > NB: This theorem exists in std in `std/permutation/alternating.b4m:122:nothingBelowZeroIsATransposition`

- **`twoDividesNoTwoConsecutive`** (`aata/5.1-permutation-groups.md:1603`)
  `forall m: Nat; divides(TWO, m) -> (not divides(TWO, succ(m)))`
  > NB: This theorem exists in std in `std/peano/parity.b4m:478:twoDividesNoTwoConsecutive`

- **`evenIsNotOdd`** (`aata/5.1-permutation-groups.md:1663`)
  `forall t: Fn; isEvenPerm(t) -> (not isOddPerm(t))`
  > NB: This theorem exists in std in `std/permutation/alternating.b4m:988:evenIsNotOdd`


## aata/7.1-private-key-cryptography.md — 1

- **`affineDecodes`** (`aata/7.1-private-key-cryptography.md:80`)
  `forall a: Zn; forall b: Zn; forall p: Zn; isUnit(a) -> add(mul(unitInverse(a), add(mul(a, p), b)), neg(mul(unitInverse(a), b))) = p`
  > NB: This theorem exists in std in `std/integer/mod-n.b4m:1312:anAffineCipherWithAUnitMultiplierDecodes`


---

# SCOPE RULING (user, 2026-10-18) — WHICH theorems must be written out

> *"You ONLY need to prove theorems that have proof text in judson or say 'proof is in
> exercise'."* … *"if judson says 'proof left to reader' you should do that too."*

So a Class-1 site is a real defect **only** when Judson signals that a proof is expected.
Three qualifying signals:

1. **`<proof>`** — he spells the argument out.
2. **"left as an exercise"** — he forwards it (the aata guide already requires these be
   proved in the MAIN TEXT, with only a prose pointer in the exercise slot).
3. **"left to the reader"** — same obligation.

A result he **states flatly**, with no proof and no forwarding, has no proof structure to
transcribe. **Those may stay citations** — aliasing them was never a defect, and this
supersedes the audit's per-chapter Class-1 counts.

## Measured against the vendored XML

Every `<theorem>/<lemma>/<corollary>/<proposition>` in the ten in-scope files, classified by
whether it carries a `<proof>`, is forwarded in the surrounding prose, or is bare:

| chapter | XML | has `<proof>` | forwarded | **in scope** | bare (citation OK) |
|---|---|---|---|---|---|
| 1.2.x | `sets.xml` | 5 | 0 | **5** | 1 |
| 2.x | `integers.xml` | 7 | 0 | **7** | 1 |
| 3.x | `groups.xml` | 7 | 2 | **9** | 1 |
| 4.x | `cyclic.xml` | 7 | 1 | **8** | 3 |
| 5.x | `permute.xml` | 9 | 0 | **9** | 3 |
| 6.x | `cosets.xml` | 9 | 1 | **10** | 3 |
| 9.x | `isomorph.xml` | 10 | 2 | **12** | 2 |
| 10.x | `normal.xml` | 6 | 0 | **6** | 0 |
| 11.x | `homomorph.xml` | 4 | 0 | **4** | 2 |
| **total** | | **64** | **6** | **70** | **16** |

**~70 results to write out, not ~146.** The audit's Class-1 count conflated "is an alias"
with "is a defect"; under this ruling roughly half the sites it listed are legitimate
citations of results Judson never proves.

**A caveat on the forwarded count.** An element-scoped scan reports *zero* forwarded proofs,
because Judson almost always puts the forwarding in the prose **around** the result, not
inside it. Scanning the surrounding prose finds 14 forwarding phrases, of which 6 attach
cleanly to a numbered result. The other 8 forward a *part* of a proof or an unnumbered claim
and still create an obligation — list, with the exact wording:

- `groups.xml` — "We leave the proof as an exercise" (**cancellation laws**, his Ex. 30)
- `groups.xml` — "We will leave the proof of this theorem as an exercise" (**laws of
  exponents**, his Ex. 29)
- `groups.xml` — "We will leave this task as an exercise" (closure of $SL_2(\mathbb{R})$
  under multiplication)
- `cyclic.xml` — "The proof … is straightforward and is left as an exercise"
  (**polar multiplication**)
- `permute.xml` — "We leave the proof that $|S_n| = n!$ as an exercise"
- `permute.xml` — "The proof for the case in which $\sigma$ can be expressed as an odd
  number of transpositions is left as an exercise"
- `permute.xml` — "We will leave the proof that $\lambda_\sigma$ is surjective to the reader"
- `permute.xml` — "We will leave the proof that $srs = r^{-1}$ as an exercise"
  (**the dihedral relation** — note §5.2 currently takes this as an `axiom` and the exercise
  slot aliases it, so *neither* slot proves it)
- `cosets.xml` — "(We leave its proof as an exercise.)" (**Lemma 6.3**)
- `isomorph.xml` — "whose proof is left as an exercise" (**isomorphism is an equivalence
  relation**, his Thm 9.10)
- `isomorph.xml` — "We will leave the proof that $\phi$ is one-to-one and onto as an exercise"
- `isomorph.xml` — "We will leave the proof of the following theorem as an exercise"
  (**internal direct products**)
- `sets.xml` — "The proof of (2) is left as an exercise" (**De Morgan**, second part)
- `sets.xml` — "Part (2) is left as an exercise" (**composition of injections/surjections**)

## The 16 bare statements — citations are legitimate

These he states without proof and without forwarding. Several were on the audit's Class-1
list and should come off it:


- `sets.xml` **(unnamed)** — Two equivalence classes of an equivalence relation are either disjoint o
- `integers.xml` **integers-corollary-coprime** — Let a and b be two integers that are relatively prime. Then there exist 
- `groups.xml` **(unnamed)** — If g is any element in a group G , then the inverse of g , denoted by g^
- `cyclic.xml` **(unnamed)** — The subgroups of {\mathbb Z} are exactly n{\mathbb Z} for n = 0, 1, 2,\l
- `cyclic.xml` **cyclic-corollary-mod-n-generators** — The generators of {\mathbb Z}_n are the integers r such that 1 \leq r \l
- `cyclic.xml` **(unnamed)** — The circle group is a subgroup of {\mathbb C}^* .
- `permute.xml` **(unnamed)** — Any permutation of a finite set containing at least two elements can be 
- `permute.xml` **(unnamed)** — The dihedral group, D_n , is a subgroup of S_n of order 2n .
- `permute.xml` **permute-proposition-motions-cube** — The group of rigid motions of a cube contains 24 elements.
- `cosets.xml` **cosets-corollary-theorem-6** — Suppose that G is a finite group and g \in G . Then the order of g must 
- `cosets.xml` **cosets-theorem-theorem-11** — Let U(n) be the group of units in {\mathbb Z}_n . Then |U(n)| = \phi(n) 
- `cosets.xml` **cosets-theorem-theorem-13** — Fermat's Little Theorem Fermat's Little Theorem Let p be any prime numbe
- `isomorph.xml` **(unnamed)** — Let (g_1, \ldots, g_n) \in \prod G_i . If g_i has finite order r_i in G_
- `isomorph.xml` **isomorph-corollary-relatively-prime** — Let n_1, \ldots, n_k be positive integers. Then \prod_{i=1}^k {\mathbb Z
- `homomorph.xml` **(unnamed)** — Let \phi : G \rightarrow H be a group homomorphism. Then the kernel of \
- `homomorph.xml` **homomorph-theorem-third-isomorphism** — Third Isomorphism Theorem Third Isomorphism Theorem for groups Let G be 

Notable consequences: **Theorem 6.15** ($|U(n)| = \varphi(n)$), **Corollary 6.10** (order
divides $|G|$), **Fermat's Little Theorem**, the **Third Isomorphism Theorem**, the
**kernel-is-normal** corollary, $|D_n| = 2n$, and **every-permutation-is-a-product-of-
transpositions** are all bare in the book. The audit flagged most of them as Class-1
defects; under this ruling they are not. The §6.3/§7.2 "statement mismatch" residue largely
dissolves with them.


---

# PINNED FOR THE END OF THE SWEEP (user, 2026-10-18)

## §9.2's `cubeIsIdentityComponentwise` — Theorem 9.17 proper

`aata/9.2:96` proves a hardcoded **k = 3 instance** where Judson states the general
order/lcm theorem: the order of $(g,h)$ in $G \times H$ is $\mathrm{lcm}(|g|,|h|)$.
CHAPTER9-PAINPOINTS calls the k=3 form "the tell that the general version was wanted and
skipped". The general version needs `power` over the pair sort plus lcm minimality; the
`ProductGroup` model makes `std/group/power.b4m` available and `std/integer/lattice.b4m`
carries lcm minimality, and the painpoints text says "neither connection is made" — not
that it cannot be. **Probe before deciding.** User: do it at the end.

## The five deferred axiomatization items (unchanged)

Still flagged-not-changed, to be taken one at a time after the main sweep:
`1.2.3-partitions:484` (`axiom quotientContains`), `4.1:494` + `:950`, `3.3:39`+`:69`
(subgroup criterion as axioms), `5.2:88` (dihedral relations as axioms),
`1.2.3-partitions:822` (the converse Judson proves, dropped as "left to a later section").

## Settled, no longer owed

- **§9.1 Theorem 9.10** — isomorphism as an equivalence relation. Proved pairwise over
  the concrete declared groups; this is the right form and needs nothing further.
- **§9.1 Theorem 9.7** — proved (both halves of his map); only the `≅` restatement is an
  (a) aside.
- **§9.1 Theorems 9.8, 9.9** — transcribed with his own proofs; the varying-modulus
  limit is a real (a) aside (`std/integer/mod-n.b4m`'s single `const N`).
