# AATA transcription audit — RESOLVED 2026-10-21

**The corpus is now a transliteration.** The 2026-10-20 note claimed the work complete; a
comprehensive scan plus three agent audits found **159 defects across 24 files**, all of
which are now fixed. The text is GFDL, so the standard is Judson's words essentially
verbatim — "otherwise this exercise is nonsensical".

| main-text prose, non-aside | n | median fidelity | < 0.5 | < 0.3 |
|---|---|---|---|---|
| before | 472 | 0.84 | 150 | 91 |
| **after** | 468 | **0.94** | **67** | **34** |

Worst-first movement: `2.3-primes` 0.25 → 0.96, `3.1` 0.44 → 0.83, `6.3` 0.56 → 0.91,
`11.2` 0.69 → 0.94, `5.1` 0.70 → **1.00**. Two files sit just under 0.85 (`7.1` 0.81,
`3.1` 0.83), both carrying explicit elision declarations rather than silent gaps.

Gate: `check aata` 40 files / 7171 declarations / 423 theorems, exit 0 — unchanged
throughout, as it must be, since prose is not what the checker sees.

## What was structurally wrong

**Proofs simply ABSENT, now restored verbatim** — Bézout (with his four-step display),
Euclid's Lemma, the Infinitude of Primes, both FTA halves, Proposition 5.8, Theorem 5.9,
the parity lemma, Theorem 9.16, the Well-Ordering lemma and theorem, the Correspondence
Theorem's fourth paragraph, Cayley in full, DeMoivre, the roots of unity, the five-case
$A_n$ proof, the $S_4$ cube argument, Prop 11.4's clauses (3) and (4).

**Results used but never defined** — even/odd permutation (all of §10.2 rested on it),
"relatively prime" (a hypothesis at `2.3:955`), his own index-form disjointness definition.

**A promised subsection that did not exist** — §3.1's "Symmetries", named in the file's own
title and header.

**A false claim in a file** — `4.2`'s header said "The book's prose is reproduced in order"
while six passages were absent.

**~67 paragraphs of our prose in his register**, demoted to `>` asides, and 19 narration
sites cleared to zero. The content was legitimately needed; the defect was that a reader
could not tell it from the source.

**Three cases of his sentences relocated into our gloss** (`11.1:178`, `4.2:526`,
`9.1:715`) — restoring the proof made the gloss redundant, so each was one edit.

## The rulings that settled scope (all 2026-10-21)

1. **Invented proofs are DELIBERATE and the proofs STAY.** Where Judson leaves a proof as
   an exercise, supplying it is the point. The 5 sites instead read "Judson's text leaves
   this proof as an exercise:" before our `**Proof.**` — the one sanctioned "Judson's
   text …" in body prose, because it is what makes the following argument honestly ours.
2. **Exception (d), a DIVERGENT PROOF STRUCTURE**, added to the aside vocabulary. It
   carries the two FTA proofs (his existence uses Well-Ordering over a SET of integers; his
   uniqueness assumes both factorizations SORTED), §5.2's presentation-vs-geometry, §10.2's
   five-case exhaustiveness, and §5.1's nested-induction parity argument.
3. **Numerics are NOT in scope** — his worked examples and figures are not transliterated,
   and where they carried a general remark, the remark is kept.
4. **Chapter 7's cryptography exposition is elided wholesale** with one declaration.

## Reproducing the audit

    python3 drafts/aata-conformance/extract.py judson.json
    python3 drafts/aata-conformance/compare.py judson.json cmp.json

Per-defect findings with Judson's exact LaTeX: `drafts/aata-conformance/findings/`.

**The scan's blind spot, worth knowing**: `compare.py` scores paragraphs WE wrote, so it
cannot see paragraphs we DROPPED. 35 of the 159 defects were found only by scanning HIS
side for passages with no counterpart in ours — and those were the serious ones. Any future
audit must run both directions.

## What the scan measures, and how to re-run it

    python3 drafts/aata-conformance/extract.py judson.json      # his prose, per <proof>/<p>
    python3 drafts/aata-conformance/compare.py judson.json cmp.json

For each of our paragraphs, against its best match among his:
- **coverage** = fraction of HIS words we carry — low means TRUNCATION
- **fidelity** = fraction of OUR words that are his — low means PARAPHRASE

Symbol renames are normalized away (the transcription exception covers names and notation),
so the comparison is on WORDS.

| category | n | median fidelity | < 0.5 |
|---|---|---|---|
| MAIN-TEXT result/proof | 145 | **0.91** | 19 |
| MAIN-TEXT prose | 324 | 0.63 | 130 |
| exercise solution (ours by design) | 275 | 0.33 | 189 |
| blockquote aside (allowed) | 203 | 0.44 | 123 |
| attribution header (allowed) | 26 | 0.13 | 26 |

**Theorem statements and proofs are in good shape (0.91).** The damage is in inter-theorem
exposition.

**The scan has a blind spot worth knowing**: it scores paragraphs WE wrote, so it cannot see
paragraphs we DROPPED. A second pass over Judson's text found 138 of his passages with under
35% of their words anywhere in our corpus — 70 of those are his Sage/software sections (out of
scope), leaving **53 real math-prose gaps**. **35 of the 159 defects were invisible to the
scanner** for exactly this reason, and they are the most serious ones.

Full per-defect findings, each with Judson's exact LaTeX quoted so every fix is a paste:
`drafts/aata-conformance/findings/group{1,2,3}.md` (1002 + 153 + 1131 lines).

## The governing rules, for anyone picking this up

**Which theorems must be written out** (user ruling, 2026-10-18). Only where Judson
signals a proof is expected: he gives a `<proof>`, or says "left as an exercise", or says
"left to the reader". A result he states **flatly** has no proof structure to transcribe
and legitimately keeps a citation. Measured against the XML: 64 `<proof>` + 6 cleanly
attached forwards = ~70 in scope; **16 bare statements are not defects** (Corollary 6.10,
Theorem 6.15, Fermat's Little Theorem, the Third Isomorphism Theorem, $|D_n| = 2n$,
every-permutation-is-a-product-of-transpositions, and others).

**When in doubt, put the full theorem into aata** (user ruling, 2026-10-19). Imports from
`std` stay legal — alias the axioms, objects and helper lemmas a proof needs as *inputs* —
but a theorem itself must not be an alias or a one-line re-export.

**Prose must be Judson's.** The legitimate uses of "Judson …" are:
- (a) a real language limit;
- (b) an infeasible calculation;
- (c) a deliberate divergence reading "Judson does X, we are doing Y";
- (d) **a DIVERGENT PROOF STRUCTURE** (user ruling, 2026-10-21) — where we take a different
  axiomatic strategy and reconciling it with his would be a pain. Say so, naming his
  structure and ours.

(a)–(d) must sit in a markdown blockquote aside. Import-horizon reasoning ("which Judson has
in hand") is a defect. **Attribution headers stay.** **`Deferred:` / `Skipped` blocks stay
exactly as they are**, including the `std` paths inside them (user ruling, 2026-10-19).

**The ONE exception to the blockquote rule** (user ruling, 2026-10-21): where Judson leaves a
proof as an exercise and we supply one, the body prose reads "Judson's text leaves this proof
as an exercise:" immediately before our `**Proof.**`. That attribution belongs in the flow,
because it is what makes the following argument honestly ours rather than his.

---

# OPEN ITEMS

The transliteration items (1-8 of the 2026-10-20 list) are all RESOLVED; the detail is in
the commits from `aata: the comprehensive transliteration audit` through
`aata: group 2 complete`. Two things remain, neither about transliteration.

## 1. ~~Axiomatization ruling 2~~ — CLOSED 2026-10-21

§4.1's `const m` + `axiom mIsTheLeastPositiveExponent` are gone. The main theorem is
hypothetical in `m`, and `everySubgroupElementIsAPowerOfALeastExponent` unpacks
`aLeastPositiveExponentExists` (proved from `nonnegWellOrdering`) to discharge its
hypotheses — so the derivation is load-bearing instead of orphaned, and the three
projection theorems that existed only to read conjuncts off the axiom are gone with it.

`--axioms` now reports only `somePositivePowerIsInH`, which is Judson's own premise.
Axiom count down one, theorem added — the signature of closing a gap rather than
relabelling it. See `87d6043`.

**All five axiomatization rulings are now genuinely applied.**

## 2. The engine question — HALF CLOSED 2026-10-20

**CLOSED — an uncited import is now a hard error** (`8b7b6d7`). `check` fails with
`import 'X' (path) is never used — cite it, or remove it if the path is wrong`. A PARSE-TIME
syntactic check in `src/parser.zig`: an `unused_imports` map filled at the import decl,
drained in `stamp` (any `X.name` qualifier) and at the theory-rule argument
(`using import(X) thm`, `using model(X) …`, `arithmetic(X)`), reported at `parseFile`'s tail.

The user rejected the first design (a "used" bit at the six engine sites that resolve a
qualifier) as overengineering, and the parser version is also MORE correct: syntactic use is
complete by construction, where the six-site version was complete only until someone added a
seventh path. It also dissolved the hard case — six corpus imports are used ONLY inside
`model` blocks.

**STILL OPEN — the unused DECLARATION, and the mechanism is the blocker.**

What passes today, all for one reason — nothing in the file uses the declaration, so the
demand-driven engine never resolves it and never tests its target:

- `fact f = realFile.noSuchTheorem` — nothing cites `f`;
- `sort A = lib.X` with `import lib <<< "no-such-file.b4m"` — nothing uses `A`.

Measured 2026-10-20: all five alias kinds (`sort`/`pred`/`func`/`const`/`fact`) accept a
nonexistent target. Repros in `drafts/uncited-alias/`.

**Why the parse-time mechanism does NOT transfer.** An import is a CONSUMPTION — its purpose
is inward, so "this file never reaches it" is locally decidable and the file is the right
authority. A declaration is a PUBLICATION — its purpose is outward, and whether anything
needs it is a whole-corpus question a parser cannot answer.

**Measured, and it settles it: 470 distinct downstream references to non-fact forwards (835
total).** `std/permutation/simplicity.b4m` uses `permutation.transposition` 98 times, where
`transposition` is an alias in `std/permutation.b4m`; one aata file uses `peano.less_than` 49
times, forwarded there from `std/order.b4m`. That is the intended practice — import the
theory at the level you reason at and take its vocabulary; a façade re-exports its
sub-theories' vocabulary so consumers need not know the decomposition. So "an alias unused in
its own file is dead" would false-fail at scale.

**Where it belongs: `--library`**, which already sees the whole root set and would count those
835 references as uses. **The blocker is that no symbol-usage graph exists.** The axiom check
rides on `ctx.axiom_taint` — per proven theorem, the facts its proof rests on. Sorts, consts,
funcs and preds are used by appearing in STATEMENTS AND TERMS, not in a citation closure, and
every `Context` side table is fact-level (`axiom_taint`, `hole_taint`, `model_discharged`).
Building that graph is the design question to answer before any of this is implementable.

## 3. The duplicate catalog — DONE 2026-10-20

**159 cross-reference asides inserted across 29 files.** Generated and placed by
`python3 drafts/aata-audit/insert_asides.py --apply`, which regenerates the catalog
(`dup.py`) first, so it stays correct as `std` line numbers drift. Re-running is safe: it is
idempotent, recognizing all 159 and inserting nothing.

Placement (no precedent existed; set here): in PROSE, between the introducing text and the
```2b4m fence that declares the theorem. Not inside the fence — it would be parsed as 2b4m.
Not above the exercise statement — the aside annotates the proof, not the problem.

```
**Exercise 10.** Prove $A \cup B = (A \cap B) \cup (A \setminus B) \cup (B \setminus A)$.

> NB: This theorem exists in std in `std/set.b4m:1268:unionAsThreePieces`.

```2b4m
```

A theorem whose statement lives in two `std` theories gets one aside listing both, with a
bare `>` separating it from any following aside (else the next `> NB:` reads as another
bullet of the list).

**Duplication in `std` is encouraged** — these are cross-references, not a delete list.

Gate: `check aata` 40 files / 7193 declarations / 423 theorems, exit 0 — identical to
pre-insertion, as it must be, since asides are prose the checker never sees. All 29 files
fmt-clean.

# SETTLED — do not reopen

Every claim in this section was re-tested on 2026-10-21. Claims that did NOT hold were moved
to OPEN ITEMS above and are marked here. What stays is verified.

## Class 1: every chapter proves its own results

Ten chapters proved **zero theorems** when the audit opened (3.2, 6.1, 6.2, 6.3, 7.2, 9.1,
9.2, 10.1, 10.2, 11.2). All now carry their mathematics. **VERIFIED 2026-10-21**: the only
zero-theorem files are `4.3-repeated-squares.md` and its exercises, correctly — an algorithm
section with no stated proposition, saying so in the prescribed form.

**VERIFIED 2026-10-21**: zero main-text one-line re-exports was NOT true — 7 remained. Six are
faithful (Judson states those results flatly or declines their proofs) and one,
`9.1 leftTranslationIsInjective`, is a real defect. See OPEN ITEM 1.

Landed: Lagrange, Cayley, De Moivre, Euler, RSA correctness, Theorem 10.3, $|S_n| = n!$,
the disjoint-cycle decomposition, Theorem 9.7, Theorem 6.7, the full Second Isomorphism
Theorem, and all three Isomorphism Theorems plus Correspondence.

**Citations that are legitimate and must not be "fixed":**
1. **Schemas.** `judsonsLemmaTenTen` and `theAlternatingGroupIsSimple` are
   `theorem …(inN(Fn))`, parameterized by the subgroup predicate because there is no sort
   of subgroups. A schema has no body to lift; §10.2 instantiates both at $N = A_n$. Same
   for `splittingAListing` (`prop(Item)`).
2. **Bare statements** — see the scope ruling above.
3. **Cross-theory sort mismatches**: §10.2's two `normal.b4m` results are over `Grp` while
   that chapter speaks `Fn`.

## Class 2: prose is Judson's

Six false/contradictory claims fixed; §10.2's 142-line retrospective removed (it was nearly
half the file) with his Historical Note restored verbatim, as were §11.2's and §10.1's; all
8 import-horizon justifications stripped; §2.3's invented and colliding result numbers
dropped. Restored exposition includes §2.3's Euclidean Algorithm subsection (the 945/2415
worked example — "945" previously occurred nowhere in the corpus), his prime/composite
definition and Historical Note; §2.1's induction motivation; §1.2.3's partition and
equivalence-class definitions, his named Corollary, the mod-3 example and four relation
examples; and **§5.1's right-to-left composition convention remark**, the one omission that
affected correctness.

**Two corrections of fact**, both verified against the XML: §6.2 had misdescribed his $A_4$
argument as "exhaustion over $A_4$'s elements" (it is index 2 ⇒ $gHg^{-1} = H$, then
conjugating a 3-cycle); §7.2 had truncated his second RSA case to its first sentence.

## The five axiomatization rulings

| # | item | ruling |
|---|---|---|
| 1 | `1.2.3-partitions` `quotientContains` | definition block; `isTheClassOf` reports `— DEFINITION` |
| 2 | §4.1's three `m` axioms | **CLOSED 2026-10-21** (`87d6043`) — axiom deleted; the main theorem is hypothetical in `m` and a capstone unpacks the well-ordering existence proof to discharge it |
| 3 | §4.1 `cofactorBezout` | new std lemma `cofactorsSatisfyBezout`, then derived |
| 4 | §3.3's subgroup criterion | split: converse proved, forward half a real (a) limit |
| 5 | §5.2's dihedral relations | **kept** — they are the presentation of $D_n$ |

**The audit was wrong on item 1's premise**: it said comprehension should supply
`quotientContains`, but there is **no comprehension anywhere in `std`**, and
`std/equivalence.b4m` posits classes the same way. The fix was the reporting, not the axiom.
**Item 3 needed real mathematics** — `std` had `bezout` and `coprimeBezout` but nothing
saying a gcd's cofactors are coprime, which is *why* the chapter asserted it.

## Mechanical artifacts

**VERIFIED 2026-10-21** — all fixed, and re-checked: the four surviving `less_than` prose
hits in `2.3-primes.md` are all inside ```2b4m fences as `//` code comments, not chapter
exposition. 7 `less_than` text corruptions, 2 shipped "(Proof to fill:)" TODOs, a duplicated
paragraph, every exercise number in both chapter-1 exercise files (verified against the
XML), the dangling `std/group/group_lagrange.b4m` import, and 3 mispointed imports whose
name disagreed with their target.

## Lessons worth keeping

- **`--fast` is a STRUCTURAL check and that is the whole promise.** It does not resolve what
  references bind to, so a reference can bind to the **wrong declaration of the right
  shape** and pass. Not a `--fast` defect. Measured twice: `correspondence.b4m`'s
  `hHasIdentity: inHsub(EG)` vs `subgroup.b4m`'s `subgroupHasIdentity: inSubgroup(E)`
  (re-exported as `hHasIdentity`); and `complex/polar.b4m`'s `deMoivre` (cis, 2 args) vs
  `deMoivrePolar` (3 args). Risk scales with how many theories a proof cites across. Now
  recorded in `agents/2b4m-cheatsheet.md` and `GUIDE.md`.
- **A lifted proof needs its INPUTS aliased**, and dependency closure takes a few rounds;
  aliasing a std file's whole exported set at once beats chasing one error at a time.
- **Sibling std theories each declare their own group sort** (`subgroup_product.G` →
  `subgroup.b4m`, `correspondence.G` → `factor.b4m`), so lifted bodies need retyping.
- **`tautology` sees opaque atoms** — it cannot bridge `inN(e⁻¹h)`/`inN(h)`, substitute an
  equation, or flip one. A countermodel naming two atoms you believe are linked *is* the
  missing step.
- **A `define` cannot be aliased** (it is a macro) and **a definition block's clause
  variables take their sorts from argument positions**.
- **A predicated sort relativizes every binder**, so an ambient law needs an explicit
  `fix`/`generalize` to reach a guarded goal.
- When appending to a shared `std` file, **scope renames to the appended text** — a blanket
  regex broke `std/integer.b4m`'s own `ZERO`.
