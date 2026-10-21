# AATA transcription audit — WHAT REMAINS

**Status 2026-10-21: the corpus is NOT a transliteration yet. 159 defects measured across 24
files.** The text is GFDL, so the target is Judson's words essentially VERBATIM — as the user
put it, "we are aiming for a near exact transliteration, otherwise this exercise is
nonsensical." A comprehensive machine scan plus three agent audits against
`vendor/aata/src/*.xml` found that the corpus systematically PARAPHRASES and TRUNCATES him.

Gates green throughout: `check aata` 40 files / 423 theorems; `check std --library` strict
109 files / 1485; `zig build test` 205/205. **None of this is a proof defect** — the
mathematics checks. It is a fidelity defect in the prose.

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

## 1. SETTLED SCOPE — read before fixing anything

**"Invented proofs" are DELIBERATE and the proofs STAY** (user ruling, 2026-10-21). Where
Judson writes "we leave the proof as an exercise", supplying the proof is the POINT of this
exercise, not a defect. The audits flagged 5 such sites as the worst category; that
classification is withdrawn.

**What IS still wrong at those 5 sites: nothing marks the proof as ours.** Verified
2026-10-21 — "We leave the proof as an exercise" appears NOWHERE in `3.2-groups.md`,
`11.1-group-homomorphisms.md` or `5.2-dihedral-groups.md`, so a reader takes our argument for
his.

**THE FIX (user ruling, 2026-10-21).** In this limited case, do NOT restore his sentence
verbatim. Replace it with:

> Judson's text leaves this proof as an exercise:

then our `**Proof.**` follows. This is the one place a "Judson's text …" sentence belongs in
BODY prose rather than a blockquote aside — it is the attribution that makes the following
proof honestly ours. Sites: `3.2:506`, `3.2:647`, `11.1:517`, `9.2:156`, `5.2:25`/`:50`.

Judson's exact words at each:
- `3.2:506` — "This proposition tells us that the right and left cancellation laws are true in
  groups. We leave the proof as an exercise."
- `3.2:647` — "We will leave the proof of this theorem as an exercise. Notice that
  $(gh)^n \neq g^nh^n$ in general, since the group may not be abelian."
- `11.1:517` — his Theorem 11.6 has no proof; he states it as prose BEFORE the theorem: "In
  fact, this subgroup is a normal subgroup of $G$ since the trivial subgroup is normal in $H$.
  We state this result in the following theorem…"
- `5.2:25`/`:50` — "We will leave the proof that $srs = r^{-1}$ as an exercise."
- `9.2:156` — his Corollary 9.17 has NO proof (the proof belongs to Theorem 9.16, which is
  missing entirely — see item 3).

## 2. The one real Class-1 THEOREM defect

**`aata/9.1` `leftTranslationIsInjective`** is a one-line `[using model(...)]`, but Judson
SHOWS the argument (`isomorph.xml`, Cayley):

> "To show that $\lambda_g$ is one-to-one, suppose that $\lambda_g(a) = \lambda_g(b)$. Then
> $$ga =\lambda_g(a) = \lambda_g(b) = gb.$$ Hence, $a = b$."

Three steps: assume equal, unfold both sides, cancel on the left. Transcribe it.

**VERIFIED FAITHFUL — do not "fix" these** (each read against the XML 2026-10-21):

| site | Judson's text | why a one-liner is right |
|---|---|---|
| `9.2` `prodIdentityRight`/`prodInverseRight`/`prodCancelLeft` | "The fact that the operation is associative **follows directly from the associativity of $G$ and $H$**." | a `model` transfer IS that; expanding it would be LESS faithful |
| `9.1` `theExponentMapPreservesTheOperation` | writes the chain $\phi(x+y) = e^{x+y} = e^xe^y = \phi(x)\phi(y)$ | one chain, one step |
| `9.1` `theExponentMapIsInjective` | "but this **can be determined using calculus**" — declines | nothing to transcribe |
| `5.1` `identityIsAPermutation` | "The identity of $S_n$ is just the identity map that sends 1 to 1, 2 to 2, …" | bare assertion, no structure |

## 3. THE SERIOUS DEFECTS — missing Judson text (35 sites, scanner-invisible)

These are absent, not rewritten, so nothing flagged them. Ordered by consequence.

**(a) `5.1` never defines EVEN/ODD permutation, and never states Theorem 5.16.** Judson:

> "In light of [Theorem 5.16], we define a permutation to be **even** if it can be expressed
> as an even number of transpositions and **odd** if it can be expressed as an odd number of
> transpositions."

Our `5.1:1525` goes straight to "the set of all even permutations, $A_n$" — using a term the
chapter never defines. **All of §10.2's simplicity argument rests on it.** Highest priority.

**(b) `11.2`'s Correspondence Theorem drops its fourth paragraph** (normal subgroups
correspond) — which is exactly the text his "Notice that in the course of the proof of
Theorem 11.13…" refers to, and which our `:1541` then narrates as "the route the
Correspondence Theorem's last paragraph sketches", pointing at text the file never carries.

**(c) `9.2` drops Theorem 9.16 (the order of a PAIR) and its proof entirely**, keeping only
the tuple corollary, relabelling it "Theorem 9.17", and attaching a proof of our own. He gives
the corollary no proof.

**(d) `10.2`'s five-case cycle-structure proof**: ~2 printed pages in Judson with every
conjugation computed → three sentences in ours.

**(e) `2.1` drops his Well-Ordering lemma AND theorem AND both proofs**, plus his $2^n > n+4$
example, the binomial theorem example, and the closing recursive-definitions paragraph on $n!$
(pure prose, needs no formalisation).

**(f) `3.1` drops its entire "Symmetries" subsection** — which the file's own title and header
promise.

**(g) `5.2` drops the $D_4$ example and the whole $S_4$-cube proof**; his one two-part theorem
with one proof was split into two theorems with two proofs of ours.

**(h) `7.1` carries only 56% of his §7.1 vocabulary** — the missing material is his exposition
ON CRYPTOGRAPHY (plaintext/ciphertext, monoalphabetic vs polyalphabetic, frequency analysis).
`7.2` drops its entire opening (Diffie–Hellman 1976, the one-way function discussion), the
factoring-difficulty paragraph, the digitizing scheme, and the last two sentences of Message
Verification.

**(i) `5.1` drops ~8 worked cycle/permutation examples** and both proofs for Prop 5.8 / Thm 5.9.

**(j) `4.2` drops four worked examples and two exposition paragraphs WHILE ITS HEADER CLAIMS
"The book's prose is reproduced in order"** — a false claim in the file. Also `9.2` drops its
opening decomposition paragraph, the $\mathbb{R}^2$ and
$\mathbb{Z}_2\times\mathbb{Z}_2$-vs-$\mathbb{Z}_4$ examples, the $\prod G_i$ paragraph, the
$\mathbb{Z}_2^n$ example, both $\gcd$ corollaries, and the $\mathbb{Z}_6$ example.

## 4. PARAPHRASE — his sentences rewritten (23 sites)

The pattern: his displayed computation collapsed to its result, or his justification replaced
by ours. The canonical case, VERIFIED at `integers.xml`, is `2.3-primes.md:533` (Bézout):

| Judson | ours |
|---|---|
| "Clearly, the set $S$ is nonempty; hence, by the Well-Ordering Principle…" | our own justification inserted |
| $r' = a - dq = a - (ar + bs)q = a - arq - bsq = a(1-rq) + b(-sq)$ | collapsed to just the result |
| "if we let $a = d'h$ and $b = d'k$, then $d = ar + bs = d'hr + d'ks = d'(hr + ks)$" | replaced by a one-line gloss |

Worse in the same file: four of his five §2.2 proofs are **not transliterated at all** — the
Coprime Corollary has a proof HE NEVER WROTE, Euclid's Lemma and the Infinitude of Primes are
rewritten with their statements missing, and both halves of the FTA are substituted.
"Relatively prime" is never defined though it is a hypothesis at `:953`.

**Three sites are his words RELOCATED into our gloss** (`11.1:178`, `4.2:526`, `9.1:715`):
they read as our commentary but are literally his sentences, so restoring the proof makes the
gloss redundant — ONE edit, not two.

**`4.3-repeated-squares` is the least defensible**: pure prose with no formal content to trade
against, condensed throughout (the $2^{2^{1{,}000{,}000}}$ motivation, both framing sentences,
the $271^{2^2}$ chain, the $(a^{2^n})^2 \equiv a^{2^{n+1}}$ remark).

## 5. OUR PROSE IN HIS REGISTER (~51 sites — one mechanical pass)

Group 1's central finding, and the cheapest fix in the audit. Whenever the kernel needs a lemma
Judson does not state, a paragraph was written IN HIS REGISTER and dropped into the
transliterated flow as body text — "Three ring facts come first", "Two more facts the next
proof needs", "The **peel step** shared by both uniqueness inductions". Each is individually
useful; a reader cannot tell it from Judson.

**One pass demoting every such paragraph to a `>` aside fixes all ~51.** Also in this class:
the 16 narration sites (`9.2:245`/`:721`/`:291`, `11.2:896`/`:938`, `5.1:500`/`:505`/`:792`,
`10.1:663`, `6.3:151`, `10.2:219`, `6.2:1011`, `9.2:510`, `7.2:253`, `3.2:197`) — our
commentary ABOUT his argument. Several are legitimate declared divergences in the WRONG FORM
(body prose instead of a blockquote); `7.2:253` and `3.2:197` are simply deleted.

## 6. VERIFIED LEGITIMATE — leave alone

- `1.2.2-functions.md` is **clean** (0 defects).
- `6.2-lagranges-theorem` is essentially clean: every proof Judson writes out (Lemma 6.8,
  Thm 6.9, Cor 6.11, Cor 6.12) is faithful, as are all statements.
- 47 of the 149 flagged paragraphs cleared as faithful or legitimately-needed scaffolding
  (18 in group 2, 11 in group 3, the rest in group 1).
- `5.1-permutation-groups-exercises:231`/`:467`/`:820` — inside `**Deferred:**` blocks, which
  stay verbatim by ruling.
- `5.2:210`, `6.1:113`, `9.1:426` — "Judson leaves the proof as an exercise", accepted
  forwarding language.
- 7 attribution headers.
- `6.1:580`/`:803` point at Lemma 6.6, which lives in §6.2 past 6.1's declared scope — fine.

## 7. SCOPE RULINGS — all settled 2026-10-21

**1. NUMERICS ARE NOT IN SCOPE.** Judson's numeric worked examples and figures are not
transliterated: $z = 2\cis 60°$, $3\sqrt2 - 3\sqrt2 i$, $(1+i)^{10}$, the 8th roots of unity,
$D_4$'s eight elements in cycle form, the $S_4$/cube diagonal argument, the ~8 worked
cycle/permutation examples in §5.1, the $\mathbb{Z}_2^n$ binary-tuple example, his $(8,56)$
order computation, and the rest of that kind. **This removes a large slice of the item-3 and
item-4 lists** — every "worked example absent" finding is now out of scope, not a defect.

Consequence: **`4.2`'s header must be amended.** It currently claims "The book's prose is
reproduced in order", which is false while his examples are omitted. Reword to say prose is
reproduced in order and numeric worked examples are omitted.

**2. CHAPTER 7's CRYPTOGRAPHY EXPOSITION may be elided WHOLESALE**, with one declaration
rather than paragraph-by-paragraph asides. Use approximately:

> *Judson's text includes a section on cryptography which we don't include here.*

That covers §7.1's plaintext/ciphertext vocabulary, monoalphabetic vs polyalphabetic ciphers,
frequency analysis, the Alice/Bob setup, the Diffie–Hellman opening of §7.2, the
factoring-difficulty passage and the digitizing scheme — i.e. all of finding (h). The
formalisable content (the RSA correctness chain, Euler's theorem, message verification) stays
transliterated as it is.

**3. SETTLED by exception (d).** His FTA existence argues by Well-Ordering over a set of
integers; his FTA uniqueness assumes both factorizations sorted ascending. Neither is
available in the current encoding, so both take a `>` aside naming his structure and ours.
Group 1 drafted the wording; use it. The same exception covers any other site where our
axiomatic strategy diverges and reconciling would be disproportionate — including §5.2's
dihedral relations (he derives them from the $n$-gon geometry, we take them as a presentation)
and §10.2's five-case exhaustiveness (he asserts the list, we take the disjunction as a
hypothesis).

## 8. Per-file defect counts

| file | TRUNC | PARA | NARR | NO-SRC | total |
|---|---|---|---|---|---|
| 2.3-primes.md | 2 | 1 | 0 | 33 | 36 |
| 11.2-the-isomorphism-theorems.md | 6 | 2 | 6 | 1 | 15 |
| 5.1-permutation-groups.md | 3 | 2 | 4 | 0 | 9 |
| 6.2-lagranges-theorem.md | 0 | 1 | 1 | 6 | 8 |
| 1.2.3-partitions.md | 0 | 1 | 0 | 6 | 7 |
| 2.2-division-algorithm.md | 1 | 1 | 0 | 5 | 7 |
| 5.2-dihedral-groups.md | 4 | 1 | 0 | 2 | 7 |
| 9.2-direct-products.md | 2 | 1 | 3 | 1 | 7 |
| 10.1-factor-groups-and-normal-subgroups.md | 3 | 1 | 3 | 0 | 7 |
| 6.3-fermat-and-eulers-theorems.md | 2 | 1 | 3 | 1 | 7 |
| 2.1-induction.md | 5 | 0 | 0 | 0 | 5 |
| 4.2-complex-multiplicative-group.md | 3 | 2 | 0 | 0 | 5 |
| 9.1-definition-and-examples.md | 2 | 3 | 0 | 0 | 5 |
| 3.2-groups.md | 1 | 0 | 2 | 1 | 4 |
| 4.1-cyclic-subgroups.md | 0 | 2 | 2 | 0 | 4 |
| 6.1-cosets.md | 3 | 1 | 0 | 0 | 4 |
| 7.2-public-key-cryptography.md | 3 | 0 | 1 | 0 | 4 |
| 4.3-repeated-squares.md | 1 | 2 | 0 | 1 | 4 |
| 1.2.3-relations.md | 2 | 0 | 0 | 1 | 3 |
| 3.1-integers-mod-n.md | 2 | 0 | 0 | 1 | 3 |
| 3.3-subgroups.md | 2 | 1 | 0 | 0 | 3 |
| 11.1-group-homomorphisms.md | 1 | 0 | 1 | 1 | 3 |
| 10.2-the-simplicity-of-the-alternating-group.md | 1 | 0 | 1 | 0 | 2 |
| 1.2.2-functions.md | 0 | 0 | 0 | 0 | **0** |
| **TOTAL** | **49** | **23** | **27** | **60** | **159** |

Suggested order:
1. **item 3(a)** — the missing even/odd definition. §10.2 depends on it, so it is both the
   highest-consequence defect and a prerequisite.
2. **item 1** — the 5 forwarding-sentence attributions. Six one-line edits, and they remove
   the only sites where our argument reads as his.
3. **item 5** — the single mechanical pass demoting ~51 register-matched paragraphs plus the
   16 narration sites to `>` asides. Biggest count, lowest risk.
4. **items 3 and 4** chapter by chapter, worst first: `2.3-primes` (36), `11.2` (15),
   `5.1` (9), then the rest.

Note the per-file counts in item 8 predate the ruling in item 1, so five of the 159 are now
one-line attributions rather than defects of substance.

## 9. The engine question — HALF CLOSED 2026-10-20

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

## 10. The duplicate catalog — DONE 2026-10-20

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
| 2 | §4.1's three `m` axioms | ~~derived from well-ordering~~ **REOPENED** — see OPEN ITEM 3; the derivation is orphaned (0 citations) while the axiom has 4 |
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
