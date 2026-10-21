# Transliteration fidelity audit — group 2 (9 files)

Returned as text (the harness blocked the agent's file write); transcribed here verbatim in
substance, with Judson's quotes preserved.

**Brief-level note:** the briefs' "Judson source" guesses were WRONG on 4 of 9 files —
3.2 → `groups.xml` (not rings.xml); 10.2 → `normal.xml`, 11.1 → `homomorph.xml` (not
struct.xml); 7.2 → `crypt.xml` (not homomorph.xml). All findings are against the correct source.

## Three cross-cutting patterns

1. **Invented `**Proof.**` blocks where Judson says "we leave the proof as an exercise"** —
   3.2:506, 3.2:647, 11.1:517, 9.2:156, 5.2:25/:50. The worst sub-kind: our argument is
   substituted for his explicit forwarding sentence, which MISATTRIBUTES an argument to him.
2. **Whole-file prose omissions, with a header that claims completeness.** 4.2's header says
   "The book's prose is reproduced in order" while four worked examples and two exposition
   paragraphs are absent. 2.1, 5.2, 7.2, 9.2 have the same defect without the false claim.
3. **Judson's words relocated out of his proof into our gloss** — 11.1:178, 4.2:526, 9.1:715.
   These read as our commentary but are literally his sentences, so restoring the proof makes
   the gloss redundant: ONE edit, not two.

## Per-file defects

### aata/10.2-the-simplicity-of-the-alternating-group.md — 2
- **:200 TRUNCATED** — his five-case cycle-structure proof is ~2 printed pages with every
  conjugation computed; ours is three sentences. Paste his proof verbatim (`normal.xml`).
- **:219 NARRATION** — "Judson's text says … exhaustiveness is asserted rather than proved".
  Wrap as a `>` aside (legitimate declared divergence, wrong form).
- NOT defects: :38, :60, :65, :188, :215 — scaffolding; his Lemmas 10.8/10.9 proofs are
  verbatim at :54-58 and :177-186.

### aata/11.1-group-homomorphisms.md — 3
- **:97 TRUNCATED** — clauses (3) and (4) of Prop 11.4 compressed; his (4) includes the
  normality half (`\phi(g^{-1}hg) = [\phi(g)]^{-1}\phi(h)\phi(g) \in H_2`). Paste both.
- **:517 NARRATION/invented proof** — his Theorem 11.6 has NO proof; he states it as prose
  BEFORE the theorem ("In fact, this subgroup is a normal subgroup of $G$ since the trivial
  subgroup is normal in $H$. We state this result in the following theorem…"). Delete our
  `**Proof.**`, move his two sentences above the statement.
- **:178 NO-SOURCE** — this is where his truncated (4) text went. Delete once :97 is restored.
- NOT defects: :736 (his version is an exercise), :8-25, :26-43, :894-920 — verbatim.

### aata/2.1-induction.md — 5
- **:246 TRUNCATED** — keeps his "The Principle of Well-Ordering is equivalent to the
  Principle of Mathematical Induction" then replaces his LEMMA (1 is the least positive
  natural) + THEOREM (induction ⇒ well-ordering) + both proofs with our contrapositive sketch.
  Paste his lemma and theorem; our sketch moves to a `>` aside.
- **:224 TRUNCATED** — his first sentence kept, remainder is ours. Move ours to an aside.
- **Whole-file omissions, undeclared:** (a) his `2^n > n+4` example with full induction;
  (b) the binomial theorem example with the `\binom{n+1}{k} = \binom{n}{k} + \binom{n}{k-1}`
  lemma; (c) the closing recursive-definitions paragraph on `n!` (pure prose, needs no
  formalisation at all).
- NOT defects: :140, :161 — support the substituted `3 | 4^n - 1` example, whose divergence
  IS declared at :89.

### aata/3.2-groups.md — 4
- **:204 TRUNCATED** — his five sentences on identity uniqueness ("If we think of $e$ as the
  identity, then $ee' = e'$; but if $e'$ is the identity, then $ee' = e$…") → our one.
- **:506 NARRATION/invented proof** — Judson: "We leave the proof as an exercise." VERIFIED
  against groups.xml. Restore his sentence; our proof shape to an aside.
- **:647 NARRATION/invented proof** — Judson: "We will leave the proof of this theorem as an
  exercise. Notice that $(gh)^n \neq g^nh^n$ in general, since the group may not be abelian."
- **:197 NO-SOURCE** — "The remainder of the section establishes…" has no counterpart. Delete.
- NOT defects: :206, :297, :348, :1137, :193, :213, :255-295, :504, :631, :1119 — verbatim.

### aata/4.2-complex-multiplicative-group.md — 5
- **:211 TRUNCATED+PARAPHRASED** — collapses FOUR Judson items (polar exposition, his
  proposition, DeMoivre's statement, DeMoivre's full inductive proof with the five-line
  display) into one paragraph.
- **:508 TRUNCATED** — the circle-group/roots-of-unity block: his two framing paragraphs, the
  `H = {1,-1,i,-i}` example, the theorem and its proof all compressed.
- **:526 PARAPHRASED** — his proof sentence ("The fact that these are all of the roots …
  follows from [the degree-$n$ corollary]") paraphrased out of his proof into our prose.
- **File-level omissions, undeclared** — worked examples ($z = 2+3i$/$w = 1-2i$;
  $z = 2\cis 60°$; $3\sqrt2 - 3\sqrt2 i$; $(1+i)^{10}$; the 8th roots with
  $\omega,\omega^3,\omega^5,\omega^7$), the rectangular-representation paragraph. **The
  header falsely claims "The book's prose is reproduced in order."**
- NOT defects: :101 (borderline, load-bearing text survives), :116, :227.

### aata/5.2-dihedral-groups.md — 7
- **:25 and :50 TRUNCATED+PARAPHRASED (one defect, two sites)** — Judson states ONE theorem
  with two parts and ONE proof; we split it into two theorems with two proofs of our own, and
  his proof is absent. His proof carries the $n$ rotations display, the $s_1 \ldots s_n$
  reflection labelling, the even/odd vertex case split, and "We will leave the proof that
  $srs = r^{-1}$ as an exercise."
- **:308 TRUNCATED** — the cube section keeps only his two statements; his two narrative
  paragraphs and the whole $S_4$ proof (six axes → all transpositions) are absent.
- **the $D_4$ example** — absent entirely, undeclared (his eight elements with cycle forms).
- **:55, :300 NO-SOURCE** — declared gaps sitting as body prose; wrap as asides. Note :300's
  "still prose: the even/odd case split" IS his text that :25 dropped.
- **:8 TRUNCATED (trivial)** — drops "Recall the symmetry group of an equilateral triangle in
  Chapter 3."
- NOT defects: :210 (accepted forwarding language), :213 (our own proposition, announced).

### aata/7.2-public-key-cryptography.md — 4
- **:253 NARRATION** — "Congruence, by contrast, *is* available and this file simply does not
  reach it:" — a dangling editorial sentence ending in a colon, followed by a heading. Delete.
- **Whole-file omissions, undeclared (3):** (a) the ENTIRE §7.2 opening (Diffie–Hellman 1976,
  the one-way function discussion); (b) the factoring-difficulty paragraph (the 150-digit /
  50-million-years passage) and the digitizing scheme (`A = 00, B = 02, …, Z = 25`);
  (c) the last two sentences of Message Verification (the $y' = x'^E \bmod n$ round trip).
- NOT defects: :36, :150, :263, :20-34, :240-262 — verbatim, with the non-formalisable second
  case properly declared in an aside.

### aata/9.1-definition-and-examples.md — 5
- **:649 TRUNCATED+PARAPHRASED** — the confirmed Cayley defect. Drops "We must find a group of
  permutations $\overline{G}$ that is isomorphic to $G$"; collapses
  $ga = \lambda_g(a) = \lambda_g(b) = gb$ to $ga = gb$; and omits his entire second half
  (defining $\overline{G}$, closure, $\lambda_e$, the inverse computation, and the isomorphism
  $\phi: g \mapsto \lambda_g$ with its operation-preservation and injectivity displays).
- **:715, :862, :987 PARAPHRASED** — his second-half text, rewritten as our gloss. Once :649
  is restored these reduce to bare lead-ins or are deleted. (:987's SECOND paragraph, "the
  **left regular representation**", is verbatim his — keep.)
- **:117 TRUNCATED** — his three isomorphism Examples ($\mathbb{Z}_4 \cong \langle i\rangle$
  with its four-value table; the exponential map; $\mathbb{Z} \cong \{2^n\}$ with its
  injectivity argument) compressed to one sentence. Two further examples
  ($U(8) \cong U(12)$, $S_3 \not\cong \mathbb{Z}_6$) absent.
- NOT defects: :232, :359, :407, :415, :423, :10 — verbatim word for word. :125, :241, :292,
  :381 are lead-ins. :426 is accepted forwarding language.

### aata/9.2-direct-products.md — 7
- **:147+:156 TRUNCATED** — his Theorem 9.16 (order of a PAIR) and its proof are ABSENT; we
  keep only the tuple corollary, relabel it "Theorem 9.17", and attach a proof of our own
  invention. He gives the corollary NO proof.
- **:245, :721, :291 NARRATION** — "that is exactly what Judson's proof turns on",
  "Judson's chain", "And his squeeze follows". His chain is already verbatim at :508-511.
- **:510 NO-SOURCE** — "The two halves he does prove" is commentary; reword to a bare lead-in.
- **:84 PARAPHRASED (borderline)** — his four sentences reordered into one, closure dropped.
- **File-level omissions, undeclared** — the opening decomposition paragraph; the
  $\mathbb{R}^2$ and $\mathbb{Z}_2\times\mathbb{Z}_2$ vs $\mathbb{Z}_4$ examples; the
  external-direct-product/$\prod G_i$/$G^n$ paragraph; the $\mathbb{Z}_2^n$ binary-tuple
  example; both $\gcd$ corollaries with proof; the $n$-fold internal direct product
  definition; the $\mathbb{Z}_6$ example.
- NOT defects: :455, :477, :485, :493, :496 — verbatim. :115, :162 lead-ins. :467 is an added
  illustration, not a replacement.

## Summary

| file | TRUNC | PARA | NARR | NO-SRC | defects |
|---|---|---|---|---|---|
| 10.2-the-simplicity-of-the-alternating-group.md | 1 | 0 | 1 | 0 | 2 |
| 11.1-group-homomorphisms.md | 1 | 0 | 1 | 1 | 3 |
| 2.1-induction.md | 5 | 0 | 0 | 0 | 5 |
| 3.2-groups.md | 1 | 0 | 2 | 1 | 4 |
| 4.2-complex-multiplicative-group.md | 3 | 2 | 0 | 0 | 5 |
| 5.2-dihedral-groups.md | 4 | 1 | 0 | 2 | 7 |
| 7.2-public-key-cryptography.md | 3 | 0 | 1 | 0 | 4 |
| 9.1-definition-and-examples.md | 2 | 3 | 0 | 0 | 5 |
| 9.2-direct-products.md | 2 | 1 | 3 | 1 | 7 |
| **total** | **22** | **7** | **8** | **5** | **42** |

18 of 50 flagged paragraphs cleared as faithful or legitimately-needed scaffolding. 11 of the
42 defects were found OUTSIDE the flagged set — whole-file omissions the scorer cannot see,
because the omitted text is simply absent.
