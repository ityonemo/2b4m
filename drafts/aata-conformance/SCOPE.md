# AATA transliteration conformance — measured scope, 2026-10-21

The text is GFDL, so the target is NEAR-EXACT TRANSLITERATION of Judson's words, not a
paraphrase. Two scans, both reproducible from this directory:

    python3 drafts/aata-conformance/extract.py  judson.json   # his prose, per <proof>/<p>
    python3 drafts/aata-conformance/compare.py  judson.json cmp.json

`compare.py` scores each of our prose paragraphs against its best match among his:
  coverage = fraction of HIS words we carry   (low => TRUNCATION)
  fidelity = fraction of OUR words that are his (low => PARAPHRASE / our own narration)

## Direction 1 — our prose vs his (paraphrase)

976 prose paragraphs in `aata/*.md`, 773 outside blockquote asides. Median fidelity 0.50.
Classified:

| category | n | median fidelity | < 0.5 |
|---|---|---|---|
| MAIN-TEXT result/proof | 145 | **0.91** | 19 |
| MAIN-TEXT prose | 324 | 0.63 | 130 |
| exercise solution (ours by design) | 275 | 0.33 | 189 |
| blockquote aside (allowed) | 203 | 0.44 | 123 |
| attribution header (allowed) | 26 | 0.13 | 26 |

**The theorem statements and proofs are in good shape (0.91).** The defect concentrates in
inter-theorem exposition: **149 main-text paragraphs below 0.5**, led by `2.3-primes` (36),
`9.2` (9), `11.2` (8).

Three agents audited these against the XML; findings in `findings-group{1,2,3}.md`.

## Direction 2 — his prose with no counterpart in ours (truncation)

138 of Judson's paragraphs/proofs have under 35% of their words anywhere in our corpus.
Triaged:

| kind | n | verdict |
|---|---|---|
| Sage / software sections | 70 | out of scope — we do not transliterate his computational appendices |
| **MATH PROSE** | **53** | **real gaps** |
| geometric example / figure | 8 | needs a ruling: his cube/n-gon/triangle walkthroughs |
| historical note | 5 | should be carried (we restored several already) |
| meta / pedagogy | 2 | e.g. "a mathematical proof is nothing more than a convincing argument" |

The 53 math-prose gaps by chapter: crypt 22, sets 10, permute 5, groups 4, cyclic 4,
cosets 3, isomorph 3, integers 1, homomorph 1.

**Chapter 7 is the worst and is a measured outlier**: `aata/7.1-private-key-cryptography.md`
carries only **56%** of Judson's §7.1 vocabulary. The missing material is his exposition on
cryptography itself — plaintext/ciphertext, monoalphabetic vs polyalphabetic ciphers,
frequency analysis, the Alice/Bob setup — which the chapter skips to reach the formalizable
parts. That is exactly the "transliteration, not selective formalization" failure.

## Known individually

- `aata/9.1` Cayley (lines ~649-654): BOTH truncated and paraphrased. Judson writes
  "Then $ga =\lambda_g(a) = \lambda_g(b) = gb$. Hence, $a = b$."; we collapsed the chain to
  "Then $ga = gb$, hence $a = b$." He also opens "We must find a group of permutations
  $\overline{G}$ that is isomorphic to $G$" (dropped) and continues past our stopping point
  to define $\overline{G}$, show closure, and build the isomorphism (dropped).
- `aata/9.1` `leftTranslationIsInjective` is a one-line model transfer where Judson shows
  three steps — the one real Class-1 theorem defect.
- 16 narration sites listed in `AATA-fixes.md` OPEN ITEM 2.
