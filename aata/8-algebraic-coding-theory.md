# Algebraic Coding Theory — DEFERRED, placeholder

**Chapter 8 of Thomas W. Judson's *Abstract Algebra: Theory and Applications*
(source: `vendor/aata/src/algcodes.xml`; © 1997–2026 Judson, GFDL 1.3) is not
transliterated.** This file exists so the gap between §7.2 and §9.1 is visible rather
than silent — the corpus otherwise jumps from chapter 7 to chapter 9 with nothing saying
why.

There is no `2b4m` code here, so `check aata` reports it as 0 declarations, as it does
`§4.3`.

## Why it is deferred

**§8.2 Linear Codes, §8.3 Parity-Check and Generator Matrices, and §8.4 Efficient
Decoding need vectors and matrices**, which `std/` does not have.

Note what kind of obstacle that is (user, 2026-10-21): **in principle we COULD build
vectors and matrices — nothing in the language prevents it — but it is likely to be painful
enough that we should not.** A matrix over $\mathbb{Z}_2$ is an indexed family of indexed
families, and every operation on one (product, rank, row reduction) is a nested induction
over two bounds with no arithmetic shortcuts available. So this is a DELIBERATE
non-construction on cost grounds, not a language limit. Do not record it as impossible, and
do not start it opportunistically.

**§8.1 Error-Detecting and Correcting Codes is reachable but should wait for literals.**
Measured 2026-10-21: the section is 3,368 words containing 59 explicit binary strings, 3
tabulars and 2 figures, so most of it is numeric and out of scope by the numerics ruling.
What survives is three results:

| result | status |
|---|---|
| the probability of errors in exactly $k$ coordinates, $\binom{n}{k}q^kp^{n-k}$ | blocked — needs binomial coefficients AND probability |
| the 5-part Hamming-distance proposition (weight-as-distance, non-negativity, identity of indiscernibles, symmetry, triangle inequality) | reachable, but every part needs bit-counting scaffolding |
| $d_{\min} = 2n+1$ corrects $n$ errors and detects $2n$ | reachable and clean — his proof is pure triangle inequality |

The blocker on the middle row is that **Judson defines the Hamming distance as "the number
of bits in which $\mathbf{x}$ and $\mathbf{y}$ differ"** — a count over a tuple — and
`d_min` as a minimum over all distances between distinct codewords, i.e. a minimum over a
set of pairs. Counting is exactly where this corpus has paid repeatedly: §6.2 could not say
$|G|/|H| = [G:H]$ and went through listings, §6.3 could not say $|U(n)| = \varphi(n)$, and
§5.1's $|A_n| = n!/2$ needed a listing-splitting argument. Doing §8.1 now means building
that scaffolding a fourth time — and it is the scaffolding that numerals and list literals
are meant to make unnecessary.

**The plan (user, 2026-10-21): do as much AATA as possible WITHOUT literals, then build
them.** So §8.1 is not blocked on literals so much as deprioritised relative to chapters
that need no new machinery at all — it would cost a fourth hand-built counting layer for
one and a half theorems. When literals do land, a binary $n$-tuple becomes a literal rather
than an axiomatized sequence and "the number of bits where they differ" becomes a fold, so
the chapter is a natural consumer of that work — arguably its best test case, being entirely
fixed-width bit vectors.

See the `literal-declarations-design` and `list-literals-direction` notes for the design
(both recorded as discussion-only, numerals first).

## One thing worth knowing if this is picked up early

The $d_{\min}$ theorem is genuinely independent of all the counting — Judson's proof uses
only $d(\mathbf{x},\mathbf{z}) \leq d(\mathbf{x},\mathbf{y}) + d(\mathbf{y},\mathbf{z})$
and arithmetic on $n$, and `std/peano/order.b4m` already has every ordering fact it needs
(`lessOrEqualTransitive`, `lessOrEqualAntisymmetric`, `lessOrEqualIsGapExistential`,
`trichotomy`). It could land against an *axiomatized* distance function.

**Resist that.** A fixed symbol plus axioms characterising it is the
`fixed-symbol-sections-are-model-sources` trap — it was hit twice in chapter 6 — and it
would put an unproved distance function on the trust surface to buy one theorem.
