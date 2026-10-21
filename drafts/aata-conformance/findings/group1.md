# Transliteration fidelity audit — group 1

Files: aata/1.2.3-partitions.md, aata/1.2.3-relations.md,
aata/2.2-division-algorithm.md, aata/2.3-primes.md,
aata/4.3-repeated-squares.md, aata/6.2-lagranges-theorem.md

A note on the dominant pattern. In these six files the overwhelming defect is
NO-SOURCE narration placed in Judson's prose voice: paragraphs written by us,
in plain body text (not a `>` aside), that explain what the *formalization*
needs next ("Both halves rest on one arithmetic fact...", "Three ring facts
come first...", "The **peel step** shared by both uniqueness inductions...").
A reader cannot tell these from Judson's own sentences. Each is individually
useful — it introduces an imported std lemma — but each belongs in a `>` aside
under the sanctioned "declared divergence" rule, not in the transliterated
flow. I mark them NO-SOURCE and the fix is uniformly "wrap as a `>` aside"
unless noted.

Separately there are genuine TRUNCATION and PARAPHRASE defects where Judson's
actual words were dropped or rewritten. Those are the expensive ones and I list
them first in each file.

---

## aata/1.2.3-relations.md

### aata/1.2.3-relations.md:35  [TRUNCATED]
OURS:
> Given an equivalence relation $R$ on a set $X$, we usually write $x \sim y$
> instead of $(x, y) \in R$.

(paragraph ends here; next is blank, then `**Example.**`)

JUDSON:
> Given an equivalence relation R on a set X,
> we usually write x \sim y instead of (x, y) \in R.
> [DROPPED] If the equivalence relation already has an associated notation such
> as =, \equiv, or \cong, we will use that notation.

FIX: append his dropped sentence —
Given an equivalence relation $R$ on a set $X$, we usually write $x \sim y$
instead of $(x, y) \in R$. If the equivalence relation already has an associated
notation such as $=$, $\equiv$, or $\cong$, we will use that notation.

### aata/1.2.3-relations.md:63-67  [TRUNCATED]
OURS:
> ... by saying $A \sim B$ if there exists an invertible matrix $P$ such
> that $PAP^{-1} = B$. Let $I$ be the $2 \times 2$ identity matrix. Then
> $IAI^{-1} = IAI = A$; ...

JUDSON (between "$PAP^{-1} = B$." and "Then $IAI^{-1} = IAI = A$"):
> For example, if
>   A = \begin{pmatrix} 1 & 2 \\ -1 & 1 \end{pmatrix}
>   \quad \text{and} \quad
>   B = \begin{pmatrix} -18 & 33 \\ -11 & 20 \end{pmatrix}
> ,
> then A \sim B since PAP^{-1} = B for
>   P = \begin{pmatrix} 2 & 5 \\ 1 & 3 \end{pmatrix}
> .
> Let I be the 2 \times 2 identity matrix; that is,
>   I = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}
> .

FIX: restore both dropped pieces —
matrices, by saying $A \sim B$ if there exists an invertible matrix $P$ such
that $PAP^{-1} = B$. For example, if

$$A = \begin{pmatrix} 1 & 2 \\ -1 & 1 \end{pmatrix}
\quad \text{and} \quad
B = \begin{pmatrix} -18 & 33 \\ -11 & 20 \end{pmatrix},$$

then $A \sim B$ since $PAP^{-1} = B$ for

$$P = \begin{pmatrix} 2 & 5 \\ 1 & 3 \end{pmatrix}.$$

Let $I$ be the $2 \times 2$ identity matrix; that is,

$$I = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}.$$

Then $IAI^{-1} = IAI = A$; therefore, the relation is reflexive.

### aata/1.2.3-relations.md:86  [NO-SOURCE]
OURS:
> Directly from the definition, an equivalence relation *is* each of its three
> constituent properties.

JUDSON: none — no counterpart in the source. Judson states no such lemma; the
three theorems that follow (equivalenceIsReflexive/Symmetric/Transitive) are
projections out of our `and`-conjunction encoding of his three-bullet
definition, i.e. pure formalization plumbing.

FIX: wrap as a `>` aside, e.g.
> *Judson's three-bullet definition is encoded here as a single conjunction, so
> each bullet has to be projected back out before it can be cited.*

VERDICT for this file: the four Examples (37-79) are otherwise faithful
transliterations, including his $psu = qru = qst$ chain and his
$C = QBQ^{-1} = QPAP^{-1}Q^{-1} = (QP)A(QP)^{-1}$ display. The opening
definition (26-35) is verbatim. The two `>` asides (19-22, 81-84) are
legitimate language-limit declarations.

---

## aata/1.2.3-partitions.md

The spine of this file is FAITHFUL: lines 8-14 (partition / equivalence class
definition), 16-24 (mod-3 Example), 49-52 (Theorem statement), 54-56 and
278-283 (both halves of Judson's proof), 868-873 (the converse paragraph) are
transliterated essentially word-for-word.

### aata/1.2.3-partitions.md:463  [PARAPHRASED]
OURS:
> Clearly $X = \bigcup_{x \in X} [x]$, so the classes cover $X$; with the
> corollary above they therefore form a partition of $X$.

JUDSON (the one sentence of his this covers, between "...and so $[x]$ is
nonempty." and "Now let $x, y \in X$."):
> Clearly X = \bigcup_{x \in X} [x].

FIX: keep his sentence alone; move our clause to an aside —
Clearly $X = \bigcup_{x \in X} [x]$.

> *That covering, together with the corollary above, is what the three theorems
> below assemble into "the classes form a partition".*

### aata/1.2.3-partitions.md:605  [NO-SOURCE]
OURS:
> **The classes are pairwise disjoint.** Two distinct members $s, t$ of
> $\mathcal{P}$ are classes $s = [a]$ and $t = [b]$. By the corollary either
> $[a] = [b]$ — impossible, since that would make $s = t$ — or
> $[a] \cap [b] = \emptyset$, that is, $s \cap t = \emptyset$.

JUDSON: none — no counterpart. His "Therefore, any two equivalence classes are
either disjoint or exactly the same." is already transliterated at 282-283;
this paragraph re-reads that corollary against our pairwiseDisjoint(quotient)
encoding.

FIX: wrap as a `>` aside.

### aata/1.2.3-partitions.md:760  [NO-SOURCE]
OURS:
> **The classes form a partition.** A partition is a covering, pairwise disjoint
> collection none of whose members is empty. The first two are what was just
> proved, and no class is empty because $[a]$ always contains $a$.

JUDSON: none — no counterpart. Judson never unpacks his own "form a partition"
against his definition; he takes it as read. Ours is the isPartition assembly.

FIX: wrap as a `>` aside.

### Also (not flagged, same class) — :101, :480, :498, :1026  [NO-SOURCE x4]
- :101 "Next, two elements are equivalent exactly when their classes
  coincide. ..." — our standalone iff lemma; Judson has this only INSIDE his
  corollary proof.
- :480 "Write $\mathcal{P}$ for the collection $\{[x] : x \in X\}$ ..." — our
  encoding note.
- :498 "**The classes cover $X$.** Every element $z$ lies in its own class
  ..." — our expansion of his one-sentence "Clearly $X = \bigcup [x]$".
- :1026 "For transitivity the blocks must be pairwise disjoint: ..." — our
  expansion of his one-sentence "then $x$ must be in the same partition as $z$".
JUDSON: none for any of the four.
FIX: wrap each as a `>` aside.

---

## aata/2.2-division-algorithm.md

Transliterated spine is good: 8-9, 78-80 (Theorem), 82-85 (the
"existence-and-uniqueness" opening), 118-125 (Uniqueness) are verbatim Judson.

### aata/2.2-division-algorithm.md:456  [TRUNCATED]
OURS:
> We must first show that $S$ is nonempty. If $a > 0$, then $a - b\cdot 0 \in S$.

JUDSON (his Existence paragraph opens with two sentences we dropped, right after
the display defining $S$):
> If 0 \in S, then b divides a, and we can let q = a/b and r = 0.
> If 0 \notin S, we can use the Well-Ordering Principle.
> We must first show that S is nonempty.
> If a \gt 0, then a - b \cdot 0 \in S.

FIX: insert his two sentences ahead of ours —
If $0 \in S$, then $b$ divides $a$, and we can let $q = a/b$ and $r = 0$. If
$0 \notin S$, we can use the Well-Ordering Principle. We must first show that
$S$ is nonempty. If $a > 0$, then $a - b\cdot 0 \in S$.

### aata/2.2-division-algorithm.md:457-467  [PARAPHRASED] (two edits, one paragraph)
OURS:
> If $a < 0$, then $a - b(2a) = a(1 - 2b) \in S$ — a product of two nonpositive
> factors, since $a < 0$ and $1 - 2b < 0$ because $b > 0$ forces $2b \ge 2 > 1$.
> ...
> smallest member of $S$. So $r \le b$; and $r \ne b$, so $r < b$.

JUDSON:
> If a \lt 0, then a - b(2a) = a(1 - 2b) \in S.
> ...
> which would contradict the fact that r = a - bq is the smallest member of S.
> So r \leq b.
> Since 0 \notin S, r \neq b and so r \lt b.

(1) we ADDED a justification Judson does not give ("a product of two nonpositive
factors, since..."); (2) we DROPPED his reason for $r \ne b$ ("Since
$0 \notin S$") — which is the payoff of the "If $0 \notin S$" sentence truncated
above.

FIX:
If $a < 0$, then $a - b(2a) = a(1 - 2b) \in S$.
...and...
smallest member of $S$. So $r \le b$. Since $0 \notin S$, $r \neq b$ and so
$r < b$.
(our added justification, if wanted, moves to a `>` aside).

### aata/2.2-division-algorithm.md:87  [NO-SOURCE]
OURS:
> Both halves rest on one arithmetic fact: a product of nonnegatives is
> nonnegative. It follows by induction on the second factor — $b\cdot 0 = 0$, and
> $b\cdot(k+1) = b\cdot k + b$ is a sum of nonnegatives.
JUDSON: none — no counterpart. Introduces the imported
productOfNonnegativesIsNonneg.
FIX: wrap as a `>` aside.

### aata/2.2-division-algorithm.md:95  [NO-SOURCE]
OURS:
> Next, a nonnegative multiple of $b$ that lies strictly below $b$ must be zero —
> this is what makes "$b \mid (r' - r)$ and $0 \le r' - r < b$ possible only if
> $r' - r = 0$." Writing the multiple as $m = bk$, split on the sign of $k$. ...
JUDSON: none. The quoted fragment inside it is his (already transliterated
correctly at 123-124), but the paragraph around it is entirely ours — it proves
a step Judson asserts in passing.
FIX: wrap as a `>` aside.

### aata/2.2-division-algorithm.md:107  [NO-SOURCE]
OURS:
> Finally, at the very end of uniqueness, $b > 0$ cancels: from $bq = bq'$ one
> reads off $q = q'$. Behind that cancellation is the fact that a positive times a
> positive is positive, so a positive times a factor that is *not* zero cannot be
> zero — hence $bz = 0$ with $b > 0$ forces $z = 0$.
JUDSON: none — Judson writes only "Hence, $r = r'$ and $q = q'$."
FIX: wrap as a `>` aside.

### aata/2.2-division-algorithm.md:127  [NO-SOURCE / NARRATION]
OURS:
> The remainders agree first: trichotomy on $r_1$ versus $r_2$ makes each strict
> case a bounded multiple of $b$, which the lemma above forbids. Then substituting
> $r_2 = r_1$ and cancelling the common remainder gives $bq_1 = bq_2$, that is,
> $b(q_1 - q_2) = 0$, so $q_1 = q_2$ because a positive $b$ cannot annihilate.
JUDSON: none — a second, different proof of the uniqueness he already proved
(and which we already transliterated at 122-125), narrating our formalization's
shape ("trichotomy... the lemma above").
FIX: wrap as a `>` aside.

### aata/2.2-division-algorithm.md:1024  [NO-SOURCE]
OURS:
> Together these two halves are the Division Algorithm: for every $a$ and every
> $b > 0$ there are integers $q$ and $r$ with $a = bq + r$ and $0 \le r < b$, and
> they are unique.
JUDSON: none. Our closing summary (his theorem statement already appears at
78-80).
FIX: wrap as a `>` aside, or delete as redundant.

---

## aata/2.3-primes.md

This is the worst file in the group. Four of Judson's five §2.2 proofs are NOT
TRANSLITERATED AT ALL — replaced with our own different proofs or with
narration about our formalization. Plus 30 scaffolding paragraphs in his voice.

### aata/2.3-primes.md:12  [TRUNCATED]
OURS (paragraph ends):
> and if $d'$ is any other common divisor of $a$ and $b$, then $d' \mid d$.

JUDSON (continues):
> We write d = \gcd(a, b);
> for example, \gcd( 24, 36) = 12 and \gcd(120, 102) = 6.
> We say that two integers a and b are relatively prime if \gcd( a, b ) = 1.

The third sentence matters: "relatively prime" is the hypothesis of the Coprime
Corollary we state at line 953, and it is never defined in our file.

FIX: append —
We write $d = \gcd(a, b)$; for example, $\gcd(24, 36) = 12$ and
$\gcd(120, 102) = 6$. We say that two integers $a$ and $b$ are **relatively
prime** if $\gcd(a, b) = 1$.

### aata/2.3-primes.md:533-542  [PARAPHRASED + TRUNCATED]
OURS:
> **Proof.** Let $S = \{am + bn : am + bn > 0\}$. $S$ is nonempty, and every
> member is positive hence nonnegative, so by the Principle of Well-Ordering $S$
> has a least member $d = ar + bs$. We claim that $d = \gcd(a, b)$. Running the
> Division Algorithm on $a$ by $d$ gives $a = dq + r'$ with $0 \le r' < d$. Were
> $r' > 0$, the identity $r' = a(1 - rq) + b(-sq)$ would make $r'$ a member of $S$
> smaller than $d$, contradicting minimality; so $r' = 0$ and $d \mid a$.
> Symmetrically $d \mid b$. Finally any common divisor $e$ of $a$ and $b$ divides
> $ar + bs = d$, so $d$ is the greatest. Uniqueness follows: any two integers
> divisible by every common divisor divide each other, and being positive are
> equal.

JUDSON (both paragraphs, verbatim):
> Let
>   S = \{ am + bn : m, n \in {\mathbb Z} \text{ and } am + bn \gt 0 \}
> .
> Clearly, the set S is nonempty;
> hence, by the Well-Ordering Principle S must have a smallest member,
> say d = ar + bs.
> We claim that d = \gcd( a, b).
> Write a = dq + r' where 0 \leq r' \lt d.
> If r' \gt 0, then
>   r' & = a - dq
>      & = a - (ar + bs)q
>      & = a - arq - bsq
>      & = a( 1 - rq ) + b( -sq )
> ,
> which is in S.
> But this would contradict the fact that d is the smallest member of S.
> Hence, r' = 0 and d divides a.
> A similar argument shows that d divides b.
> Therefore, d is a common divisor of a and b.
>
> Suppose that d' is another common divisor of a and b,
> and we want to show that d' \mid d.
> If we let a = d'h and b = d'k, then
>   d = ar + bs = d'hr + d'ks = d'(hr + ks)
> .
> So d' must divide d.
> Hence, d must be the unique greatest common divisor of a and b.

Our last two sentences REPLACE his entire second paragraph, including the
$d = d'hr + d'ks = d'(hr+ks)$ computation. His four-line display of $r'$ is
collapsed to a bare "the identity".

FIX (paste his two paragraphs):
**Proof.** Let

$$S = \{\, am + bn : m, n \in \mathbb{Z} \text{ and } am + bn > 0 \,\}.$$

Clearly, the set $S$ is nonempty; hence, by the Well-Ordering Principle $S$ must
have a smallest member, say $d = ar + bs$. We claim that $d = \gcd(a, b)$. Write
$a = dq + r'$ where $0 \le r' < d$. If $r' > 0$, then

$$\begin{aligned}
r' &= a - dq \\
   &= a - (ar + bs)q \\
   &= a - arq - bsq \\
   &= a(1 - rq) + b(-sq),
\end{aligned}$$

which is in $S$. But this would contradict the fact that $d$ is the smallest
member of $S$. Hence, $r' = 0$ and $d$ divides $a$. A similar argument shows that
$d$ divides $b$. Therefore, $d$ is a common divisor of $a$ and $b$.

Suppose that $d'$ is another common divisor of $a$ and $b$, and we want to show
that $d' \mid d$. If we let $a = d'h$ and $b = d'k$, then

$$d = ar + bs = d'hr + d'ks = d'(hr + ks).$$

So $d'$ must divide $d$. Hence, $d$ must be the unique greatest common divisor of
$a$ and $b$.

### aata/2.3-primes.md:956-959  [NO-SOURCE]
OURS:
> **Proof.** If $a$ and $b$ are relatively prime — every common divisor is $\pm 1$
> — then the positive common divisor $d = \gcd(a, b)$ must itself be $1$ or $-1$.
> It is positive, and $-1$ is not, so $d = 1$ and Bézout's identity
> $d = ar + bs$ becomes $ar + bs = 1$.

JUDSON: none — JUDSON GIVES THIS COROLLARY NO PROOF AT ALL. He states it and
moves on ("Let $a$ and $b$ be two integers that are relatively prime. Then there
exist integers $r$ and $s$ such that $ar + bs = 1$.") followed immediately by the
Euclidean Algorithm section.

FIX: wrap as a `>` aside —
> *Judson states this corollary without proof. Since there is no $\gcd$ function
> here, the step from "relatively prime" to $d = 1$ has to be made explicit: the
> positive common divisor $d$ must itself be $1$ or $-1$, and $-1$ is not
> positive, so $d = 1$ and Bézout's $d = ar + bs$ becomes $ar + bs = 1$.*

### aata/2.3-primes.md:1812-1819  [NARRATION + TRUNCATED]
OURS:
> **Euclid's Lemma.** Suppose the prime $p$ divides $ab$. If $p \mid a$ we are
> done; otherwise $p \nmid a$, so $a$ and $p$ are relatively prime and the coprime
> corollary yields $r$, $s$ with $ar + ps = 1$. Multiplying by $b$,
> $$b = b\cdot 1 = b(ar + ps) = (ab)r + p(bs).$$
> Now $p \mid (ab)r$ because $p \mid ab$, and $p \mid p(bs)$ because $p \mid p$;
> so their sum, which is $b$, is divisible by $p$. Hence $p \mid b$.

JUDSON — STATEMENT (we never state it; we only bold the name):
> Let a and b be integers and p be a prime number.
> If p \mid ab, then either p \mid a or p \mid b.

JUDSON — PROOF:
> Suppose that p does not divide a.
> We must show that p \mid b.
> Since \gcd( a, p ) = 1,
> there exist integers r and s such that ar + ps = 1.
> So
>   b = b(ar + ps) = (ab)r + p(bs)
> .
> Since p divides both ab and itself,
> p must divide b = (ab)r + p(bs).

FIX: restore both —
> **Lemma (Euclid).** Let $a$ and $b$ be integers and $p$ be a prime number. If
> $p \mid ab$, then either $p \mid a$ or $p \mid b$.

**Proof.** Suppose that $p$ does not divide $a$. We must show that $p \mid b$.
Since $\gcd(a, p) = 1$, there exist integers $r$ and $s$ such that $ar + ps = 1$.
So

$$b = b(ar + ps) = (ab)r + p(bs).$$

Since $p$ divides both $ab$ and itself, $p$ must divide $b = (ab)r + p(bs)$.
$\blacksquare$

### aata/2.3-primes.md:2422-2427  [PARAPHRASED + TRUNCATED]
OURS:
> **Proof.** Were there only finitely many primes $p_1, \ldots, p_n$, the number
> $P = p_1 p_2 \cdots p_n + 1$ has a prime factor $p$, since every integer greater
> than $1$ does, and by completeness $p$ is one of the $p_i$. Then $p$ divides the
> product $p_1 \cdots p_n$, and $p$ divides $P$, so $p$ divides
> $P - p_1 \cdots p_n = 1$ — forcing $p \le 1$, contradicting $p > 1$. No finite
> list can hold every prime.

JUDSON — STATEMENT (missing from our file entirely):
> There exist an infinite number of primes.

JUDSON — PROOF:
> We will prove this theorem by contradiction.
> Suppose that there are only a finite number of primes,
> say p_1, p_2, \ldots, p_n.
> Let P = p_1 p_2 \cdots p_n + 1.
> Then P must be divisible by some p_i for 1 \leq i \leq n.
> In this case, p_i must divide P - p_1 p_2 \cdots p_n = 1, which is a contradiction.
> Hence, either P is prime or there exists an additional prime number
> p \neq p_i that divides P.

Note his conclusion is a DISJUNCTION ("either $P$ is prime or there exists an
additional prime $p \neq p_i$"); ours is "No finite list can hold every prime."

FIX:
> **Theorem (Euclid).** There exist an infinite number of primes.

**Proof.** We will prove this theorem by contradiction. Suppose that there are
only a finite number of primes, say $p_1, p_2, \ldots, p_n$. Let
$P = p_1 p_2 \cdots p_n + 1$. Then $P$ must be divisible by some $p_i$ for
$1 \le i \le n$. In this case, $p_i$ must divide $P - p_1 p_2 \cdots p_n = 1$,
which is a contradiction. Hence, either $P$ is prime or there exists an
additional prime number $p \neq p_i$ that divides $P$. $\blacksquare$

### aata/2.3-primes.md:2429  [NO-SOURCE]
OURS:
> The step $P > 1$ reads $P = p_1 \cdots p_n + 1 > p_1 \cdots p_n \ge 1$.
JUDSON: none.
FIX: fold into the `>` aside already at 2431-2435.

### aata/2.3-primes.md:2675-2683  [NO-SOURCE — our proof replaces his]
OURS:
> **Proof.** Every integer $n > 1$ is a product of primes, by strong induction on
> $n$. A prime factor $p$ splits off, leaving a cofactor $c$ with $n = pc$; the
> cofactor is positive, so either $c = 1$ — and then $n = p$ is itself prime,
> factored by the singleton $[p]$ — or $c > 1$, and then $c < n$, so the induction
> hypothesis factors $c$, and $p$ is prepended to that factorization. Three
> order facts come first.

JUDSON — his Existence proof, which is NOT a strong induction but a
Well-Ordering contradiction, and does not appear in our file at all:
> To show existence,
> suppose that there is some integer that cannot be written as the product of primes.
> Let S be the set of all such numbers.
> By the Principle of Well-Ordering, S has a smallest number, say a.
> If the only positive factors of a are a and 1,
> then a is prime, which is a contradiction.
> Hence, a = a_1 a_2 where 1 \lt a_1 \lt a and 1 \lt a_2 \lt a.
> Neither a_1 \in S nor a_2 \in S, since a is the smallest element in S.
> So
>   a_1 & = p_1 \cdots p_r
>   a_2 & = q_1 \cdots q_s
> .
> Therefore,
>   a = a_1 a_2 = p_1 \cdots p_r q_1 \cdots q_s
> .
> So a \notin S, which is a contradiction.

FIX: transliterate his proof as the **Proof.**, demote ours to a declared
divergence aside:
**Proof.** To show existence, suppose that there is some integer that cannot be
written as the product of primes. Let $S$ be the set of all such numbers. By the
Principle of Well-Ordering, $S$ has a smallest number, say $a$. If the only
positive factors of $a$ are $a$ and $1$, then $a$ is prime, which is a
contradiction. Hence, $a = a_1 a_2$ where $1 < a_1 < a$ and $1 < a_2 < a$.
Neither $a_1 \in S$ nor $a_2 \in S$, since $a$ is the smallest element in $S$.
So

$$\begin{aligned}
a_1 &= p_1 \cdots p_r \\
a_2 &= q_1 \cdots q_s.
\end{aligned}$$

Therefore,

$$a = a_1 a_2 = p_1 \cdots p_r q_1 \cdots q_s.$$

So $a \notin S$, which is a contradiction. $\blacksquare$

> *Judson argues by Well-Ordering on the set of non-factorable integers. There is
> no set-of-integers sort here, so the formalization below runs the contrapositive
> as a strong induction on $n$ instead: a prime factor $p$ splits off, leaving a
> positive cofactor $c$ with $n = pc$; either $c = 1$, and $n = p$ is factored by
> the singleton $[p]$, or $c > 1$ and $c < n$, so the induction hypothesis factors
> $c$ and $p$ is prepended.*

### aata/2.3-primes.md:6334-6355  [NARRATION — his proof is absent]
OURS:
> If $n = q_1 \cdots q_l$ is a second factorization into primes, then $k = l$ and
> the $q_i$ are, after reordering, the $p_i$.
>
> The core is that every prime in one factorization appears in the other: given two
> prime factorizations of the same product, of lengths $k$ and $l$, each entry of
> the first is prime and divides the common product, so it divides some entry of
> the second; and a prime dividing a prime equals it. ...
>
> That is strengthened two ways, both by induction on $k$ that peels the last
> factor, ... [bullets] ...
>
> The map $\sigma$ is the "after reordering." Together with $k = l$ it says the two
> factorizations are the same primes with the same multiplicities.

JUDSON — his Uniqueness proof, ABSENT from our file:
> To show uniqueness we will use induction on n.
> The theorem is certainly true for n = 2 since in this case n is prime.
> Now assume that the result holds for all integers m such that 1 \leq m \lt n, and
>   n = p_1 p_2 \cdots p_k = q_1 q_2 \cdots q_l
> ,
> where p_1 \leq p_2 \leq \cdots \leq p_k and q_1 \leq q_2 \leq \cdots \leq q_l.
> By Euclid's Lemma, p_1 \mid q_i for some i = 1, \ldots, l and q_1 \mid p_j for
> some j = 1, \ldots, k.
> Since all of the p_i's and q_i's are prime, p_1 = q_i and q_1 = p_j.
> Hence, p_1 = q_1 since p_1 \leq p_j = q_1 \leq q_i = p_1.
> By the induction hypothesis,
>   n' = p_2 \cdots p_k = q_2 \cdots q_l
> has a unique factorization.
> Hence, k = l and q_i = p_i for i = 1, \ldots, k.

FIX: transliterate his proof as the **Proof.** of the Uniqueness section, and
demote our three-paragraph description of the formal development to a `>` aside:
**Proof.** To show uniqueness we will use induction on $n$. The theorem is
certainly true for $n = 2$ since in this case $n$ is prime. Now assume that the
result holds for all integers $m$ such that $1 \le m < n$, and

$$n = p_1 p_2 \cdots p_k = q_1 q_2 \cdots q_l,$$

where $p_1 \le p_2 \le \cdots \le p_k$ and $q_1 \le q_2 \le \cdots \le q_l$. By
Euclid's Lemma, $p_1 \mid q_i$ for some $i = 1, \ldots, l$ and $q_1 \mid p_j$ for
some $j = 1, \ldots, k$. Since all of the $p_i$'s and $q_i$'s are prime,
$p_1 = q_i$ and $q_1 = p_j$. Hence, $p_1 = q_1$ since
$p_1 \le p_j = q_1 \le q_i = p_1$. By the induction hypothesis,

$$n' = p_2 \cdots p_k = q_2 \cdots q_l$$

has a unique factorization. Hence, $k = l$ and $q_i = p_i$ for
$i = 1, \ldots, k$. $\blacksquare$

> *Judson's induction is on $n$ and relies on both factorizations being sorted
> ascending, so that $p_1 = q_1$ falls out of $p_1 \le p_j = q_1 \le q_i = p_1$.
> There is no sorting here, so the development below instead inducts on the
> length $k$, peeling the LAST factor and deleting its match from the second
> factorization; "after reordering" becomes an explicit injective index map
> $\sigma$ with $p_i = q_{\sigma(i)}$.*

### aata/2.3-primes.md:2654  [TRUNCATED]
OURS (paragraph ends):
> To find $r$ and $s$ such that $ar + bs = d$, we begin with this last equation and
> substitute results obtained from the previous equations.

JUDSON (continues with a display and the naming sentence):
> ... substitute results obtained from the previous equations:
>   d & = r_n
>     & = r_{n - 2} - r_{n - 1} q_n
>     & = r_{n - 2} - q_n( r_{n - 3} - q_{n - 1} r_{n - 2} )
>     & = -q_n r_{n - 3} + ( 1+ q_n q_{n-1} ) r_{n - 2}
>     & \vdots
>     & = ra + sb
> .
> The algorithm that we have just used to find the greatest common divisor d of
> two integers a and b and to write d as the linear combination of a and b is
> known as the Euclidean algorithm.

The dropped sentence is the one that actually NAMES the Euclidean algorithm —
the section's own title.

FIX: append —
substitute results obtained from the previous equations:

$$\begin{aligned}
d &= r_n \\
  &= r_{n-2} - r_{n-1} q_n \\
  &= r_{n-2} - q_n(r_{n-3} - q_{n-1} r_{n-2}) \\
  &= -q_n r_{n-3} + (1 + q_n q_{n-1}) r_{n-2} \\
  &\;\;\vdots \\
  &= ra + sb.
\end{aligned}$$

The algorithm that we have just used to find the greatest common divisor $d$ of
two integers $a$ and $b$ and to write $d$ as the linear combination of $a$ and
$b$ is known as the **Euclidean algorithm**.

### aata/2.3-primes.md — NO-SOURCE scaffolding in Judson's voice (one block, 30 items)
Each of the following is our commentary on the formalization, in plain body text,
with no counterpart anywhere in integers.xml. Verdict NO-SOURCE for all; FIX for
all is WRAP AS A `>` ASIDE. They are legitimately needed (each introduces an
imported std lemma or describes an induction our encoding forces), but must not
read as Judson.

  :149  "A positive integer is in particular nonnegative. From $0 < x$ ..."
  :157  "The Bezout argument will, at its crux, learn of a remainder $r'$ ..."
  :239  "The nonemptiness argument splits on the sign of $a$ ..."
  :250  "Two more facts the next proof needs: the additive left-swap ..."
  :306  "The heart of the argument that $d = ar + bs$ divides $a$ runs the Division Algorithm ..."
  :312  "From $a = dq + r'$ we recover $r' = a - dq$ by cancelling $dq$ ..."
  :413  "The coprime corollary will produce a positive common divisor $d$ ..."
  :421  "Before invoking Well-Ordering we must exhibit *some* positive member ..."
  :1253 "Euclid's Lemma needs to collapse $b(ar+ps)$ ... Three ring facts come first"
  :1287 "The left-swap forms $a(bc) = b(ac)$ and $a+(b+c) = b+(a+c)$ reassociate ..."
  :1335 "The additive left-swap is the identical argument on addition ..."
  :1338 "A small positivity fact used repeatedly: $0 < 1$ ..."
  :1345 "$-e$ divides whatever $e$ divides: from $n = ek$ ..."
  :1405 "A negative integer negates to a positive one ..."
  :1412 "Euclid's Lemma proceeds by cases on whether $p \mid a$, so divisibility ... decidable."
  :1591 "The bridge from primality to Bezout's coprimality hypothesis ..."
  :2022 "Euclid's Lemma lifts by induction on the length $k$ to a whole finite product ..."
  :2670 "A **prime factorization** of $n$ is a finite sequence of length $k$ ..."
  :2682 "A nonnegative index strictly below $1$ must be $0$ ..."
  :2749 "$p > 1$ and $c > 0$ force $c < pc$ ..."
  :2866 "The cofactor of a positive number by a positive factor is itself positive ..."
  :3015 "Now the existence half itself, by strong induction on $n$ ..."
  :3752 "Two prime factorizations of the *same* product have the same length. ..."
  :3756 "Second, strict order is preserved by the successor on both sides ..."
  :3925 "The **peel step** shared by both uniqueness inductions. ..."
  :4403 "The length statement itself, by induction on the length $k$ ..."
  :4807 "The injectivity of the index map needs one small arithmetic fact ..."
  :4853 "Two facts about the reindexing map $c \mapsto c$ for $c < m$ ..."
  :4922 "Second, when a value $b$ lies at or above the threshold $a$ ..."
  :4965 "The reordering itself, by induction on the length $k$, building the index map $\sigma$ ..."
  :6587 "The capstone conjoins the two: equal length and an explicit matching bijection."

(Two of these — the paragraphs just above the existing asides at :1420 and
:2431 — should be folded into those asides rather than given new ones.)

FAITHFUL in this file, do NOT touch: 8-12 (definitions, apart from the
truncation noted at :12), 529-531 (Bezout statement), 953-954 (Coprime
Corollary statement), 1113-1115 (prime/composite definition), 2616-2654 (the
Euclidean Algorithm section and the 945/2415 worked example — verbatim,
including "Notice that $r$ and $s$ are not unique, since $r = 41$ and
$s = -16$ would also work."), 2664-2668 (FTA statement), 6685-6698 (Historical
Note — verbatim).

---

## aata/4.3-repeated-squares.md

### aata/4.3-repeated-squares.md:12-17  [TRUNCATED]
OURS:
> Computing large powers can be very time-consuming. If we want to compute
> something like
> $$2^{37{,}398{,}332} \pmod{46{,}389},$$
> the result is a number between $0$ and $46{,}388$ that we could easily write
> down — but a naive computation is infeasible. To compute powers modulo $n$
> quickly we use the binary expansion of the exponent.

JUDSON:
> Computing large powers can be very time-consuming.
> [DROPPED] Just as anyone can compute 2^2 or 2^8, everyone knows how to compute
>   2^{2^{1{,}000{,}000} }
> .
> However, such numbers are so large that we do not want to attempt the
> calculations; moreover, past a certain point the computations would not be
> feasible even if we had every computer in the world at our disposal.
> Even writing down the decimal representation of a very large number may not be
> reasonable. It could be thousands or even millions of digits long.
> However, [END DROP] if we could compute something like
>   2^{37{,}398{,}332 } \pmod{ 46{,}389}
> ,
> we could very easily write the result down since it would be a number between
> 0 and 46{,}388.
> [DROPPED] If we want to compute powers modulo n quickly and efficiently, we will
> have to be clever.

Three losses: the whole $2^{2^{1{,}000{,}000}}$ motivation, both framing
sentences, and our "the result is a number ... but a naive computation is
infeasible" is a rewrite of his "we could very easily write the result down
since it would be a number between $0$ and $46{,}388$."

FIX:
Computing large powers can be very time-consuming. Just as anyone can compute
$2^2$ or $2^8$, everyone knows how to compute
$$2^{2^{1{,}000{,}000}}.$$
However, such numbers are so large that we do not want to attempt the
calculations; moreover, past a certain point the computations would not be
feasible even if we had every computer in the world at our disposal. Even
writing down the decimal representation of a very large number may not be
reasonable. It could be thousands or even millions of digits long. However, if
we could compute something like
$$2^{37{,}398{,}332} \pmod{46{,}389},$$
we could very easily write the result down since it would be a number between
$0$ and $46{,}388$. If we want to compute powers modulo $n$ quickly and
efficiently, we will have to be clever.

### aata/4.3-repeated-squares.md:19-22  [PARAPHRASED]
OURS:
> Any number $a$ can be written as a sum of distinct powers of $2$: ... its binary
> representation.

JUDSON:
> The first thing to notice is that any number a can be written as the sum of
> distinct powers of 2; that is, we can write
>   a = 2^{k_1} + 2^{k_2} + \cdots + 2^{k_n}
> ,
> where k_1 \lt k_2 \lt \cdots \lt k_n.
> This is just the binary representation of a.

FIX:
The first thing to notice is that any number $a$ can be written as the sum of
distinct powers of $2$; that is, we can write
$$a = 2^{k_1} + 2^{k_2} + \cdots + 2^{k_n}, \quad k_1 < k_2 < \cdots < k_n.$$
This is just the binary representation of $a$. For example, the binary
representation of $57$ is $111001$, since we can write
$57 = 2^0 + 2^3 + 2^4 + 2^5$.

(We also renamed his index bound $k_n$ to $k_r$. That is a notation change,
covered by the transcription exception — not a defect on its own.)

### aata/4.3-repeated-squares.md:31-39  [NO-SOURCE lead-in + TRUNCATED example]
OURS:
> To compute $a^m \pmod n$, expand $m$ in binary and multiply together the
> $a^{2^{k_i}}$ for the bits $k_i$ that are set. For example, computing $271^{321}
> \pmod{481}$: since $321 = 2^0 + 2^6 + 2^8$,
> $$271^{321} \equiv 271^{2^0} \cdot 271^{2^6} \cdot 271^{2^8} \pmod{481}.$$
> Repeated squaring gives $271^{2^1} \equiv 329$, $271^{2^2} \equiv 16$, and,
> continuing, $271^{2^6} \equiv 419$ and $271^{2^8} \equiv 16 \pmod{481}$;
> therefore
> $$271^{321} \equiv 271 \cdot 419 \cdot 16 \equiv 1{,}816{,}784 \equiv 47
> \pmod{481}.$$

JUDSON — our opening sentence has NO counterpart (it is our summary of the
method); and his worked example is compressed, losing the $271^{2^2}$
derivation chain and the $(a^{2^n})^2 \equiv a^{2^{n+1}}$ remark:
> We will compute 271^{321} \pmod{ 481}.
> Notice that
>   321 = 2^0 +2^6 + 2^8;
> hence, computing 271^{ 321} \pmod{ 481} is the same as computing
>   271^{ 2^0 +2^6 + 2^8 } \equiv 271^{ 2^0 } \cdot 271^{2^6 } \cdot 271^{ 2^8 } \pmod{ 481}
> .
> So it will suffice to compute 271^{ 2^i } \pmod{ 481} where i = 0, 6, 8.
> It is very easy to see that
>   271^{ 2^1}  = 73{,}441 \equiv 329 \pmod{ 481}
> .
> We can square this result to obtain a value for 271^{ 2^2} \pmod{481}:
>   271^{ 2^2}  & \equiv (271^{ 2^1})^2 \pmod{ 481}
>               & \equiv (329)^2 \pmod{481}
>               & \equiv 108{,}241 \pmod{481}
>               & \equiv 16 \pmod{481}
> .
> We are using the fact that (a^{2^n})^2  \equiv a^{2 \cdot 2^n} \equiv a^{ 2^{n+1} } \pmod{ n}.
> Continuing, we can calculate
>   271^{ 2^6 } \equiv 419 \pmod{481}
> and
>   271^{ 2^8 }  \equiv 16 \pmod{481}
> .
> Therefore,
>   271^{ 321} & \equiv 271^{ 2^0 +2^6 + 2^8 } \pmod{481}
>              & \equiv 271^{ 2^0 } \cdot 271^{ 2^6 } \cdot 271^{ 2^8 } \pmod{481}
>              & \equiv 271 \cdot 419 \cdot 16 \pmod{ 481}
>              & \equiv 1{,}816{,}784 \pmod{ 481}
>              & \equiv 47 \pmod{ 481}
> .

FIX: drop our lead-in sentence and paste his example as an **Example.** —
**Example.** We will compute $271^{321} \pmod{481}$. Notice that
$$321 = 2^0 + 2^6 + 2^8;$$
hence, computing $271^{321} \pmod{481}$ is the same as computing
$$271^{2^0 + 2^6 + 2^8} \equiv 271^{2^0} \cdot 271^{2^6} \cdot 271^{2^8}
\pmod{481}.$$
So it will suffice to compute $271^{2^i} \pmod{481}$ where $i = 0, 6, 8$. It is
very easy to see that
$$271^{2^1} = 73{,}441 \equiv 329 \pmod{481}.$$
We can square this result to obtain a value for $271^{2^2} \pmod{481}$:
$$\begin{aligned}
271^{2^2} &\equiv (271^{2^1})^2 \pmod{481} \\
          &\equiv (329)^2 \pmod{481} \\
          &\equiv 108{,}241 \pmod{481} \\
          &\equiv 16 \pmod{481}.
\end{aligned}$$
We are using the fact that
$(a^{2^n})^2 \equiv a^{2 \cdot 2^n} \equiv a^{2^{n+1}} \pmod{n}$. Continuing, we
can calculate
$$271^{2^6} \equiv 419 \pmod{481}$$
and
$$271^{2^8} \equiv 16 \pmod{481}.$$
Therefore,
$$\begin{aligned}
271^{321} &\equiv 271^{2^0 + 2^6 + 2^8} \pmod{481} \\
          &\equiv 271^{2^0} \cdot 271^{2^6} \cdot 271^{2^8} \pmod{481} \\
          &\equiv 271 \cdot 419 \cdot 16 \pmod{481} \\
          &\equiv 1{,}816{,}784 \pmod{481} \\
          &\equiv 47 \pmod{481}.
\end{aligned}$$

### aata/4.3-repeated-squares.md:41-43  [PARAPHRASED]
OURS:
> The method of repeated squares is essential for RSA cryptography (a later
> chapter), where encoding and decoding require quickly computing large powers of
> integers mod $n$.

JUDSON:
> The method of repeated squares will prove to be a very useful tool when we
> explore RSA cryptography in [Chapter 7].
> To encode and decode messages in a reasonable manner under this scheme,
> it is necessary to be able to quickly compute large powers of integers mod n.

FIX:
The method of repeated squares will prove to be a very useful tool when we
explore RSA cryptography in Chapter 7. To encode and decode messages in a
reasonable manner under this scheme, it is necessary to be able to quickly
compute large powers of integers mod $n$.

Note on the closing `## Why there is no formal content here` block (45-55): that
is a declared divergence and is legitimate — leave it, though the `>`-aside
convention would suit it better than a bare code fence. Also faithful and NOT a
defect: 24-29 (the laws-of-exponents paragraph) is a clean transliteration, and
the Sage section is correctly omitted.

---

## aata/6.2-lagranges-theorem.md

The theorem/corollary statements and all four of Judson's proofs that he actually
writes out (Lemma 6.8, Thm 6.9, Cor 6.11, Cor 6.12) are FAITHFULLY
TRANSLITERATED — lines 80-89, 315-320, 656-657, 761-766, 927-933 need nothing.

### aata/6.2-lagranges-theorem.md:1010-1019  [NARRATION + TRUNCATED]
OURS:
> **The converse of Lagrange's Theorem is false.** A divisor of $|G|$ need not be the
> order of any subgroup: $A_4$ has order 12 but no subgroup of order 6. Judson's
> argument: since $[A_4 : H] = 2$, the left and right cosets coincide, so
> $gHg^{-1} = H$ for every $g \in A_4$; and since $A_4$ contains eight $3$-cycles, at
> least one — say $(1\,2\,3)$ — lies in $H$, along with its inverse $(1\,3\,2)$.
> Conjugating, $(1\,2\,4)(1\,2\,3)(1\,2\,4)^{-1} = (2\,4\,3)$ and
> $(2\,4\,3)(1\,2\,3)(2\,4\,3)^{-1} = (1\,4\,2)$ are in $H$ too, with their inverses,
> so $H$ has at least the seven elements $(1)$, $(1\,2\,3)$, $(1\,3\,2)$, $(2\,4\,3)$,
> $(2\,3\,4)$, $(1\,4\,2)$, $(1\,2\,4)$ — more than six. That argument is recorded
> here as prose.

JUDSON — the section's lead-in paragraph (ENTIRELY ABSENT from our file):
> The group A_4 has order 12;
> however, it can be shown that it does not possess a subgroup of order 6.
> According to Lagrange's Theorem,
> subgroups of a group of order 12 can have orders of either 1, 2, 3, 4, or 6.
> However, we are not guaranteed that subgroups of every possible order exist.
> To prove that A_4 has no subgroup of order 6,
> we will assume that it does have such a subgroup H and show that a contradiction must occur.
> Since A_4 contains eight 3-cycles, we know that H must contain a 3-cycle.
> We will show that if H contains one 3-cycle, then it must contain more than 6 elements.

JUDSON — the THEOREM statement (absent) and its PROOF (ours narrates it in third
person via "Judson's argument:", which is the NARRATION defect):
> The group A_4 has no subgroup of order 6.
>
> Since [A_4 : H] = 2,
> there are only two cosets of H in A_4.
> Inasmuch as one of the cosets is H itself,
> right and left cosets must coincide;
> therefore, gH = Hg or g H g^{-1} = H for every g \in A_4.
> Since there are eight 3-cycles in A_4,
> at least one 3-cycle must be in H.
> Without loss of generality, assume that (1 \, 2 \, 3) is in H.
> Then (1 \, 2 \, 3)^{-1} = (1 \, 3 \, 2) must also be in H.
> Since g h g^{-1} \in H for all g \in A_4 and all h \in H and
>   (1 \, 2 \, 4)(1 \, 2 \, 3)(1 \, 2 \, 4)^{-1} & = (1 \, 2 \, 4)(1 \, 2 \, 3)(1 \, 4 \, 2)  = (2 \, 4 \, 3)
>   (2 \, 4 \, 3)(1 \, 2 \, 3)(2 \, 4 \, 3)^{-1} & = (2 \, 4 \, 3)(1 \, 2 \, 3)(2 \, 3 \, 4)  = (1 \, 4 \, 2)
> we can conclude that H must have at least seven elements
>   (1), (1 \, 2 \, 3), (1 \, 3 \, 2), (2 \, 4 \, 3), (2 \, 4 \, 3)^{-1} = (2 \, 3 \, 4), (1 \, 4 \, 2), (1 \, 4 \, 2)^{-1} = (1 \, 2 \, 4)
> .
> Therefore, A_4 has no subgroup of order 6.

FIX — replace 1010-1019 with:
## The converse of Lagrange's Theorem is false

The group $A_4$ has order 12; however, it can be shown that it does not possess a
subgroup of order 6. According to Lagrange's Theorem, subgroups of a group of
order 12 can have orders of either 1, 2, 3, 4, or 6. However, we are not
guaranteed that subgroups of every possible order exist. To prove that $A_4$ has
no subgroup of order 6, we will assume that it does have such a subgroup $H$ and
show that a contradiction must occur. Since $A_4$ contains eight $3$-cycles, we
know that $H$ must contain a $3$-cycle. We will show that if $H$ contains one
$3$-cycle, then it must contain more than 6 elements.

> **Example.** The group $A_4$ has no subgroup of order 6.

**Proof.** Since $[A_4 : H] = 2$, there are only two cosets of $H$ in $A_4$.
Inasmuch as one of the cosets is $H$ itself, right and left cosets must coincide;
therefore, $gH = Hg$ or $g H g^{-1} = H$ for every $g \in A_4$. Since there are
eight $3$-cycles in $A_4$, at least one $3$-cycle must be in $H$. Without loss of
generality, assume that $(1\,2\,3)$ is in $H$. Then
$(1\,2\,3)^{-1} = (1\,3\,2)$ must also be in $H$. Since $g h g^{-1} \in H$ for
all $g \in A_4$ and all $h \in H$ and

$$\begin{aligned}
(1\,2\,4)(1\,2\,3)(1\,2\,4)^{-1} &= (1\,2\,4)(1\,2\,3)(1\,4\,2) = (2\,4\,3) \\
(2\,4\,3)(1\,2\,3)(2\,4\,3)^{-1} &= (2\,4\,3)(1\,2\,3)(2\,3\,4) = (1\,4\,2)
\end{aligned}$$

we can conclude that $H$ must have at least seven elements

$$(1),\ (1\,2\,3),\ (1\,3\,2),\ (2\,4\,3),\ (2\,4\,3)^{-1} = (2\,3\,4),\
(1\,4\,2),\ (1\,4\,2)^{-1} = (1\,2\,4).$$

Therefore, $A_4$ has no subgroup of order 6. $\blacksquare$

> *This argument needs a concrete $A_4$ with its eight named $3$-cycles; there is
> no such model here, so it is carried as prose only.*

### aata/6.2-lagranges-theorem.md:921-923  [PARAPHRASED]
OURS:
> Corollary 6.11 suggests that groups of prime order $p$ must somehow look like
> $\mathbb{Z}_p$ — the classification that §6.3's companions and Chapter 9's
> isomorphism machinery make precise.

JUDSON:
> [Corollary 6.11] suggests that groups of prime order p must somehow look like
> {\mathbb Z}_p.

The em-dash clause is ours.

FIX:
Corollary 6.11 suggests that groups of prime order $p$ must somehow look like
$\mathbb{Z}_p$.

### aata/6.2-lagranges-theorem.md:91  [NO-SOURCE]
OURS:
> In the form Lagrange needs it, the bijection says that a count of $H$ of size $p$
> gives a count of $gH$ of size $p$ — "each left coset has $|H|$ elements".
JUDSON: none. Our restatement of Lemma 6.8 in listing form.
FIX: wrap as a `>` aside (the header aside at 10-15 declares the listing
encoding; this is its per-theorem instance).

### aata/6.2-lagranges-theorem.md:322  [NO-SOURCE]
OURS:
> Both halves of that one-line proof are the results above — §6.1 gives the partition,
> Lemma 6.8 the common size — and they assemble by block decomposition: the group is $k$
> blocks of $p$ entries each, so a count of $k \cdot p$.
JUDSON: none.
FIX: wrap as a `>` aside.

### aata/6.2-lagranges-theorem.md:404  [NO-SOURCE]
OURS:
> "The number of elements in $H$ must divide the number of elements in $G$" is the
> divisibility reading of the same equation.
JUDSON: none (the quoted fragment is his, from the Thm 6.9 statement already
transliterated at 316-317; the sentence around it is ours).
FIX: wrap as a `>` aside.

### aata/6.2-lagranges-theorem.md:504  [NO-SOURCE]
OURS:
> A count's size is not *a priori* unique — nothing in the definition forbids two
> listings of a group having different lengths — so writing $|G|$ at all requires
> knowing that any two listings of the same group agree in length.
JUDSON: none. This is a genuine language limit and belongs in an aside by the
sanctioned rule.
FIX: wrap as a `>` aside.

### aata/6.2-lagranges-theorem.md:659  [NO-SOURCE]
OURS:
> The order of $g$ is $|\langle g \rangle|$, so this is Lagrange applied to the cyclic
> subgroup generated by $g$.
JUDSON: none — Judson gives Corollary 6.10 no proof at all.
FIX: wrap as a `>` aside.

### aata/6.2-lagranges-theorem.md:935  [NO-SOURCE]
OURS:
> Stated multiplicatively, the chain is: from $|G| = a\,|H|$ and $|H| = b\,|K|$
> conclude $|G| = (a b)\,|K|$. The cancelling of fractions is associativity of $\cdot$,
> and the content is pure arithmetic once Lagrange has supplied both factorizations.
JUDSON: none.
FIX: wrap as a `>` aside.

---

## Cross-file observation

The six files share one systematic habit: whenever the kernel needs a lemma
Judson does not state, a paragraph is written IN HIS REGISTER ("Three ring facts
come first", "Two more facts the next proof needs") and dropped into the
transliterated flow. That habit accounts for 41 of the 55 defects. A single
mechanical pass — demote every such paragraph to a `>` aside — fixes all of them
and leaves the 14 word-level defects (real truncations and paraphrases of
Judson's own words) as the only hand-repair.

The 14 word-level defects cluster in two places: 2.3-primes.md, where four of
Judson's five proofs were replaced by our own (Bezout's second paragraph, the
Coprime Corollary, Euclid's Lemma, the Infinitude of Primes, and both halves of
the FTA), and 4.3-repeated-squares.md, where the entire section is a
condensation rather than a transliteration despite being pure prose with no
formal content to accommodate.
