# Transliteration fidelity audit — group 3

9 files, 49 machine-flagged paragraphs. The machine score was a weak signal; several
flagged paragraphs are faithful bridging scaffolding and are recorded as NOT defects at
the end of each section. Conversely, reading the XML turned up defects the flagger never
saw — whole Judson paragraphs, examples, and in two cases whole theorems missing. Those
are included.

---

## aata/1.2.2-functions.md

Judson's §1.2.2 prose here is faithful and essentially complete: the relations / mapping /
well-defined / onto / one-to-one / bijective definitions, both figure examples, the
`f(x)=x^3` and `f∘g` examples, Theorem 1.22's statement and his full proof text (including
"We will prove (1) and (3). Part (2) is left as an exercise. Part (4) follows directly from
(2) and (3)." verbatim at line 155), and Theorem 1.25's proof.

### NOT defects

- **:65, :77** — `*(Figure omitted: ...)*` notes, substituting for Judson's two `<image>`
  elements. A real medium limit; the prose referring to the figures ("In the figure below we
  define relations $f$ and $g$...") is carried verbatim around them. Legitimate.
- **:429** — "**(4)** A bijection is a map that is both one-to-one and onto, so this
  follows directly from (2) and (3)." A **proof-block section marker**, not a replacement:
  Judson's own sentence "Part (4) follows directly from (2) and (3)." is already verbatim at
  :155, and the added clause restates his earlier definition "A map that is both one-to-one
  and onto is called **bijective**" (carried at :71). NO-SOURCE / legitimate.

**0 defects.**

---

## aata/10.1-factor-groups-and-normal-subgroups.md

### aata/10.1 (missing before :11)  [TRUNCATED]
OURS:   Opens straight at "## Normal subgroups / **Definition.** A subgroup $H$ of a group
        $G$ is **normal** in $G$ if ...". Judson's chapter-opening paragraph is absent.
JUDSON: "If $H$ is a subgroup of a group $G$, then right cosets are not always the same as
        left cosets; that is, it is not always the case that $gH = Hg$ for all $g \in G$.
        The subgroups for which this property holds play a critical role in group theory —
        they allow for the construction of a new class of groups, called factor or quotient
        groups. Factor groups may be studied directly or by using homomorphisms, a
        generalization of isomorphisms. We will study homomorphisms in Chapter 11."
FIX:    Insert that paragraph immediately after the attribution header, before
        "## Normal subgroups".

### aata/10.1:72  [PARAPHRASED]
OURS:   "**Examples.** Every subgroup of an abelian group is normal, since $gh = hg$ makes
        $gH = Hg$ automatic. In $S_3$, the subgroup $\{(1), (12)\}$ is *not* normal —
        $(123)H = \{(123),(13)\}$ while $H(123) = \{(123),(23)\}$ — but
        $N = \{(1),(123),(132)\}$ is, since its two cosets are $N$ itself and
        $(12)N = N(12) = \{(12),(13),(23)\}$."
JUDSON: (two separate examples)
        "**Example.** Let $G$ be an abelian group. Every subgroup $H$ of $G$ is a normal
        subgroup. Since $gh = hg$ for all $g \in G$ and $h \in H$, it will always be the
        case that $gH = Hg$."
        "**Example.** Let $H$ be the subgroup of $S_3$ consisting of elements $(1)$ and
        $(12)$. Since
        $$(123) H = \{ (1 \, 2 \, 3), (1 \, 3) \} \quad \text{and} \quad H (1 \, 2 \, 3) = \{ (1 \, 2 \, 3), (2 \, 3) \},$$
        $H$ cannot be a normal subgroup of $S_3$. However, the subgroup $N$, consisting of
        the permutations $(1)$, $(1 \, 2 \, 3)$, and $(1 \, 3 \, 2)$, is normal since the
        cosets of $N$ are
        $$\begin{aligned} N &= \{ (1), (1 \, 2 \, 3), (1 \, 3 \, 2) \} \\ (1 \, 2) N &= N (1 \, 2) = \{ (1 \, 2), (1 \, 3), (2 \, 3) \} \end{aligned}.$$"
FIX:    Replace our single "**Examples.**" paragraph with Judson's two "**Example.**"
        paragraphs, quoted above verbatim.

### aata/10.1 (missing before :78)  [TRUNCATED]
OURS:   Our "## Theorem 10.3 — the conjugation characterization" heading follows the
        examples directly.
JUDSON: "The following theorem is fundamental to our understanding of normal subgroups."
FIX:    Insert that sentence between the examples and the Theorem 10.3 statement.

### aata/10.1:95  [NARRATION]
OURS:   "Conditions (2) and (3) say the same thing here, containment in both directions
        being agreement, so the theorem is the equivalence of the coset form with the
        conjugation form. Forward: there exists $n'$ with $gn = n'g$. Backward: conjugate by
        $g^{-1}$ and collapse $(g^{-1})^{-1} = g$."
JUDSON: none — no counterpart. His proof text is carried verbatim immediately above
        (:86–93).
FIX:    Wrap as a `>` aside (the (2)⇔(3) collapse is a real representational divergence):
        "> *With no sort of subsets, "$gNg^{-1} \subset N$" and "$gNg^{-1} = N$" are the
        > same predicate statement, so Judson's three-way equivalence degenerates to the
        > equivalence of the coset form with the conjugation form.*"
        Drop the "Forward:/Backward:" sentences — they restate his proof, already quoted.

### aata/10.1:379  [NARRATION]
OURS:   "Well-definedness is the content. Since $aN = bN$ holds exactly when
        $a^{-1}b \in N$ (§6.1), the statement reads: if $a, b$ represent the same coset and
        $c, d$ do, then so do $ac$ and $bd$. The middle step $bn_1N = bNn_1 = bN$ is where
        normality enters, and it appears as the hypothesis."
JUDSON: none — no counterpart. His Theorem 10.4 proof is verbatim above at :371–377.
FIX:    Wrap as a `>` aside — the §6.1-criterion restatement IS a declared divergence:
        "> *With cosets carried as predicates, "$aN = bN$" is restated by §6.1's criterion
        > as $a^{-1}b \in N$, so well-definedness reads: if $a^{-1}b \in N$ and
        > $c^{-1}d \in N$ then $(ac)^{-1}(bd) \in N$. Judson's middle step
        > $bn_1N = bNn_1 = bN$ is where normality enters; it appears as the hypothesis.*"

### aata/10.1:500  [TRUNCATED]
OURS:   "The remainder of the theorem is easy: $eN = N$ is the identity and $g^{-1}N$ is the
        inverse of $gN$, so the cosets of $N$ form a group under this operation."
JUDSON: "The remainder of the theorem is easy: $eN = N$ is the identity and $g^{-1} N$ is
        the inverse of $gN$. The order of $G/N$ is, of course, the number of cosets of $N$
        in $G$."
FIX:    "The remainder of the theorem is easy: $eN = N$ is the identity and $g^{-1}N$ is the
        inverse of $gN$. The order of $G/N$ is, of course, the number of cosets of $N$ in
        $G$."

### aata/10.1:662  [NARRATION]
OURS:   "The class map $G \to G/N$ is itself a homomorphism, and its kernel is exactly $N$ —
        both of which Judson takes up in §11.2."
JUDSON: none — no counterpart in §10.1.
FIX:    Wrap as a `>` aside, striking the "Judson takes up" narration:
        "> *These two facts — that the class map $G \to G/N$ is a homomorphism and that its
        > kernel is $N$ — are §11.2 material, proved here because the quotient
        > construction's own group axioms are stated through the class map.*"

### aata/10.1 (missing after :757, end of file)  [TRUNCATED]
OURS:   File ends with the `theCanonicalMapsKernelIsN` proof block. Judson's four
        post-theorem paragraphs of §10.1 are absent entirely, no declared divergence.
JUDSON: "It is very important to remember that the elements in a factor group are sets of
        elements in the original group."
        "**Example.** Consider the normal subgroup of $S_3$,
        $N = \{ (1), (1 \, 2 \, 3), (1 \, 3 \, 2) \}$. The cosets of $N$ in $S_3$ are $N$
        and $(12) N$. The factor group $S_3 / N$ has the following multiplication table.
        $$\begin{array}{c|cc} & N & (1 \, 2) N \\ \hline N & N & (1 \, 2) N \\ (1 \, 2) N & (1 \, 2) N & N \end{array}$$
        This group is isomorphic to ${\mathbb Z}_2$. At first, multiplying cosets seems both
        complicated and strange; however, notice that $S_3 / N$ is a smaller group. The
        factor group displays a certain amount of information about $S_3$. Actually,
        $N = A_3$, the group of even permutations, and
        $(1 \, 2) N = \{ (1 \, 2), (1 \, 3), (2 \, 3) \}$ is the set of odd permutations.
        The information captured in $G/N$ is parity; that is, multiplying two even or two
        odd permutations results in an even permutation, whereas multiplying an odd
        permutation by an even permutation yields an odd permutation."
        "**Example.** Consider the normal subgroup $3 {\mathbb Z}$ of ${\mathbb Z}$. The
        cosets of $3 {\mathbb Z}$ in ${\mathbb Z}$ are
        $$\begin{aligned} 0 + 3 {\mathbb Z} &= \{ \ldots, -3, 0, 3, 6, \ldots \} \\ 1 + 3 {\mathbb Z} &= \{ \ldots, -2, 1, 4, 7, \ldots \} \\ 2 + 3 {\mathbb Z} &= \{ \ldots, -1, 2, 5, 8, \ldots \} \end{aligned}.$$
        The group ${\mathbb Z}/ 3 {\mathbb Z}$ is given by the Cayley table below.
        $$\begin{array}{c|ccc} + & 0 + 3{\mathbb Z} & 1 + 3{\mathbb Z} & 2 + 3{\mathbb Z} \\ \hline 0 + 3{\mathbb Z} & 0 + 3{\mathbb Z} & 1 + 3{\mathbb Z} & 2 + 3{\mathbb Z} \\ 1 + 3{\mathbb Z} & 1 + 3{\mathbb Z} & 2 + 3{\mathbb Z} & 0 + 3{\mathbb Z} \\ 2 + 3{\mathbb Z} & 2 + 3{\mathbb Z} & 0 + 3{\mathbb Z} & 1 + 3{\mathbb Z} \end{array}$$
        In general, the subgroup $n {\mathbb Z}$ of ${\mathbb Z}$ is normal. The cosets of
        ${\mathbb Z } / n {\mathbb Z}$ are
        $$\begin{aligned} n {\mathbb Z} \\ 1 + n {\mathbb Z} \\ 2 + n {\mathbb Z} \\ \vdots \\ (n-1) + n {\mathbb Z} \end{aligned}.$$
        The sum of the cosets $k + n{\mathbb Z}$ and $l + n{\mathbb Z}$ is
        $k+l + n{\mathbb Z}$. Notice that we have written our cosets additively, because the
        group operation is integer addition."
        "**Example.** Consider the dihedral group $D_n$, generated by the two elements $r$
        and $s$, satisfying the relations
        $$\begin{aligned} r^n &= \identity \\ s^2 &= \identity \\ srs &= r^{-1} \end{aligned}.$$
        The element $r$ actually generates the cyclic subgroup of rotations, $R_n$, of $D_n$.
        Since $srs^{-1} = srs = r^{-1} \in R_n$, the group of rotations is a normal subgroup
        of $D_n$; therefore, $D_n / R_n$ is a group. Since there are exactly two elements in
        this group, it must be isomorphic to ${\mathbb Z}_2$."
FIX:    Append all four paragraphs verbatim at the end of the file. They state no theorems
        — concrete examples needing no proof blocks; nothing here is infeasible.

**7 defects** (1 PARAPHRASED, 3 NARRATION, 3 TRUNCATED).

---

## aata/11.2-the-isomorphism-theorems.md

### aata/11.2 (missing before :136)  [TRUNCATED]
OURS:   Our "## First Isomorphism Theorem" heading follows the canonical-homomorphism proof
        blocks and the `>` aside about `≅`.
JUDSON: "The following theorems describe the relationships between group homomorphisms,
        normal subgroups, and factor groups."
FIX:    Insert that sentence just before the "## First Isomorphism Theorem" heading.

### aata/11.2:145  [TRUNCATED]
OURS:   "**Proof.** Define $\eta : G/K \rightarrow \psi(G)$ by $\eta(gK) = \psi(g)$. We
        first show that $\eta$ is a well-defined map. If $g_1K = g_2K$, then for some
        $k \in K$, $g_1k = g_2$; consequently,
        $\eta(g_1K) = \psi(g_1) = \psi(g_1)\psi(k) = \psi(g_1k) = \psi(g_2) = \eta(g_2K)$.
        We must also show that $\eta$ is a homomorphism: ..."
JUDSON: "We already know that $K$ is normal in $G$. Define $\eta: G/K \rightarrow \psi(G)$
        by $\eta(gK) = \psi(g)$. We first show that $\eta$ is a well-defined map. If
        $g_1 K =g_2 K$, then for some $k \in K$, $g_1 k=g_2$; consequently,
        $\eta(g_1 K) = \psi(g_1) = \psi(g_1) \psi(k) = \psi(g_1k) = \psi(g_2) = \eta(g_2 K)$.
        Thus, $\eta$ does not depend on the choice of coset representatives and the map
        $\eta: G/K \rightarrow \psi(G)$ is uniquely defined since $\psi = \eta \phi$. We
        must also show that $\eta$ is a homomorphism. Indeed, ..."
FIX:    Two insertions. Open the proof with "We already know that $K$ is normal in $G$."
        before "Define $\eta$ …", and after "… $= \eta(g_2K)$." insert "Thus, $\eta$ does
        not depend on the choice of coset representatives and the map
        $\eta : G/K \rightarrow \psi(G)$ is uniquely defined since $\psi = \eta\phi$."
        Also restore "Indeed," before the homomorphism display.

### aata/11.2:150  [PARAPHRASED]
OURS:   "To show $\eta$ is one-to-one, suppose $\eta(g_1K) = \eta(g_2K)$. Then
        $\psi(g_1) = \psi(g_2)$, so $\psi(g_1^{-1}g_2) = e$, so $g_1^{-1}g_2$ is in the
        kernel; hence $g_1K = g_2K$."
JUDSON: "To show that $\eta$ is one-to-one, suppose that $\eta(g_1 K) = \eta(g_2 K)$. Then
        $\psi(g_1) = \psi(g_2)$. This implies that $\psi( g_1^{-1} g_2 ) = e$, or
        $g_1^{-1} g_2$ is in the kernel of $\psi$; hence, $g_1^{-1} g_2K = K$; that is,
        $g_1K =g_2K$."
FIX:    "To show that $\eta$ is one-to-one, suppose that $\eta(g_1 K) = \eta(g_2 K)$. Then
        $\psi(g_1) = \psi(g_2)$. This implies that $\psi(g_1^{-1} g_2) = e$, or
        $g_1^{-1} g_2$ is in the kernel of $\psi$; hence, $g_1^{-1} g_2 K = K$; that is,
        $g_1 K = g_2 K$."
        (The dropped step $g_1^{-1}g_2K = K$ is exactly the Lemma-6.3 hinge.)

### aata/11.2:154  [NARRATION]
OURS:   "Well-definedness is the first thing to check: the premise "$g_1K = g_2K$" is the
        equation $\mathrm{cls}(g_1) = \mathrm{cls}(g_2)$ between classes, and $\eta$'s value
        must not depend on which representative carries it."
JUDSON: none — no counterpart.
FIX:    Wrap as a `>` aside (genuine representational note):
        "> *"$g_1K = g_2K$" is carried here as the equation
        > $\mathrm{cls}(g_1) = \mathrm{cls}(g_2)$ in the quotient sort, so
        > well-definedness is that $\eta$'s value does not depend on which representative
        > carries the class.*"

### aata/11.2:374  [NO-SOURCE]
OURS:   "Clearly $\eta$ is onto $\psi(G)$: every element of the image is
        $\psi(g) = \eta(gK)$ by construction."
JUDSON: "Clearly, $\eta$ is onto $\psi( G)$." — already carried verbatim inside the proof at
        :148. The explanatory clause after the colon is ours.
FIX:    Delete. It restates a sentence quoted 226 lines above.

### aata/11.2 (missing before :377)  [TRUNCATED]
OURS:   Our "## Second Isomorphism Theorem" heading follows the η proof blocks.
JUDSON: "Mathematicians often use diagrams called **commutative diagrams** to describe such
        theorems. The following diagram commutes since $\psi = \eta \phi$."
        (followed by the $G \to H$ / $G \to G/K \to H$ triangle figure)
        "**Example.** Let $G$ be a cyclic group with generator $g$. Define a map
        $\phi : {\mathbb Z} \rightarrow G$ by $n \mapsto g^n$. This map is a surjective
        homomorphism since $\phi( m + n) = g^{m+n} = g^m g^n = \phi(m) \phi(n)$. Clearly
        $\phi$ is onto. If $|g| = m$, then $g^m = e$. Hence, $\ker \phi = m {\mathbb Z}$ and
        ${\mathbb Z} / \ker \phi = {\mathbb Z} / m {\mathbb Z} \cong G$. On the other hand,
        if the order of $g$ is infinite, then $\ker \phi = 0$ and $\phi$ is an isomorphism of
        $G$ and ${\mathbb Z}$. Hence, two cyclic groups are isomorphic exactly when they
        have the same order. Up to isomorphism, the only cyclic groups are ${\mathbb Z}$ and
        ${\mathbb Z}_n$."
FIX:    Insert both paragraphs verbatim before "## Second Isomorphism Theorem", the diagram
        as a `*(Figure omitted: ...)*` note in the style 1.2.2 uses.

### aata/11.2:398  [PARAPHRASED]
OURS:   "By the First Isomorphism Theorem, the image of $\phi$ is isomorphic to
        $H/\ker\phi$; and since $\ker\phi = \{h \in H : h \in N\} = H \cap N$, we get
        $HN/N = \phi(H) \cong H/H \cap N$."
JUDSON: "By the First Isomorphism Theorem, the image of $\phi$ is isomorphic to
        $H / \ker \phi$; that is, $HN/N = \phi(H) \cong H / \ker \phi$. Since
        $\ker \phi = \{ h \in H : h \in N \} = H \cap N$,
        $HN/N = \phi(H) \cong H / H \cap N$."
FIX:    "By the First Isomorphism Theorem, the image of $\phi$ is isomorphic to
        $H/\ker\phi$; that is, $HN/N = \phi(H) \cong H/\ker\phi$. Since
        $\ker\phi = \{h \in H : h \in N\} = H \cap N$, $HN/N = \phi(H) \cong H/H \cap N$."

### aata/11.2:402  [NARRATION]
OURS:   "Each regrouping inserts a cancelling pair — $h_2h_2^{-1}$ in the product,
        $h^{-1}h$ in the inverse — so each is written out below."
JUDSON: none — no counterpart. His two regroupings are verbatim at :386–389.
FIX:    Wrap as a `>` aside:
        "> *Judson's two regroupings each insert a cancelling pair — $h_2h_2^{-1}$ in
        > $(h_1n_1)(h_2n_2) = h_1h_2((h_2)^{-1}n_1h_2)n_2$ and $h^{-1}h$ in
        > $(hn)^{-1} = h^{-1}(hn^{-1}h^{-1})$ — so each is written out step by step below.*"

### aata/11.2:810  [NARRATION]
OURS:   "Surjectivity of $\phi$ onto $HN/N$ is the computation "any coset $hnN = hN$": every
        element of $HN$ lies in the same $N$-coset as some element of $H$, which with §6.1's
        criterion reads $h^{-1}x \in N$."
JUDSON: none — no counterpart. His "The map $\phi$ is onto, since any coset $hnN = hN$ is
        the image of $h$ in $H$." is carried at :394.
FIX:    Wrap as a `>` aside:
        "> *With cosets carried as predicates, "any coset $hnN = hN$" becomes: every element
        > of $HN$ lies in the same $N$-coset as some element of $H$, which by §6.1's
        > criterion is $h^{-1}x \in N$.*"

### aata/11.2:896  [NARRATION]
OURS:   "The other two halves of Judson's $\phi$ are statements about the class map. Taking
        $H$ as a subgroup of the group $G$ that $N$ is normal in, $\phi$ is $h \mapsto hN$,
        i.e. $h \mapsto \mathrm{cls}(h)$ — so $\phi$ preserving the operation is the class of
        a product being the product of the classes:"
JUDSON: none — no counterpart.
FIX:    Wrap as a `>` aside, stripping the "Judson's" narration:
        "> *$\phi : h \mapsto hN$ is carried here as $h \mapsto \mathrm{cls}(h)$, so
        > "$\phi$ is a homomorphism" is the class of a product being the product of the
        > classes.*"

### aata/11.2:938  [NARRATION]
OURS:   "And $\ker\phi = \{h \in H : h \in N\} = H \cap N$, which is Judson's last step
        before applying the First Isomorphism Theorem. A class is the identity exactly when
        its representative lies in $N$, so for $h \in H$ the kernel condition is membership
        in both."
JUDSON: none — no counterpart. The equation itself is verbatim at :397–398.
FIX:    Wrap as a `>` aside, stripping "which is Judson's last step":
        "> *A class is the identity exactly when its representative lies in $N$, so for
        > $h \in H$ the kernel condition $\ker\phi = \{h \in H : h \in N\}$ is membership in
        > both $H$ and $N$.*"

### aata/11.2:1039  [TRUNCATED]
OURS:   "**Proof.** Let $H$ be a subgroup of $G$ containing $N$. Since $N$ is normal in $H$,
        $H/N$ is a factor group. Let $aN$ and $bN$ be elements of $H/N$. Then
        $(aN)(b^{-1}N) = ab^{-1}N \in H/N$; hence $H/N$ is a subgroup of $G/N$. Now let $S$
        be a subgroup of $G/N$ and put $H = \{g \in G : gN \in S\}$; then $H$ is a subgroup
        of $G$, clearly containing $N$, and $S = H/N$. Finally, suppose $H_1$ and $H_2$ are
        subgroups of $G$ containing $N$ with $H_1/N = H_2/N$; since $N$ is contained in
        $H_2$, every $h_1 \in H_1$ is in $H_2$, and symmetrically. $\blacksquare$"
JUDSON: "Let $H$ be a subgroup of $G$ containing $N$. Since $N$ is normal in $H$, $H/N$ is a
        factor group. Let $aN$ and $bN$ be elements of $H/N$. Then
        $(aN)( b^{-1} N )= ab^{-1}N \in H/N$; hence, $H/N$ is a subgroup of $G/N$."
        "Let $S$ be a subgroup of $G/N$. This subgroup is a set of cosets of $N$. If
        $H= \{ g \in G : gN \in S \}$, then for $h_1, h_2 \in H$, we have that
        $(h_1 N)( h_2 N )= h_1 h_2 N \in S$ and $h_1^{-1} N \in S$. Therefore, $H$ must be a
        subgroup of $G$. Clearly, $H$ contains $N$. Therefore, $S = H / N$. Consequently, the
        map $H \mapsto H/N$ is onto."
        "Suppose that $H_1$ and $H_2$ are subgroups of $G$ containing $N$ such that
        $H_1/N = H_2/N$. If $h_1 \in H_1$, then $h_1 N \in H_1/N$. Hence,
        $h_1 N = h_2 N \subset H_2$ for some $h_2$ in $H_2$. However, since $N$ is contained
        in $H_2$, we know that $h_1 \in H_2$ or $H_1 \subset H_2$. Similarly,
        $H_2 \subset H_1$. Since $H_1 = H_2$, the map $H \mapsto H/N$ is one-to-one."
        "Suppose that $H$ is normal in $G$ and $N$ is a subgroup of $H$. Then it is easy to
        verify that the map $G/N \rightarrow G/H$ defined by $gN \mapsto gH$ is a
        homomorphism. The kernel of this homomorphism is $H/N$, which proves that $H/N$ is
        normal in $G/N$. Conversely, suppose that $H/N$ is normal in $G/N$. The homomorphism
        given by
        $$G \rightarrow G/N \rightarrow \frac{G/N}{H/N}$$
        has kernel $H$. Hence, $H$ must be normal in $G$."
FIX:    Replace our condensed proof with Judson's four paragraphs above, verbatim. Ours
        collapses his second paragraph to one clause, his third to half a sentence, and
        drops his fourth (the normal-subgroups half of the correspondence) entirely — which
        also makes :1541's forward reference to "the Correspondence Theorem's last
        paragraph" point at text the file never carries.

### aata/11.2:1047  [NARRATION]
OURS:   ""$S = H/N$" is agreement of two membership predicates on $G/N$, which is why the
        surjectivity result below is an `iff`. Each half is stated at a given subgroup."
JUDSON: none — no counterpart.
FIX:    Wrap as a `>` aside:
        "> *"$S = H/N$" is agreement of two membership predicates on $G/N$, which is why the
        > surjectivity result below is an `iff`; and with no quantification over subgroups,
        > each half is stated at a given subgroup.*"

### aata/11.2 (missing before :1535)  [TRUNCATED]
OURS:   Our "## Third Isomorphism Theorem" heading follows the correspondence proof blocks.
JUDSON: "Notice that in the course of the proof of Theorem 11.13, we have also proved the
        following theorem."
FIX:    Insert that sentence before the "## Third Isomorphism Theorem" heading. (Only
        recoverable once :1039's dropped fourth paragraph is restored — that is the "course
        of the proof" it refers to.)

### aata/11.2:1541  [NARRATION]
OURS:   "The proof is left to the reader. The route is the one the Correspondence Theorem's
        last paragraph sketches: the composite $G \rightarrow G/N \rightarrow (G/N)/(H/N)$
        is a homomorphism with kernel $H$, so the First Isomorphism Theorem gives
        $G/H \cong (G/N)/(H/N)$."
JUDSON: none — Judson gives no proof of Theorem 11.14 at all (it falls out of 11.13's proof,
        which is what his "Notice that in the course of the proof …" sentence says), and he
        never says "The proof is left to the reader" here.
FIX:    Delete the whole paragraph; its job is done by Judson's own "Notice that in the
        course of the proof of Theorem 11.13, we have also proved the following theorem."
        (restored above) placed BEFORE the theorem statement. The `>` aside at :1545 already
        declares why the two nested quotients are out of reach.

### aata/11.2 (missing after :1548, end of file)  [TRUNCATED]
OURS:   The file ends with the `>` aside about nested quotients.
JUDSON: "**Example.** By the Third Isomorphism Theorem,
        ${\mathbb Z} / m {\mathbb Z} \cong ({\mathbb Z}/ mn {\mathbb Z})/ (m {\mathbb Z}/ mn {\mathbb Z})$.
        Since $| {\mathbb Z} / mn {\mathbb Z} | = mn$ and
        $|{\mathbb Z} / m{\mathbb Z}| = m$, we have $| m {\mathbb Z} / mn {\mathbb Z}| = n$."
FIX:    Append that example verbatim at the end of the file.

**15 defects** (2 PARAPHRASED, 6 NARRATION, 6 TRUNCATED, 1 NO-SOURCE).

---

## aata/3.1-integers-mod-n.md

This file's bridging commentary is mostly well-placed: Judson's statements and his (1) and
(6) proof paragraphs are carried verbatim (statements in `>` blockquotes, proofs as plain
paragraphs), and each plain paragraph that follows is clearly ours. The real defects are at
the top and bottom of the section.

### aata/3.1:9  [NO-SOURCE]
OURS:   "This section motivates the definition of a group, which does not arrive until §3.2,
        with two families of concrete examples: the **integers mod $n$** and the
        **symmetries** of a plane figure. It rests on the integer theory of Chapter 2 — the
        ring $(\mathbb Z, +, \cdot)$, divisibility, and the gcd/Bézout theory."
JUDSON: His corresponding opening prose, NOT carried anywhere, is:
        "Let us now investigate some mathematical structures that can be viewed as sets with
        single operations."
        "**The Integers mod $n$.** The integers mod $n$ have become indispensable in the
        theory and applications of algebra. In mathematics they are used in cryptography,
        coding theory, and the detection of errors in identification codes. We have already
        seen that two integers $a$ and $b$ are equivalent mod $n$ if $n$ divides $a - b$.
        The integers mod $n$ also partition ${\mathbb Z}$ into $n$ different equivalence
        classes; we will denote the set of these equivalence classes by ${\mathbb Z}_n$."
FIX:    Replace our paragraph with Judson's two paragraphs above. (A `>` aside saying this
        section motivates §3.2's definition may stay, but must not stand in place of his
        prose.) Note that after this fix our :61 becomes a duplicate of his second
        paragraph's content and should be deleted.

### aata/3.1 (missing before :79)  [TRUNCATED]
OURS:   Our "## The proposition on equivalence classes in $\mathbb Z_n$" heading follows the
        `congruent` definition directly.
JUDSON: "**Example.** Consider the integers modulo 12 and the corresponding partition of the
        integers:
        $$\begin{aligned} [0] &= \{ \ldots, -12, 0, 12, 24, \ldots \}, \\ [1] &= \{ \ldots, -11, 1, 13, 25, \ldots \}, \\ &\ \ \vdots \\ [11] &= \{ \ldots, -1, 11, 23, 35, \ldots \} \end{aligned}.$$
        When no confusion can arise, we will use $0, 1, \ldots, 11$ to indicate the
        equivalence classes $[0], [1], \ldots, [11]$ respectively."
        "We can do arithmetic on ${\mathbb Z}_n$. For two integers $a$ and $b$, define
        addition modulo $n$ to be $(a + b) \pmod{n}$; that is, the remainder when $a + b$ is
        divided by $n$. Similarly, multiplication modulo $n$ is defined as $(a b) \pmod{ n}$,
        the remainder when $a b$ is divided by $n$."
        "**Example.** The following examples illustrate integer arithmetic modulo $n$:
        $$\begin{aligned} 7 + 4 &\equiv 1 \pmod{ 5} & 7 \cdot 3 &\equiv 1 \pmod{ 5} \\ 3 + 5 &\equiv 0 \pmod{ 8} & 3 \cdot 5 &\equiv 7 \pmod{ 8} \\ 3 + 4 &\equiv 7 \pmod{ 12} & 3 \cdot 4 &\equiv 0 \pmod{ 12} \end{aligned}.$$
        In particular, notice that it is possible that the product of two nonzero numbers
        modulo $n$ can be equivalent to $0$ modulo $n$."
        "Most, but not all, of the usual laws of arithmetic hold for addition and
        multiplication in ${\mathbb Z}_n$. For instance, it is not necessarily true that
        there is a multiplicative inverse. Consider the multiplication table for
        ${\mathbb Z}_8$ in Table 3.1. Notice that $2$, $4$, and $6$ do not have
        multiplicative inverses; that is, for $n = 2$, $4$, or $6$, there is no integer $k$
        such that $k n \equiv 1 \pmod{ 8}$."
        (plus the $\mathbb Z_8$ multiplication table itself)
FIX:    Insert those four paragraphs and the table verbatim between the `congruent`
        definition block and the "## The proposition …" heading.

### aata/3.1 (missing after :693, end of file)  [TRUNCATED]
OURS:   File ends with the `unitIffCoprime` proof block. §3.1's entire second half — the
        "Symmetries" subsection, which the FILE'S OWN TITLE names ("Integer Equivalence
        Classes and **Symmetries**") and whose header paragraph promises ("two families of
        concrete examples: the integers mod $n$ and the **symmetries** of a plane figure") —
        is absent, with no declared divergence.
JUDSON: "**Symmetries.** A symmetry of a geometric figure is a rearrangement of the figure
        preserving the arrangement of its sides and vertices as well as its distances and
        angles. A map from the plane to itself preserving the symmetry of an object is called
        a **rigid motion**. For example, if we look at the rectangle in Figure 3.2, it is
        easy to see that a rotation of $180^{\circ}$ or $360^{\circ}$ returns a rectangle in
        the plane with the same orientation as the original rectangle and the same
        relationship among the vertices. A reflection of the rectangle across either the
        vertical axis or the horizontal axis can also be seen to be a symmetry. However, a
        $90^{\circ}$ rotation in either direction cannot be a symmetry unless the rectangle
        is a square."
        (then the equilateral-triangle development: "Let us find the symmetries of the
        equilateral triangle $\bigtriangleup ABC$. To find a symmetry of
        $\bigtriangleup ABC$, we must first examine the permutations of the vertices $A$,
        $B$, and $C$ and then ask if a permutation extends to a symmetry of the triangle.
        Recall that a permutation of a set $S$ is a one-to-one and onto map
        $\pi : S \rightarrow S$. …" and the rest of §3.1's symmetry material)
FIX:    Either transliterate the "Symmetries" subsection (concrete prose and figures, so it
        needs `*(Figure omitted: ...)*` notes in 1.2.2's style but no proof blocks), or add a
        `>` aside at the end declaring the divergence in the sanctioned form — "*Judson
        continues §3.1 with the Symmetries subsection …; we are stopping at the integers mod
        $n$ because …*" — and amend the header's claim that it covers "two families".

### NOT defects

- **:97, :106, :132, :258, :394** — the "the two sides are *equal* integers … so their
  difference is $0$ and $n \mid 0$" family. Not replacements for Judson's words: his
  statements sit verbatim in the `>` blockquotes directly above each (:103–104, :256, :337,
  :392), and his (1) and (6) proofs are verbatim at :103–104 and :508–516. Each says what
  the following `2b4m` block proves and why the relation-level argument differs from his
  remainder argument — the role of a divergence note. Ideally `>` asides; borderline style,
  not fidelity defects.
- **:61** — counted under the :9 fix above (becomes a duplicate once his opening is
  restored).

**3 defects** (1 NO-SOURCE, 2 TRUNCATED).

---

## aata/3.3-subgroups.md

One of the better files: Judson's five examples, his "Let us examine some criteria …"
lead-in, his Proposition 3.21 statement and full two-direction proof, and his Proposition
3.22 statement are all carried verbatim.

### aata/3.3 (missing before :12)  [TRUNCATED]
OURS:   File opens straight at "## Definition / **Definition.** Let $G$ be a group and $H$ a
        subset of $G$. …".
JUDSON: "**Definitions and Examples.** Sometimes we wish to investigate smaller groups
        sitting inside a larger group. The set of even integers
        $2{\mathbb Z} = \{\ldots, -2, 0, 2, 4, \ldots \}$ is a group under the operation of
        addition. This smaller group sits naturally inside of the group of integers under
        addition."
FIX:    Insert that paragraph immediately after the attribution header, before
        "## Definition".

### aata/3.3:12  [PARAPHRASED]
OURS:   "**Definition.** Let $G$ be a group and $H$ a subset of $G$. Then $H$ is a
        **subgroup** of $G$ if $H$ is itself a group under the operation induced by $G$. We
        write $H \leq G$; if $H$ is a proper subset of $G$, then $H$ is a **proper
        subgroup**, written $H \lt G$. The subgroup $\{e\}$ consisting of the identity alone
        is the **trivial subgroup**; every group $G$ has $\{e\}$ and $G$ itself as
        subgroups."
JUDSON: "We define a **subgroup** $H$ of a group $G$ to be a subset $H$ of $G$ such that
        when the group operation of $G$ is restricted to $H$, $H$ is a group in its own
        right. Observe that every group $G$ with at least two elements will always have at
        least two subgroups, the subgroup consisting of the identity element alone and the
        entire group itself. The subgroup $H = \{ e \}$ of a group $G$ is called the
        **trivial subgroup**. A subgroup that is a proper subset of $G$ is called a **proper
        subgroup**. In many of the examples that we have investigated up to this point, there
        exist other subgroups besides the trivial and improper subgroups."
FIX:    Replace our paragraph with Judson's, verbatim as quoted. Three substantive drifts,
        not just wording: he says "every group $G$ **with at least two elements**" (ours
        drops the hypothesis), his "$H \leq G$" / "$H \lt G$" notation does not appear in
        §3.3 at all (we introduced it), and his closing sentence "In many of the examples …
        there exist other subgroups besides the trivial and improper subgroups." — which
        motivates the examples that follow — is dropped.

### aata/3.3:235  [TRUNCATED]
OURS:   "**Proof.** First assume that $H$ is a subgroup of $G$. Since $h$ is in $H$, its
        inverse $h^{-1}$ must also be in $H$. Because of the closure of the group operation,
        $gh^{-1} \in H$."
JUDSON: "First assume that $H$ is a subgroup of $G$. We wish to show that $gh^{-1} \in H$
        whenever $g$ and $h$ are in $H$. Since $h$ is in $H$, its inverse $h^{-1}$ must also
        be in $H$. Because of the closure of the group operation, $gh^{-1} \in H$."
FIX:    "**Proof.** First assume that $H$ is a subgroup of $G$. We wish to show that
        $gh^{-1} \in H$ whenever $g$ and $h$ are in $H$. Since $h$ is in $H$, its inverse
        $h^{-1}$ must also be in $H$. Because of the closure of the group operation,
        $gh^{-1} \in H$."
        (Without his dropped sentence, ours introduces $g$ and $h$ with no antecedent.)

### NOT defects

- **:152** — "That converse is checkable: over the members of $H$, the three group axioms
  hold, and the identity and inverses stay inside." Judson's converse paragraph is verbatim
  immediately above (:148–151); this says what the following `2b4m` block does, and the
  file's :225 aside already explains why only the forward direction is out of reach.
  Borderline style.
- **:390** — "Having the identity, inverses, and products, $K$ meets the subgroup criterion
  — so $K \leq G$, completing the test." A proof-block closer for the one-step test, whose
  prose Judson supplies verbatim above at :270–274. Legitimately needed scaffolding for a
  proof split across three `2b4m` blocks.
- **:395, :507** — the intersection-of-subgroups section. Judson's §3.3 contains NO such
  result (it is an exercise), and our :395 says so explicitly ("A natural consequence,
  developed in the §3.3 exercises"). Our own addition, honestly labelled. NO-SOURCE /
  legitimate.

**3 defects** (1 PARAPHRASED, 2 TRUNCATED).

---

## aata/4.1-cyclic-subgroups.md

### aata/4.1:352  [PARAPHRASED]
OURS:   "We can ask which subgroups a cyclic group possesses."
JUDSON: "If $G$ is a cyclic group, what type of subgroups does $G$ possess?"
FIX:    "If $G$ is a cyclic group, what type of subgroups does $G$ possess?"

### aata/4.1:356  [PARAPHRASED / TRUNCATED]
OURS:   "**Proof.** The argument uses the division algorithm and well-ordering. Let
        $G = \langle a \rangle$ and let $H$ be a subgroup of $G$. If $H = \{e\}$ it is
        trivially cyclic. Otherwise $H$ contains some $g \neq e$, say $g = a^n$; since $H$ is
        a subgroup, $g^{-1} = a^{-n} \in H$ too, so $H$ contains a positive power of $a$. Let
        $m$ be the smallest natural number with $a^m \in H$ (it exists by well-ordering). We
        claim $h = a^m$ generates $H$: for any $h' = a^k \in H$, the division algorithm gives
        $k = mq + r$ with $0 \leq r < m$, so
        $$a^k = a^{mq+r} = (a^m)^q a^r = h^q a^r, \quad\text{hence}\quad a^r = a^k h^{-q}.$$
        Since $a^k \in H$ and $h^{-q} \in H$, we get $a^r \in H$; but $m$ was the least
        positive exponent with $a^m \in H$, so $r = 0$ and $k = mq$. Therefore
        $h' = a^k = (a^m)^q = h^q$, and $H$ is generated by $h$."
JUDSON: "The main tools used in this proof are the division algorithm and the Principle of
        Well-Ordering."
        "Let $G$ be a cyclic group generated by $a$ and suppose that $H$ is a subgroup of
        $G$. If $H = \{ e \}$, then trivially $H$ is cyclic. Suppose that $H$ contains some
        other element $g$ distinct from the identity. Then $g$ can be written as $a^n$ for
        some integer $n$. Since $H$ is a subgroup, $g^{-1} = a^{-n}$ must also be in $H$.
        Since either $n$ or $-n$ is positive, we can assume that $H$ contains positive powers
        of $a$ and $n \gt 0$. Let $m$ be the smallest natural number such that $a^m \in H$.
        Such an $m$ exists by the Principle of Well-Ordering."
        "We claim that $h = a^m$ is a generator for $H$. We must show that every
        $h' \in H$ can be written as a power of $h$. Since $h' \in H$ and $H$ is a subgroup
        of $G$, $h' = a^k$ for some integer $k$. Using the division algorithm, we can find
        numbers $q$ and $r$ such that $k = mq +r$ where $0 \leq r \lt m$; hence,
        $$a^k = a^{mq +r} = (a^m)^q a^r = h^q a^r.$$
        So $a^r = a^k h^{-q}$. Since $a^k$ and $h^{-q}$ are in $H$, $a^r$ must also be in
        $H$. However, $m$ was the smallest positive number such that $a^m$ was in $H$;
        consequently, $r=0$ and so $k=mq$. Therefore,
        $$h' = a^k = a^{mq} = h^q$$
        and $H$ is generated by $h$."
FIX:    Replace our condensed single-paragraph proof with Judson's three paragraphs above,
        verbatim. Ours rewrites essentially every sentence and drops three outright ("Since
        either $n$ or $-n$ is positive, we can assume that $H$ contains positive powers of
        $a$ and $n \gt 0$."; "We must show that every $h' \in H$ can be written as a power of
        $h$."; "Since $h' \in H$ and $H$ is a subgroup of $G$, $h' = a^k$ for some integer
        $k$.").

### aata/4.1:808  [NARRATION + TRUNCATED]
OURS:   "Having shown every $a^k \in H$ is a multiple power $(a^m)^q$,
        $H = \langle a^m \rangle$ is cyclic, generated by $h = a^m$. As a corollary, the
        subgroups of $\mathbb{Z}$ are exactly $n\mathbb{Z}$ for $n = 0, 1, 2, \ldots$."
JUDSON: (a stated corollary, not a trailing clause)
        "**Corollary.** The subgroups of ${\mathbb Z}$ are exactly $n{\mathbb Z}$ for
        $n = 0, 1, 2,\ldots$."
FIX:    Split in two. The first sentence is the real divergence (only "every $a^k \in H$ is a
        power of $a^m$" is reachable without a sort of subsets) — and since the :368 aside
        already says exactly that, it may simply be deleted. Then state the corollary in his
        own form:
        "**Corollary.** The subgroups of $\mathbb{Z}$ are exactly $n\mathbb{Z}$ for
        $n = 0, 1, 2, \ldots$."

### aata/4.1:1318  [NARRATION + TRUNCATED]
OURS:   "So $b = a^k$ has order $M_0 = n/d$ — it is killed by $M_0$ and by nothing smaller.
        As a corollary, the generators of $\mathbb{Z}_n$ are exactly the integers $r$ with
        $1 \leq r < n$ and $\gcd(r, n) = 1$; for example, every $r$ coprime to $16$ generates
        $\mathbb{Z}_{16}$."
JUDSON: (a stated corollary plus a worked example)
        "**Corollary.** The generators of ${\mathbb Z}_n$ are the integers $r$ such that
        $1 \leq r \lt n$ and $\gcd(r,n) = 1$."
        "**Example.** Let us examine the group ${\mathbb Z}_{16}$. The numbers $1$, $3$, $5$,
        $7$, $9$, $11$, $13$, and $15$ are the elements of ${\mathbb Z}_{16}$ that are
        relatively prime to $16$. Each of these elements generates ${\mathbb Z}_{16}$. For
        example,
        $$\begin{aligned} 1 \cdot 9 &= 9 & 2 \cdot 9 &= 2 & 3 \cdot 9 &= 11 \\ 4 \cdot 9 &= 4 & 5 \cdot 9 &= 13 & 6 \cdot 9 &= 6 \\ 7 \cdot 9 &= 15 & 8 \cdot 9 &= 8 & 9 \cdot 9 &= 1 \\ 10 \cdot 9 &= 10 & 11 \cdot 9 &= 3 & 12 \cdot 9 &= 12 \\ 13 \cdot 9 &= 5 & 14 \cdot 9 &= 14 & 15 \cdot 9 &= 7 \end{aligned}.$$"
FIX:    Keep the first clause ("So $b = a^k$ has order $M_0 = n/d$ — it is killed by $M_0$
        and by nothing smaller.") as a proof-block closer, then state the corollary and the
        example in Judson's own words as quoted (the example is a concrete computation
        needing no proof block).

### NOT defects

- **:1035** — our Theorem 4.13 proof ("We seek the smallest $M$ with $e = b^M = a^{kM}$. By
  the previous proposition this is the smallest $M$ such that $n \mid kM$, or equivalently
  $(n/d) \mid M(k/d)$. …") tracks his sentence-for-sentence with $m$ renamed $M$ (a renamed
  symbol, covered by the transcription exception) and his last two sentences joined by a
  semicolon. Faithful transliteration.
- **:816** — our Proposition 4.12 proof is verbatim-faithful.
- **:1041, :1051, :1144** — the cofactor paragraphs. These do not displace Judson's text —
  his proof sits verbatim at :1035 directly above — and each states a real mechanisation
  divergence: with no $\gcd$ function and no $n/d$ division, the cofactors enter as declared
  constants with a Bézout identity, and "the order of $b$ is $n/d$" splits into a kills-half
  and a minimal-half. Should be `>` asides on style; they replace nothing. Borderline style,
  not fidelity defects.
- **:1322** — the closing aside. Legitimate.

**4 defects** (2 PARAPHRASED, 2 NARRATION+TRUNCATED).

---

## aata/5.1-permutation-groups.md

This file carries Judson's definitions, his Theorem 5.1 statement and proof, the
right-to-left convention paragraph, the cycle definition, the transposition definition and
the no-unique-representation paragraph verbatim. But four substantial pieces of his text
were replaced with narration, and several blocks of examples plus a whole theorem are
missing.

### aata/5.1 (missing around :47 and after :476)  [TRUNCATED]
OURS:   "A subgroup of $S_n$ is called a **permutation group**." is followed immediately by
        "### Cycle Notation"; and the convention paragraph at :47–54 ends at "… by
        $\sigma\tau(x)$ we mean $\sigma(\tau(x))$."
JUDSON: "**Example.** Consider the subgroup $G$ of $S_5$ consisting of the identity
        permutation $\identity$ and the permutations
        $$\begin{aligned} \sigma &= \begin{pmatrix} 1 & 2 & 3 & 4 & 5 \\ 1 & 2 & 3 & 5 & 4 \end{pmatrix} \\ \tau &= \begin{pmatrix} 1 & 2 & 3 & 4 & 5 \\ 3 & 2 & 1 & 4 & 5 \end{pmatrix} \\ \mu &= \begin{pmatrix} 1 & 2 & 3 & 4 & 5 \\ 3 & 2 & 1 & 5 & 4 \end{pmatrix} \end{aligned}.$$
        The following table tells us how to multiply elements in the permutation group $G$.
        $$\begin{array}{c|cccc} \circ & \identity & \sigma & \tau & \mu \\ \hline \identity & \identity & \sigma & \tau & \mu \\ \sigma & \sigma & \identity & \mu & \tau \\ \tau & \tau & \mu & \identity & \sigma \\ \mu & \mu & \tau & \sigma & \identity \end{array}$$"
        Dropped parenthetical from the convention paragraph: "(Another way of solving this
        problem would be to write functions on the right; that is, instead of writing
        $\sigma(x)$, we could write $(x)\sigma$. We could also multiply permutations left to
        right to agree with the usual way of multiplying elements in a group. Certainly all
        of these methods have been used.)"
        Dropped example: "**Example.** Permutation multiplication is not usually commutative.
        Let
        $$\begin{aligned} \sigma &= \begin{pmatrix} 1 & 2 & 3 & 4 \\ 4 & 1 & 2 & 3 \end{pmatrix} \\ \tau &= \begin{pmatrix} 1 & 2 & 3 & 4 \\ 2 & 1 & 4 & 3 \end{pmatrix} \end{aligned}.$$
        Then
        $$\sigma \tau = \begin{pmatrix} 1 & 2 & 3 & 4 \\ 1 & 4 & 3 & 2 \end{pmatrix},$$
        but
        $$\tau \sigma = \begin{pmatrix} 1 & 2 & 3 & 4 \\ 3 & 2 & 1 & 4 \end{pmatrix}.$$"
FIX:    Restore the parenthetical into the convention paragraph; insert the
        non-commutativity example after it; insert the $S_5$ example after "A subgroup of
        $S_n$ is called a **permutation group**." All three are concrete, needing no proof
        blocks.

### aata/5.1 (missing before :492)  [TRUNCATED]
OURS:   Our cycle definition paragraph ends "… Two cycles $\sigma, \tau \in S_X$ are
        **disjoint** if …" and is followed immediately by the propositions blockquote.
JUDSON: Five paragraphs of worked cycle examples are dropped, as is his own disjointness
        definition:
        "**Example.** The permutation
        $$\sigma = \begin{pmatrix} 1 & 2 & 3 & 4 & 5 & 6 & 7 \\ 6 & 3 & 5 & 1 & 4 & 2 & 7 \end{pmatrix} = (1\, 6\, 2\, 3\, 5\, 4)$$
        is a cycle of length $6$, whereas
        $$\tau = \begin{pmatrix} 1 & 2 & 3 & 4 & 5 & 6 \\ 1 & 4 & 2 & 3 & 5 & 6 \end{pmatrix} = (2\, 4\, 3)$$
        is a cycle of length $3$."
        "Not every permutation is a cycle. Consider the permutation
        $$\begin{pmatrix} 1 & 2 & 3 & 4 & 5 & 6 \\ 2 & 4 & 1 & 3 & 6 & 5 \end{pmatrix} = (1\, 2\, 4\, 3)(5\, 6).$$
        This permutation actually contains a cycle of length $2$ and a cycle of length $4$."
        "**Example.** It is very easy to compute products of cycles. Suppose that
        $$\sigma = (1\, 3\, 5\, 2 ) \quad \text{and} \quad \tau = (2\, 5\, 6).$$
        If we think of $\sigma$ as
        $$1 \mapsto 3, \qquad 3 \mapsto 5, \qquad 5 \mapsto 2, \qquad 2 \mapsto 1,$$
        and $\tau$ as
        $$2 \mapsto 5, \qquad 5 \mapsto 6, \qquad 6 \mapsto 2,$$
        then for $\sigma \tau$ remembering that we apply $\tau$ first and then $\sigma$, it
        must be the case that
        $$1 \mapsto 3, \qquad 3 \mapsto 5, \qquad 5 \mapsto 6, \qquad 6 \mapsto 2 \mapsto 1,$$
        or $\sigma \tau = (1 \, 3 \, 5 \, 6)$. If $\mu = (1 \, 6 \, 3 \, 4)$, then
        $\sigma \mu = (1\, 6\, 5\, 2)(3\, 4)$."
        "Two cycles in $S_X$, $\sigma = (a_1, a_2, \ldots, a_k )$ and
        $\tau = (b_1, b_2, \ldots, b_l )$, are **disjoint** if $a_i \neq b_j$ for all $i$ and
        $j$."
        "**Example.** The cycles $(1\, 3\, 5)$ and $(2\, 7)$ are disjoint; however, the
        cycles $(1\, 3\, 5)$ and $(3\, 4\, 7)$ are not. Calculating their products, we find
        that
        $$\begin{aligned} (1\, 3\, 5)(2\, 7 ) &= (1\, 3\, 5)(2\, 7 ) \\ (1\, 3\, 5)(3\, 4\, 7 ) &= (1\, 3\, 4\, 7\, 5) \end{aligned}.$$
        The product of two cycles that are not disjoint may reduce to something less
        complicated; the product of disjoint cycles cannot be simplified."
FIX:    Insert those five paragraphs verbatim. Note our disjointness clause ("Two cycles
        $\sigma, \tau \in S_X$ are **disjoint** if $a \neq \sigma(a)$ implies $\tau(a) = a$,
        and $b \neq \tau(b)$ implies $\sigma(b) = b$.") is a *restatement* of his index-form
        definition in support terms — defensible as a notation divergence, but it should be
        declared in a `>` aside, with his own sentence carried first.

### aata/5.1:498  [NARRATION]
OURS:   "A cycle $(a_0\, a_1 \ldots a_k)$ is taken in the factorized form established further
        down, $(a_0\, a_1 \ldots a_k) = (a_0\, a_k) \cdots (a_0\, a_2)(a_0\, a_1)$, and the
        action Judson uses as his definition — advance, wrap around, fix the rest — is then
        proved of it for a list of distinct points. Two cycles are disjoint exactly when their
        supports, the sets of points they move, do not meet; the proposition in fact holds for
        any two permutations with disjoint supports, cycles or not. The decomposition theorem
        is proved for a permutation moving finitely many points, which is what
        $\sigma \in S_n$ means, by Judson's argument: peel off the cycle of one orbit, and
        induct on the size of the support."
JUDSON: His two PROOFS, which our file carries nowhere:
        (Proposition 5.8) "Let $\sigma = (a_1, a_2, \ldots, a_k )$ and
        $\tau = (b_1, b_2, \ldots, b_l )$. We must show that $\sigma \tau(x) = \tau \sigma(x)$
        for all $x \in X$. If $x$ is neither in $\{ a_1, a_2, \ldots, a_k \}$ nor
        $\{b_1, b_2, \ldots, b_l \}$, then both $\sigma$ and $\tau$ fix $x$. That is,
        $\sigma(x)=x$ and $\tau(x)=x$. Hence,
        $$\sigma \tau(x) = \sigma( \tau(x)) = \sigma(x) = x = \tau(x) = \tau( \sigma(x)) = \tau \sigma(x).$$
        Do not forget that we are multiplying permutations right to left, which is the
        opposite of the order in which we usually multiply group elements. Now suppose that
        $x \in \{ a_1, a_2, \ldots, a_k \}$. Then $\sigma( a_i ) = a_{(i \bmod k) + 1}$; that
        is,
        $$\begin{aligned} a_1 &\mapsto a_2 \\ a_2 &\mapsto a_3 \\ &\ \vdots \\ a_{k-1} &\mapsto a_k \\ a_k &\mapsto a_1 \end{aligned}.$$
        However, $\tau(a_i) = a_i$ since $\sigma$ and $\tau$ are disjoint. Therefore,
        $$\begin{aligned} \sigma \tau(a_i) &= \sigma( \tau(a_i)) \\ &= \sigma(a_i) \\ &= a_{(i \bmod k)+1} \\ &= \tau( a_{(i \bmod k)+1} ) \\ &= \tau( \sigma(a_i) ) \\ &= \tau \sigma(a_i) \end{aligned}.$$
        Similarly, if $x \in \{b_1, b_2, \ldots, b_l \}$, then $\sigma$ and $\tau$ also
        commute."
        (Theorem 5.9) "We can assume that $X = \{ 1, 2, \ldots, n \}$. If $\sigma \in S_n$
        and we define $X_1$ to be $\{ \sigma(1), \sigma^2(1), \ldots \}$, then the set $X_1$
        is finite since $X$ is finite. Now let $i$ be the first integer in $X$ that is not in
        $X_1$ and define $X_2$ by $\{ \sigma(i), \sigma^2(i), \ldots \}$. Again, $X_2$ is a
        finite set. Continuing in this manner, we can define finite disjoint sets
        $X_3, X_4, \ldots$. Since $X$ is a finite set, we are guaranteed that this process
        will end and there will be only a finite number of these sets, say $r$. If $\sigma_i$
        is the cycle defined by
        $$\sigma_i( x ) = \begin{cases} \sigma( x ) & x \in X_i \\ x & x \notin X_i \end{cases},$$
        then $\sigma = \sigma_1 \sigma_2 \cdots \sigma_r$. Since the sets
        $X_1, X_2, \ldots, X_r$ are disjoint, the cycles $\sigma_1, \sigma_2, \ldots, \sigma_r$
        must also be disjoint."
        And the example that follows: "**Example.** Let
        $$\begin{aligned} \sigma &= \begin{pmatrix} 1 & 2 & 3 & 4 & 5 & 6 \\ 6 & 4 & 3 & 1 & 5 & 2 \end{pmatrix} \\ \tau &= \begin{pmatrix} 1 & 2 & 3 & 4 & 5 & 6 \\ 3 & 2 & 1 & 5 & 6 & 4 \end{pmatrix} \end{aligned}.$$
        Using cycle notation, we can write
        $$\begin{aligned} \sigma &= (1 \, 6 \, 2 \, 4) \\ \tau &= (1 \, 3)(4 \, 5 \,6) \\ \sigma \tau &= (1 \, 3\, 6) ( 2\, 4\, 5) \\ \tau \sigma &= (1 \, 4\, 3 )(2 \, 5 \, 6) \end{aligned}.$$"
        And: "From this point forward we will find it convenient to use cycle notation to
        represent permutations. When using cycle notation, we often denote the identity
        permutation by $(1)$."
FIX:    Carry both of Judson's proofs verbatim (as `**Proof.**` paragraphs under each
        statement), plus the example and the cycle-notation remark. Then reduce our paragraph
        to a `>` aside stating only the genuine divergences — that a cycle is carried in its
        transposition-factored form, that disjointness is expressed through supports (so the
        proposition generalises to any two permutations with disjoint supports), and that
        "$\sigma \in S_n$" becomes "finite support". Strike the "Judson's argument" and "the
        action Judson uses as his definition" narration.

### aata/5.1:766  [NARRATION]
OURS:   "The displayed identity is the form a cycle is taken in, one transposition at a time,
        so a cycle is a product of transpositions by construction; and the proposition follows
        from the decomposition into disjoint cycles by concatenating each cycle's
        transpositions. The "at least two elements" is not needed: the identity is the empty
        product. Below, the parity results take "a product of transpositions" as a hypothesis
        about a permutation, and this proposition is what discharges it for every permutation
        of a finite set."
JUDSON: none for the argument — Judson gives no proof of Proposition 5.12; the displayed
        identity before the statement IS his justification, and ours carries it verbatim at
        :757–762.
FIX:    Wrap as a `>` aside. The "at least two elements is not needed" clause is a real
        declared divergence; the rest is scaffolding:
        "> *A cycle is carried here in its transposition-factored form, so it is a product of
        > transpositions by construction, and the proposition follows from the decomposition
        > into disjoint cycles by concatenating each cycle's transpositions. Judson's
        > "containing at least two elements" is not needed: the identity is the empty product.
        > The parity results below take "a product of transpositions" as a hypothesis about a
        > permutation, and this proposition discharges it for every permutation of a finite
        > set.*"

### aata/5.1:792  [NARRATION]
OURS:   "Judson proves this in two moves: first a lemma about the identity, then the general
        statement."
JUDSON: none — no counterpart.
FIX:    Delete. The lemma and theorem that follow are self-labelling, and Judson's own
        structure sentence ("However, as it turns out, no permutation can be written as the
        product of both an even number …") is already carried at :785–790.

### aata/5.1:798  [PARAPHRASED / TRUNCATED]
OURS:   "**Proof.** Induct on $r$, rewriting the last two transpositions by one of four
        identities — $(ab)(ab) = \identity$, $(bc)(ab) = (ac)(bc)$, $(cd)(ab) = (ab)(cd)$,
        $(ac)(ab) = (ab)(bc)$ — so that either the product shortens by two or the last
        occurrence of a symbol $a$ moves one place left. Repeating, either two adjacent
        transpositions cancel or $a$ reaches the first position, which is impossible because
        the identity fixes $a$."
JUDSON: "We will employ induction on $r$. A transposition cannot be the identity; hence,
        $r \gt 1$. If $r=2$, then we are done. Suppose that $r \gt 2$. In this case the
        product of the last two transpositions, $\tau_{r-1} \tau_r$, must be one of the
        following cases:
        $$\begin{aligned} (a, b)(a, b) &= \identity \\ (b, c)(a, b) &= (a, c)(b, c) \\ (c, d)(a, b) &= (a, b)(c, d) \\ (a, c)(a, b) &= (a, b)(b, c) \end{aligned},$$
        where $a$, $b$, $c$, and $d$ are distinct."
        "The first equation simply says that a transposition is its own inverse. If this case
        occurs, delete $\tau_{r-1} \tau_r$ from the product to obtain
        $$\identity = \tau_1 \tau_2 \cdots \tau_{r - 3} \tau_{r - 2}.$$
        By induction $r - 2$ is even; hence, $r$ must be even."
        "In each of the other three cases, we can replace $\tau_{r - 1} \tau_r$ with the
        right-hand side of the corresponding equation to obtain a new product of $r$
        transpositions for the identity. In this new product the last occurrence of $a$ will
        be in the next-to-the-last transposition. We can continue this process with
        $\tau_{r - 2} \tau_{r - 1}$ to obtain either a product of $r - 2$ transpositions or a
        new product of $r$ transpositions where the last occurrence of $a$ is in
        $\tau_{r - 2}$. If the identity is the product of $r - 2$ transpositions, then again
        we are done, by our induction hypothesis; otherwise, we will repeat the procedure with
        $\tau_{r - 3} \tau_{r - 2}$. At some point either we will have two adjacent, identical
        transpositions canceling each other out or $a$ will be shuffled so that it will appear
        only in the first transposition. However, the latter case cannot occur, because the
        identity would not fix $a$ in this instance. Therefore, the identity permutation must
        be the product of $r-2$ transpositions and, again by our induction hypothesis, we are
        done."
FIX:    Replace our four-line summary with Judson's three paragraphs above, verbatim. (The
        `>` aside at :805 already declares the nested-induction divergence and stays as is.)

### aata/5.1:1530  [NARRATION]
OURS:   "**Proof.** Three lines, one per subgroup condition, each resting only on the parity
        theory above — no cycle structure, no counting."
JUDSON: "Since the product of two even permutations must also be an even permutation, $A_n$
        is closed. The identity is an even permutation and therefore is in $A_n$. If $\sigma$
        is an even permutation, then $\sigma = \sigma_1 \sigma_2 \cdots \sigma_r$, where
        $\sigma_i$ is a transposition and $r$ is even. Since the inverse of any transposition
        is itself, $\sigma^{-1} = \sigma_r \sigma_{r-1} \cdots \sigma_1$ is also in $A_n$."
FIX:    "**Proof.** Since the product of two even permutations must also be an even
        permutation, $A_n$ is closed. The identity is an even permutation and therefore is in
        $A_n$. If $\sigma$ is an even permutation, then
        $\sigma = \sigma_1 \sigma_2 \cdots \sigma_r$, where $\sigma_i$ is a transposition and
        $r$ is even. Since the inverse of any transposition is itself,
        $\sigma^{-1} = \sigma_r \sigma_{r-1} \cdots \sigma_1$ is also in $A_n$.
        $\blacksquare$"

### aata/5.1:1857  [PARAPHRASED]
OURS:   "**Proof.** Fix the transposition $\sigma = (0\ 1)$. The map
        $\lambda_\sigma(\tau) = \sigma\tau$ carries the even permutations to the odd ones and
        back, so the two must contain the same number of elements. Splitting the listing of
        $S_n$ into its even entries — a listing of $A_n$, of length $p$ — and its non-even
        entries, of length $q$ with $p + q = n!$, the pairing gives $p = q$ and hence
        $2p = n!$: every $\sigma\tau$ with $\tau$ even is a non-even entry, and every non-even
        entry $\rho$ is $\sigma(\sigma\rho)$ with $\sigma\rho$ even. Two facts from the
        earlier sections feed this: every permutation of $n$ letters is even or odd, since it
        has finite support and so is a product of transpositions whose count is even or odd;
        and none is both, since $2$ does not divide two consecutive numbers. And
        $\lambda_\sigma$ flips parity, since prepending $\sigma$ to a product of $m$
        transpositions gives a product of $m+1$."
JUDSON: "Let $A_n$ be the set of even permutations in $S_n$ and $B_n$ be the set of odd
        permutations. If we can show that there is a bijection between these sets, they must
        contain the same number of elements. Fix a transposition $\sigma$ in $S_n$. Since
        $n \geq 2$, such a $\sigma$ exists. Define
        $$\lambda_{\sigma} : A_n \rightarrow B_n$$
        by $\lambda_{\sigma} ( \tau ) = \sigma \tau$. Suppose that
        $\lambda_{\sigma} ( \tau ) = \lambda_{\sigma} ( \mu )$. Then
        $\sigma \tau = \sigma \mu$ and so
        $\tau = \sigma^{-1} \sigma \tau = \sigma^{-1} \sigma \mu = \mu$. Therefore,
        $\lambda_{\sigma}$ is one-to-one. We will leave the proof that $\lambda_{\sigma}$ is
        surjective to the reader."
FIX:    Carry Judson's proof verbatim as the `**Proof.**` paragraph (including his accepted
        forwarding sentence "We will leave the proof that $\lambda_\sigma$ is surjective to
        the reader."), then keep our material as a following `>` aside, since the listing
        re-expression IS a real divergence:
        "> *With no cardinality function, "the same number of elements" is a pair of
        > listings: $S_n$'s listing splits into its even entries — a listing of $A_n$, of
        > length $p$ — and its non-even entries, of length $q$ with $p + q = n!$, and the
        > pairing gives $p = q$, hence $2p = n!$. Two facts feed this: every permutation of
        > $n$ letters is even or odd, since it has finite support and so is a product of
        > transpositions whose count is even or odd; and none is both, since $2$ does not
        > divide two consecutive numbers. The transposition is fixed as $(0\ 1)$ rather than
        > chosen, and $\lambda_\sigma$ flips parity because prepending $\sigma$ to a product
        > of $m$ transpositions gives a product of $m+1$.*"

### aata/5.1:3571  [NARRATION — a whole theorem replaced]
OURS:   "Given the lemma, parity is well defined."
JUDSON: (Theorem 5.16 — statement and proof, both absent from the file's prose)
        "**Theorem.** If a permutation $\sigma$ can be expressed as the product of an even
        number of transpositions, then any other product of transpositions equaling $\sigma$
        must also contain an even number of transpositions. Similarly, if $\sigma$ can be
        expressed as the product of an odd number of transpositions, then any other product
        of transpositions equaling $\sigma$ must also contain an odd number of
        transpositions."
        "**Proof.** Suppose that
        $$\sigma = \sigma_1 \sigma_2 \cdots \sigma_m = \tau_1 \tau_2 \cdots \tau_n,$$
        where $m$ is even. We must show that $n$ is also an even number. The inverse of
        $\sigma$ is $\sigma_m \cdots \sigma_1$. Since
        $$\identity = \sigma \sigma_m \cdots \sigma_1 = \tau_1 \cdots \tau_n \sigma_m \cdots \sigma_1,$$
        $n$ must be even by Lemma 5.15. The proof for the case in which $\sigma$ can be
        expressed as an odd number of transpositions is left as an exercise."
        "In light of Theorem 5.16, we define a permutation to be **even** if it can be
        expressed as an even number of transpositions and **odd** if it can be expressed as
        an odd number of transpositions."
FIX:    Replace "Given the lemma, parity is well defined." with Judson's theorem statement
        (as a `> **Theorem.**` blockquote matching the file's convention), his `**Proof.**`
        paragraph, and the "In light of …" definition paragraph, all verbatim as quoted. The
        `>` aside that currently follows at :3573 then reads correctly. NOTE: this theorem
        statement is MISSING ENTIRELY — the file proves it in a `2b4m` block at :1420+ but
        never states it in prose, and the definitions of **even** and **odd** permutation,
        which the rest of the file and the whole of §10.2 depend on, are never given.

### aata/5.1 (missing after :3577, end of file)  [TRUNCATED]
OURS:   File ends with the `>` aside about the two spelled-out steps.
JUDSON: "**Example.** The group $A_4$ is the subgroup of $S_4$ consisting of even
        permutations. There are twelve elements in $A_4$:
        $$\begin{aligned} &(1) && (1 \, 2)(3 \, 4) && (1 \, 3)(2 \, 4) && (1 \, 4)(2 \, 3) \\ &(1 \, 2 \, 3) && (1 \, 3 \, 2) && (1 \, 2 \, 4) && (1 \, 4 \, 2) \\ &(1 \, 3 \, 4) && (1 \, 4 \, 3) && (2 \, 3 \, 4) && (2 \, 4 \, 3) \end{aligned}.$$
        One of the end-of-chapter exercises will be to write down all the subgroups of $A_4$.
        You will find that there is no subgroup of order 6. Does this surprise you?"
        (plus the Historical Note on Cauchy — treat consistently with whatever the
        corpus-wide ruling on Historical Notes is; no other file in this group carries one.)
FIX:    Append the $A_4$ example verbatim at the end of the file.

### NOT defects

- **:177** — "**The $n!$ elements.** A permutation of $n$ letters bijects the segment
  $\{0, \ldots, n-1\}$ onto itself …". This is OUR proof of what Judson explicitly leaves as
  an exercise ("We leave the proof that $|S_n|= n!$ as an exercise.", carried verbatim at
  :154). Nothing of his is displaced. Should be a `>` aside on style, but legitimate content.
  NO-SOURCE / legitimate.

**9 defects** (2 PARAPHRASED, 4 NARRATION, 3 TRUNCATED).

---

## aata/6.1-cosets.md

This file transliterates Judson's §6.1 statements and proofs faithfully — the coset
definition, Lemma 6.3's five conditions, Theorem 6.4's statement and full proof, the
"nothing special about left cosets" remark, the index definition, and Theorem 6.8's
statement and full proof are all verbatim. What is missing is the chapter opening and his
examples.

### aata/6.1 (missing before :14)  [TRUNCATED]
OURS:   File opens with the attribution header, the coset-as-predicate `>` aside, then
        "## Definition".
JUDSON: "Lagrange's Theorem, one of the most important results in finite group theory, states
        that the order of a subgroup must divide the order of the group. This theorem provides
        a powerful tool for analyzing finite groups; it gives us an idea of exactly what type
        of subgroups we might expect a finite group to possess. Central to understanding
        Lagrange's Theorem is the notion of a coset."
FIX:    Insert that paragraph after the attribution header, before the `>` aside.

### aata/6.1:57  [PARAPHRASED / TRUNCATED]
OURS:   "In a commutative group, left and right cosets are always identical. It is not always
        the case that a left coset is the same as a right coset: in $S_3$ the subgroup
        $H = \{(1), (1\,2\,3), (1\,3\,2)\}$ has its left and right cosets coinciding, while
        $K = \{(1), (1\,2)\}$ does not."
JUDSON: (one remark plus three full examples, all compressed into our two sentences)
        "**Example.** Let $H$ be the subgroup of ${\mathbb Z}_6$ consisting of the elements
        $0$ and $3$. The cosets are
        $$\begin{aligned} 0 + H = 3 + H &= \{ 0, 3 \} \\ 1 + H = 4 + H &= \{ 1, 4 \} \\ 2 + H = 5 + H &= \{ 2, 5 \} \end{aligned}.$$
        We will always write the cosets of subgroups of ${\mathbb Z}$ and ${\mathbb Z}_n$ with
        the additive notation we have used for cosets here. In a commutative group, left and
        right cosets are always identical."
        "**Example.** Let $H$ be the subgroup of $S_3$ defined by the permutations
        $\{(1), (1 \, 2 \, 3), (1 \, 3 \, 2) \}$. The left cosets of $H$ are
        $$\begin{aligned} (1)H = (1 \, 2 \, 3)H = (1 \, 3 \, 2)H &= \{(1), (1 \, 2 \, 3), (1 \, 3 \, 2) \} \\ (1 \, 2)H = (1 \, 3)H = (2 \, 3)H &= \{ (1 \, 2), (1 \, 3), (2 \, 3) \} \end{aligned}.$$
        The right cosets of $H$ are exactly the same as the left cosets:
        $$\begin{aligned} H(1) = H(1 \, 2 \, 3) = H(1 \, 3 \, 2) &= \{(1), (1 \, 2 \, 3), (1 \, 3 \, 2) \} \\ H(1 \, 2) = H(1 \, 3) = H(2 \, 3) &= \{ (1 \, 2), (1 \, 3), (2 \, 3) \} \end{aligned}.$$
        It is not always the case that a left coset is the same as a right coset. Let $K$ be
        the subgroup of $S_3$ defined by the permutations $\{(1), (1 \, 2)\}$. Then the left
        cosets of $K$ are
        $$\begin{aligned} (1)K = (1 \, 2)K &= \{(1), (1 \, 2)\} \\ (1 \, 3)K = (1 \, 2 \, 3)K &= \{(1 \, 3), (1 \, 2 \, 3)\} \\ (2 \, 3)K = (1 \, 3 \, 2)K &= \{(2 \, 3), (1 \, 3 \, 2)\} \end{aligned};$$
        however, the right cosets of $K$ are
        $$\begin{aligned} K(1) = K(1 \, 2) &= \{(1), (1 \, 2)\} \\ K(1 \, 3) = K(1 \, 3 \, 2) &= \{(1 \, 3), (1 \, 3 \, 2)\} \\ K(2 \, 3) = K(1 \, 2 \, 3) &= \{(2 \, 3), (1 \, 2 \, 3)\} \end{aligned}.$$"
FIX:    Replace our two-sentence summary with Judson's two example paragraphs verbatim as
        quoted (concrete computations; no proof blocks needed).

### aata/6.1 (missing before :367)  [TRUNCATED]
OURS:   The Lemma 6.3 proof blocks are followed directly by "## Theorem 6.4 — the cosets
        partition the group".
JUDSON: "In all of our examples the cosets of a subgroup $H$ partition the larger group $G$.
        The following theorem proclaims that this will always be the case."
FIX:    Insert that sentence pair before the Theorem 6.4 heading. (It only reads correctly
        once :57's examples are restored — "In all of our examples" has no referent
        otherwise.)

### aata/6.1 (missing after :467)  [TRUNCATED]
OURS:   The index definition is followed directly by the Theorem 6.7 statement.
JUDSON: "**Example.** Let $G= {\mathbb Z}_6$ and $H = \{ 0, 3 \}$. Then $[G:H] = 3$."
        "**Example.** Suppose that $G= S_3$, $H = \{ (1),(1 \, 2 \, 3), (1 \, 3 \, 2) \}$,
        and $K= \{ (1), (1 \, 2) \}$. Then $[G:H] = 2$ and $[G:K] = 3$."
FIX:    Insert both examples verbatim between the index definition and the Theorem 6.7
        statement.

### NOT defects

- **:71** — "Every element lies in its own coset — the fact that makes the cosets *cover*
  $G$." A proof-block label for `elementIsInItsOwnCoset`. Judson never states this as a
  result (it is implicit in his set-theoretic partition argument), so it is ours by
  necessity: with cosets as predicates, the covering half of "partition" must be proved
  separately. Legitimately needed; ideally a `>` aside.
- **:113** — "Judson leaves the proof as an exercise. …" — accepted forwarding language per
  the brief, and his own parenthetical is "(We leave its proof as an exercise.)", so the
  first sentence is faithful. The remainder is a real divergence note: only one of the five
  equivalences is reachable as stated. Not flagged.
- **:380** — "A shared element forces the two cosets to agree everywhere; together with the
  fact that every element lies in its own coset, this is the partition." Judson's proof is
  verbatim above at :373–378; this says how the two `2b4m` results compose into "partition"
  when a partition cannot be named. Legitimate divergence note.
- **:481** — "Both directions of $\phi$ appeal to the same fact, the right-coset analogue of
  Lemma 6.3 …". Judson's Theorem 6.7 proof is verbatim above at :472–479, and the `>` aside
  at :590 already declares that $\phi$ itself cannot be named. Legitimate.
- **:580, :803** — forward bridges to §6.2's Lemma 6.6 (the $H \to gH$ bijection). That
  lemma is in §6.2 of cosets.xml (past line 244, this file's declared scope), so it is NOT
  missing from §6.1 — honest "taken up in §6.2" pointers for results proved here because
  the std library needed them. Legitimate; the §6.2 agent should confirm Lemma 6.6 is stated
  there.

**4 defects** (1 PARAPHRASED, 3 TRUNCATED).

---

## aata/6.3-fermat-and-eulers-theorems.md

### aata/6.3 (missing before :17)  [TRUNCATED]
OURS:   The φ-function definition is followed directly by "**Theorem 6.15.** Let $U(n)$ be
        the group of units in $\mathbb{Z}_n$. Then $|U(n)| = \varphi(n)$."
JUDSON: "From Theorem 6.10, we know that the order of $U(n)$, the group of units in
        ${\mathbb Z}_n$, is $\phi(n)$."
        "For example, $|U(12)| = \phi(12) = 4$ since the numbers that are relatively prime to
        12 are $1$, $5$, $7$, and $11$. For any prime $p$, $\phi(p) = p-1$."
        "We state these results in the following theorem."
FIX:    Insert those three paragraphs verbatim between the definition and the Theorem 6.15
        statement — which also reorders our file to match his (our :32 currently places the
        $U(12)$ example AFTER the theorem and its proof block; it belongs before).

### aata/6.3:19  [NARRATION]
OURS:   "As in §6.2 a count is a listing rather than a cardinal, so "$|U(n)| = \varphi(n)$"
        becomes: splitting $\mathbb{Z}_n$'s listing at the units lists them without
        repetition, and that length is what $\varphi(n)$ names."
JUDSON: none — no counterpart.
FIX:    Wrap as a `>` aside — a real divergence (no cardinality function):
        "> *As in §6.2 a count is a listing rather than a cardinal, so
        > "$|U(n)| = \varphi(n)$" becomes: splitting $\mathbb{Z}_n$'s listing at the units
        > lists them without repetition, and that length is what $\varphi(n)$ names.*"

### aata/6.3 (missing before :37)  [TRUNCATED]
OURS:   Our "## Theorem 6.16 — Euler's Theorem" heading follows the $U(12)$ example.
JUDSON: "The following theorem is an important result in number theory, due to Leonhard
        Euler."
FIX:    Insert that sentence before the Euler's Theorem statement.

### aata/6.3:43  [NARRATION]
OURS:   "The group-theoretic fact behind this is that **an element raised to the size of its
        group is the identity**, which holds in any finite group. Euler's congruence is what
        it says when the group is $U(n)$, where the size is $\varphi(n)$ and the identity
        is 1."
JUDSON: none — no counterpart. His proof is verbatim above at :39–41.
FIX:    Wrap as a `>` aside — the generalisation to "any finite group" is the shape the
        mechanisation actually takes:
        "> *What is proved here is the group-theoretic fact behind the congruence — an element
        > raised to the size of its group is the identity, in any finite group. Euler's
        > congruence is what it says when the group is $U(n)$, where the size is $\varphi(n)$
        > and the identity is 1.*"

### aata/6.3:151  [NARRATION]
OURS:   "The step Judson compresses into "consequently" is the engine, isolated:"
JUDSON: none — no counterpart. (His "Consequently, $a^{\phi(n)} = 1$ for all $a \in U(n)$ …"
        is carried verbatim at :40.)
FIX:    Wrap as a `>` aside with the narration struck:
        "> *The step behind "consequently" — that a multiple of an element's order is an
        > identity exponent — is isolated below.*"

### aata/6.3:255  [PARAPHRASED]
OURS:   "Fermat is the special case of Euler's Theorem with $n = p$ prime, using
        $\varphi(p) = p - 1$ — that is, that exactly the $p-1$ classes $1, \ldots, p-1$ are
        units modulo a prime."
JUDSON: "If we consider the special case of Euler's Theorem in which $n = p$ is prime and
        recall that $\phi(p) = p - 1$, we obtain the following result, due to Pierre de
        Fermat."
FIX:    Move Judson's sentence BEFORE the Theorem 6.17 statement, verbatim: "If we consider
        the special case of Euler's Theorem in which $n = p$ is prime and recall that
        $\varphi(p) = p - 1$, we obtain the following result, due to Pierre de Fermat."
        Keep our added clause only inside the `>` aside at :261, which already declares that
        count unavailable.

### aata/6.3:263  [NO-SOURCE]
OURS:   "Note that $b^p \equiv b \pmod p$ is the extension to *every* $b$: where
        $p \nmid b$ it follows from $b^{p-1} \equiv 1$ by multiplying through by $b$, and
        where $p \mid b$ both sides are $0$."
JUDSON: none — no counterpart. Judson states "Furthermore, for any integer $b$,
        $b^p \equiv b \pmod{ p}$." (carried at :253) and gives no justification; §6.3 ends
        there.
FIX:    Delete (preferred — it ends the file on commentary where Judson ends on his own
        sentence), or wrap as a `>` aside. It is our gloss on his final clause, not a
        divergence note and not a proof of anything in the file; the `>` aside at :261
        already says Fermat's congruence is recorded as prose only.

### NOT defects

- **:240** — "And the divisibility it rests on is Corollary 6.10 from §6.2:" — a one-line
  label for the `fact` re-export immediately below. Scaffolding, legitimately needed; ideally
  a code comment rather than prose.

**7 defects** (1 PARAPHRASED, 3 NARRATION, 2 TRUNCATED, 1 NO-SOURCE).

---

## Summary

| file | TRUNCATED | PARAPHRASED | NARRATION | NO-SOURCE | total |
|---|---|---|---|---|---|
| 1.2.2-functions.md | 0 | 0 | 0 | 0 | **0** |
| 10.1-factor-groups-and-normal-subgroups.md | 3 | 1 | 3 | 0 | **7** |
| 11.2-the-isomorphism-theorems.md | 6 | 2 | 6 | 1 | **15** |
| 3.1-integers-mod-n.md | 2 | 0 | 0 | 1 | **3** |
| 3.3-subgroups.md | 2 | 1 | 0 | 0 | **3** |
| 4.1-cyclic-subgroups.md | 0 | 2 | 2 | 0 | **4** |
| 5.1-permutation-groups.md | 3 | 2 | 4 | 0 | **9** |
| 6.1-cosets.md | 3 | 1 | 0 | 0 | **4** |
| 6.3-fermat-and-eulers-theorems.md | 2 | 1 | 3 | 1 | **7** |
| **TOTAL** | **21** | **10** | **18** | **3** | **52** |

(4.1's two NARRATION entries are NARRATION+TRUNCATED compounds, counted once under
NARRATION. 11 of the 49 machine-flagged paragraphs were cleared as faithful scaffolding or
legitimate divergence notes; 14 defects were found that the flagger never saw, all of them
missing Judson text rather than rewritten Judson text.)

### Two findings worth escalating beyond the per-line fixes

1. **5.1 is missing a whole theorem from its prose.** Theorem 5.16 (even/odd parity is
   well defined) is never stated, its proof is never carried, and the *definitions* of
   **even** and **odd** permutation that it licenses are never given — yet §10.2 and the
   rest of 5.1 depend on them. "Given the lemma, parity is well defined." at :3571 is the
   only trace.
2. **11.2's Correspondence Theorem proof drops its fourth paragraph** (the
   normal-subgroups-correspond half), which is exactly the text that Judson's "Notice that
   in the course of the proof of Theorem 11.13, we have also proved the following theorem."
   refers to — and which our :1541 then narrates as "the route the Correspondence Theorem's
   last paragraph sketches", pointing at text the file never carries.
