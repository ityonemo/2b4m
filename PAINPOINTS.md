# Pain points — what the language and library still lack

Consolidated 2026-11-17 from seven per-chapter logs (ch5, 6, 7, 9, 10, 11, 17), each kept
WHILE transliterating its chapter. Organized by KIND rather than by chapter, because the
chapter a thing was hit in stops mattering once two chapters hit it.

**The standing rule, inherited from every source file: an ADDRESSED entry is DELETED, not
annotated.** What is here is what is still missing. A "resolved" ledger at the bottom keeps
one line per removed entry so nobody re-derives it.

**Every entry below was re-probed 2026-11-17** against the current corpus; the probe is
named where it is not obvious. Four entries died in that pass and moved to the ledger.

---

# PART 1 — STRUCTURAL GAPS

The expensive ones. Each is a thing the library cannot express, not a thing somebody
forgot to write.

## 1. No sort of GROUPS (nor of subgroups, nor of theories)

A group is a THEORY — a sort plus operations plus axioms — so `forall G: Group` is
unwritable, and identity-by-origin sharpens it: `theory group` twice names ONE theory, so two
abstract groups must be declared independently.

**What does NOT follow, and was asserted wrongly twice:** "cannot quantify over theories"
does not mean "cannot state theorems about several theories". You must FIX the arity by
declaring that many, and declaring is cheap. Cayley's Theorem needs six declarations and then
proves (13 theorems, `std/group/isomorphism.b4m`); transitivity of ≅ declares a third group
and proves the composite's operation-preservation in one `rewrite`.

What is genuinely out of reach is narrower: the RELATION ≅ cannot be NAMED, because naming it
quantifies over pairs of theories. Every instance you declare is provable; "for all groups
G, H" is not. Same shape for simplicity (ch10: stated per-subgroup) and for Sylow, where the
blocker is RECURSION OVER GROUPS — Sylow I recurs at C(x) and G/N.

**THE RULE this produced:** treat "std has no X" as a fact about a FILE, never about the
language. A claim of "unstatable" requires a FAILED PROBE, not a search — and the probe is
usually to write the 5–10 lines that declare the structure and ask what is missing.
DECLARE, THEN MODEL: a fresh sort plus three axioms plus one `model` block inherits a corpus.

## 2. `std/function.b4m` is SINGLE-SORTED, so a map between two sorts is not an `Fn`

`oper apply(f: Fn, x: Element) => Element` — a function's source and target are the SAME
sort. An isomorphism's differ by construction, so the whole `Fn` layer (`invertible`,
`inverse`, `compose`, `funcExtensionality`, `functionFromGraph`) is unavailable to it.

`isomorphism.b4m` declares φ and ψ as primitive and states bijectivity as two round-trip
axioms, deriving injectivity and surjectivity. ~20 lines, but EVERY cross-sort map in std
re-derives them: there is no reusable "bijection between two sorts".

**What would fix it:** a two-sorted function theory (`Map` with `dom`/`cod` as parameters),
of which today's `Fn` is the diagonal case. Not attempted.

## 3. The convolution layer is restated FIVE times

R[x], F[x], ℤ_p[x], ℤ[x], ℚ[x] each declare their own convolution recursion — re-probed:
still five. Character-for-character identical but for the coefficient sort's name.

The duplication is in the INSTANTIATION MECHANISM, not the abstraction:
`std/ring/polynomial.b4m` is genuinely generic (`sort R` abstract, all 19 theorems over an
arbitrary commutative ring). What is missing is any way to say "`ring_poly` at coefficient
sort `Q`" and have the sort and its axioms come into being.

Same shape, same cause: **`Seq` is re-postulated per carrier** (33 files declare a Seq-like
sort or an `at`), and **`disequalityIsSymmetric` exists in four files**, once per sort, with
no home. Measurement in `drafts/algebra-layering/README.md` (54 axioms below the abstract
layer) and `POLYNOMIAL-GENERICIZATION.md`.

**What would have saved the time on the ℚ[x] instance:** a `--library` check that a declared
`oper` with no axiom mentioning it is flagged. `qmulP` was mapped but LAWLESS, and nothing
said so — the probe was `fieldpoly.convolution` rejecting a `QPoly`.

## 4. A theorem-SCHEMA will not cross a model

Re-probed: `[using model(M) src.sch]` gives
`'src.sch' is a schema obligation the model does not discharge`, and the `<-` form it
suggests wants a POSITED LOCAL SCHEMA — an axiom, which the axiomatization rule forbids for
something provable.

So `std/indexed.b4m`'s `mappedListExists` could not be reused, and
`nonnegWellOrdering`/`nonnegStrongInduction` were re-proved from scratch over ℚ.

The diagnostics used to point OPPOSITE directions (one "drop the mapping", one "add the
mapping") and neither said "a schema cannot cross". The message above is now the clear one;
the LIMIT is unchanged.

## 5. ℤ_n's modulus is a single `const N`, so there is no FAMILY of cyclic groups

Re-probed: `std/integer/mod-n.b4m:49` still `const N: Int`. Theorem 9.21 compares ℤ_m × ℤ_n
with ℤ_mn for VARYING m and n — three members of a family indexed by the modulus.

This is deliberate: memory `zn-via-models-spike` settled that indexed sorts are NOT the
answer. The cost is that a theorem whose content is a relationship BETWEEN moduli is out of
reach, and §9.2's headline result is exactly that.

## 6. No CARDINALITY, so |G| = [G:H]·|H| is a statement about LISTINGS

Counts are listings by convention (§6.2), so "|G| = |H| across an isomorphism" means "φ's
image of a listing of G is a listing of H of the same length" — reachable, since φ is
injective and surjective, but not built. Theorem 9.6 (4) and (5) are the same shape: the
machinery exists over ONE group and does not travel along φ.

## 7. No STRUCTURAL query, so a differently-shaped twin is invisible

2378 theorems across 151 files is past what a reader holds. Cost a theorem written twice (90
lines of `powerSequenceExists` before finding `counting.powersAreListed`) and three confident
claims that std lacked things it has.

**A NAME index would not have helped** — in the sharpest case the statement was in hand
(`compose(compose(sigma, cycle(s,k)), inverse(sigma)) = cycle(t,k)`) and still declared
missing, because finding it required already suspecting the word "conjugate".

`query search` matches name and statement TEXT by token overlap, and a well-chosen query
often suffices now. What it cannot do is match a SHAPE — a pattern with holes, matching up to
alpha-renaming, sort aliasing and binder order:

    2b4m query shape std "compose(compose(?s, ?f), inverse(?s)) = ?"

Token search gets there when operator names are distinctive; it does not when the shape
matters and the vocabulary is common (`op`, `add`, `mul` are everywhere), nor up to a sort
alias. See memory `std-has-no-index`.

## 8. RSA's gcd ≠ 1 case is unreachable (and that is honest)

Judson splits on `gcd(x,n) = 1` (x is a unit, Euler applies — PROVED) versus `≠ 1`, which
needs n's FACTORIZATION as pq, the Chinese Remainder Theorem, and `x < n`. None exists in
std. What is proved is RSA-for-units, the case the chapter computes with.

**The honest framing:** the group fact is the mathematics; the second case is an artifact of
RSA being stated over all of ℤ_n rather than over U(n).

## 8b. Matrices are OUT OF SCOPE, by ruling

§7.1's last construction encrypts PAIRS of letters with an invertible 2×2 matrix over ℤ_26,
and §9's `det : GL_2(R) -> R*` wants the same. There is no matrix theory in std and the user
ruled matrices out of scope during Chapter 4, so both are recorded as prose. Listed here so
the absence is not re-discovered as a gap.

## 9. The cube's motions need finite case work, not an induction

8 vertices, 12 edges, 24 motions. The n-gon machinery of `std/permutation/dihedral.b4m`
would apply, but "six faces on top × four rotations" is a geometric count with NO n to
induct on. The even/odd vertex split is prose for the same reason. Marked in place in
`aata/5.2-dihedral-groups.md`.

---

# PART 2 — ENGINE DEFECTS AND MISSING CHECKS

Things the engine could reasonably do and does not.

## 10. A discharger's BINDER ORDER is part of its interface, and nothing checks it

Re-probed: still unchecked. A model maps a NAME to a name and does NOT reorder binders, so a
permuted discharger silently binds the wrong arguments and every transferred theorem gets a
subtly wrong instance. `aNonnegGapMakesItLess` was `forall a, b, d` against
`lessThanIntro`'s `forall a, d, b`.

**Worth fixing:** reject a permutation at the `<-` site by comparing binder sorts
positionally.

**The process note that came with it:** I filed this as an engine bug before finding it was
mine. The minimal repro I built PASSED, which should have redirected me immediately — a repro
that does not reproduce is evidence about the hypothesis.

## 11. An UNCONSUMED conjunct in a predicate gets no scrutiny at all

`isTheIntegerDecomposition`'s coprimality conjunct put both monomials at index ZERO, so the
polynomial's only nonzero coefficient was `r + s` — the condition was about the single number
`r+s`, not about `r` and `s` being coprime. **It checked green from the day it was written and
would have forever**, because nothing downstream consumed it.

This is the *restated argument* failure mode: a type-correct encoding of a different claim
than the source makes. **What found it:** building the consumer forced "what ARE this
polynomial's coefficients", and the probe answered `add(r, s)`.

**Generalizes:** any std predicate with a conjunct nothing has consumed carries this risk.
Worth a sweep.

## 12. An UNINSTANTIATED SCHEMA reports "0 theorems proven" and exits 0

A schema's body is checked at its instantiations, so a schema no instance exercises is as
unverified as a hole while looking green. `std/permutation/listing.b4m` therefore ends with a
concrete instance to drive the chain. Not a bug by the current design — worth a diagnostic.

## 13. `polynomial` cannot see inside a term with a Nat subterm

`[using polynomial(rational)]` fails `expected sort 'Q', got 'Nat'` when the goal holds a
power whose exponent is a `Nat` — i.e. any `qpower(s, k)`.

**Workaround (re-probed, still needed):** state the law over ABSTRACT ℚ variables and
`specialize` at the compound term, so the tactic never descends into the exponent.
`addingAndSubtractingCancels` and `theNegatedProductFromZero` exist only for this.

## 14. `polynomial`'s hardcoded rules cite source-space formulas under a transfer

The hardcoded rule set cites ring lemmas by well-known NAME with SOURCE-SPACE formulas, so
under a transfer the cite claims a guard-free universal while the resolved theorem is
relativized. The hardcoded set makes this a design question, not a one-line fix.

## 15. A model target must be a SYMBOL, not an expression

`ring_poly.ONEP` could not map onto `monomial(oneF, ZERO)`; it needed a declared
`oper monomialOne()` with a defining axiom. Cheap once seen, but the error does not say
"write a symbol" — it says the name is not found.

## 16. A definition block cannot infer a clause variable's sort under an existential

`pred inImage(s: PermG): inImage(s) iff (exists g: G; s = lam(g))` fails with "cannot infer
the sort of 'g'". A declared `pred` plus a named `axiom` works — and is what a model needs
anyway, since a definition clause's name is mangled.

## 16b. The index-arithmetic lemmas live in the wrong file

`indexSplits`, `belowTheBaseIsBelowTheSum` and `indexPastTheBase` are pure Peano-order facts
— "an index below base+m is either below base or is base+j for some j<m" — with NO
permutation content, but they are declared in `std/permutation/count.b4m`. They belong in
`std/peano/order.b4m` (or a `std/peano/block-index.b4m`). Mechanical move.

Re-probed: still there, and five files import `permutation/count.b4m`, some only for these
three. The earlier four-way DUPLICATION is gone (they are proved once and imported), so the
cost is just the misleading dependency — a block decomposition over any carrier imports the
permutation counting theory for three Peano facts.

## 16c. A DANGLING ALIAS passes `check` — and that is the cost of demand-driven resolution

**SETTLED BY DESIGN, user ruling 2026-11-17 — not a defect to plug.** Recorded here because
the behaviour is surprising and the reasons against each fix are not re-derivable.

Both of these print `OK, exit 0`:

    theory group_lagrange <<< "std/group/lagrange.b4m"   // the file exists
    sort G = group_lagrange.Grp                          // makes the theory decl "used"
    fact lagrange = group_lagrange.noSuchTheoremAtAll    // this name does NOT exist

    theory lib <<< "no-such-file.b4m"                    // the FILE does not exist
    sort A = lib.X
    const Z: A                                           // else the unused-alias check fires

One cause: **a DECLARATION is never demanded — only a proof demands anything.** Measured with
`--trace-facts`: `Context.discover` allocates a FileId and never READS the file, so on the
first repro `std/group/lagrange.b4m` is never parsed at all, not even by the `sort` alias.
All five alias kinds accept a nonexistent target.

**THE RULING: do not fix it by parsing at the import.** Racking a ParseTask per `theory`
declaration works and was nearly built — it makes every reachable file parsed by quiescence,
reducing the member check to a `declOf` lookup. It is still wrong: `[using import(I) thm]`
exists so a proof pulls in exactly the facts it NAMES instead of traversing the file tree.
Parsing at every import makes each of std's 916 `theory` declarations a traversal root and
trades that property away for a narrow class of authoring error.

**Three things any future attempt must respect:**

1. **An import is a CONSUMPTION; a declaration is a PUBLICATION.** "This file never reaches
   it" is locally decidable; "nothing needs this" is a whole-corpus question.
2. **The AGGREGATOR requirement is SOUNDNESS, not convenience.** `std/peano.b4m` must keep
   `pred less_than` even though it never says `less_than` itself, because 16 neighbouring
   `fact` re-exports are PHRASED in it. Delete it and `peano.b4m` passes ALONE while the
   LIBRARY sweep fails with `reference not found` — an undemanded `fact` is never resolved,
   so only a whole-library strict run sees it. (std declares 1426 non-`fact` aliases, so
   "unused in its own file" routinely does not mean dead.)
3. **One breakage class is unfixable in a parser, in principle.** An accelerant resolves
   lemmas by BARE NAME at proof time, so no syntactic analysis can predict a reference the
   accelerant generates later.

**If revisited, `--library` is the place** — every file is already a root there, so the parse
is paid for and no laziness is traded. **The blocker there is that no symbol-usage graph
exists:** the unused-axiom check rides on `ctx.axiom_taint` (per proven theorem, the facts its
proof rests on), but sorts, consts, opers and preds are used by appearing in STATEMENTS AND
TERMS rather than in a citation closure, and every `Context` side table is fact-level.
Building that graph is the design question to answer first.

The accurate narrow claim, worth keeping: **a syntactic check can tell you a name was
MENTIONED; only resolution can tell you it RESOLVES.**

## 17. `2b4m check tests/cases` is a runaway

The whole fixture directory as one sweep: pathological fixtures, 6.8 GB RSS, >8 min. Use
test_sweeps' curated directories.

---

# PART 3 — TACTIC AND LANGUAGE BOUNDARIES

Not defects — real boundaries that cost a round each until known. Several are now
documented; they stay here because the COST is the point.

## 18. `simplify` proves IDENTITIES, not CONSEQUENCES

Re-probed: a rearrangement like `0 = X + r·t ⟹ X = r·(−t)` is not a `simplify` goal at all,
however simple it looks. Easily the chapter's most frequent single friction, hit at a
dozen-plus sites.

`simplify` DOES chain substitutions (`A = B`, `B = C` ⊢ `f(A) = f(C)`). The boundary is
consequence-vs-identity, plus the rewrite limit on long chains. **When it fails, write the
explicit `rewrite` chain** — each is bidirectional and does one substitution, and since the
one-ref form landed a congruence needs no reflexive scaffold.

## 19. `specialize` discharges antecedents POSITIONALLY, with no way to skip one

`gaussLemmaAtDOne` has seven antecedents with the scaling equation SIXTH; handing it over
first matched it against antecedent one. Reordering the CALLER's hypotheses does not help.

**What works: claim the instance VERBATIM — scaling antecedent included — then discharge that
one antecedent with `tautology`**, which consumes an implication by CONTENT rather than
position.

Also: `specialize` on a `forall`-quantified AXIOM treats the binder as a premise to discharge
("cannot discharge the guard premise") — `apply_at` is the right rule.

**And it needs term args for binders that FOLLOW a premise.** `conjugationIsMultiplicative`
is `forall sigma; invertible(sigma) -> forall f, g; …`, and specializing at `sigma` alone
leaves `f`/`g` unbound — the diagnostic shows the remainder as `forall b1: Fn; forall b2: Fn`,
accurate but easy to misread as a shape mismatch. **Put EVERY term in the parens regardless of
where its binder sits.**

Two more citation shapes, a cycle each:

- **Inside a `case` arm, the arm label names a SUBPROOF.** `[using tautology <arm-label>]`
  errors ("names a subproof; a step reference is required") — restate the assumption first
  with `[by hypothesis <arm-label>]`.
- **A schema citing a schema instantiates the inner one AT ITS OWN PARAMETER:**
  `[using instantiation innerSchema((fun g: Fn => inQ(g))) refs]`.

## 20. An admitted `specialize` SHRINKS the proof `--fast` examines

`--fast` passed a lemma that strict rejected with `simplify: normal forms differ` — even
though `simplify` KEEPS its decision under `--fast`. It didn't fail because `--fast` never
REACHED it: the enclosing `specialize` is admitted on "a head is present", so the steps
underneath were never demanded.

**The general rule, which I got wrong twice in one turn:** it is NOT that `specialize` is
uniquely able to admit what strict refutes — per `design/acceleration.md`'s table every word
can, and the shared mechanism is WHAT A NAME DENOTES. What is special is narrower:
`specialize` is the one word whose admit drops the claim-vs-instance match, and therefore the
one whose admit reduces the amount of proof under examination. **A `--fast` green over a proof
containing a `specialize` says strictly less than a `--fast` green elsewhere.**

## 21. `tautology` sees ATOMS, not content

Documented, still costs rounds. `e = ONE` plus `ONE | ONE` does NOT give `e | ONE` — an
equation and a predicate are unrelated atoms. `power(g,m) = g` plus `g != E` does not give
`power(g,m) != E`. The countermodel names the atoms it set independently, which is the tell.
Fix: do the non-propositional step yourself, then let `tautology` close it.

An `iff` axiom likewise needs explicit elimination before either direction is usable.

## 22. `polynomial` is a SCALAR-layer tactic

It binds `add`/`mul`/`ZERO`/`succ` by WELL-KNOWN NAME, so over a polynomial carrier whose
operations are `addP`/`mulP` it reports `the goal has no add/mul structure`. Confirmed across
the corpus: every `using polynomial(...)` sits over the COEFFICIENT ring.

Easy to misread as "broken here", because the goal plainly IS a ring identity. **Corollary
worth planning around:** a new polynomial layer must state its own
distributivity/identity/negation lemmas, since no tactic will supply them.

## 23. Smaller language facts, each of which cost a round

- **A step cannot carry its own `proof … qed`.** An inner universal needing its own induction
  must be its own TOP-LEVEL theorem. The error points at the step, so it reads as a syntax
  slip rather than "this wants to be a lemma". (Hit twice in one session; and the parser's
  recovery then swallows the NEXT declaration, so the cascade is confusing.)
- **`or` is LEFT-associative** — trichotomy is `(k<0 or k=0) or 0<k`, and a `case` split must
  nest accordingly. Cost two rounds in two files.
- **`case` is a step's JUSTIFICATION, not a step of its own.**
- **A definition-block clause is UNIVERSALLY QUANTIFIED.**
- **`unpack` is `unpack v: Sort from step`**, not `unpack step as v`.
- **A nullary `oper` takes no parens; a nullary `pred` does.**
- **`import(X) law` yields the whole UNIVERSAL**, so every use at concrete arguments needs a
  `specialize` on top. Easy to forget because the citation reads like the instance.
- **Associativity orientation:** `mulIsAssociative` gives `(ab)c = a(bc)`; half of uses want
  the mirror and need `symmetry`. Cheap individually, frequent in aggregate.
- **A theorem's TERM arguments and HYPOTHESES are separate lists**, and the error is oblique.
- **A model-transferred theorem keeps the SOURCE's binder order.** Read the source statement;
  do not guess. (The diagnostic is good, once read as "your ref landed in the wrong slot".)
- **Two same-named sorts from different origins print identically** (`expected sort 'Fn', got
  'Fn'`) — path canonicalization decides identity, so import everything the same way.
- **`--axioms` lists an axiom per ORIGIN**, which reads like a bug and is not.
- **`at` has the same spelling for Seq and Points**, and it bit three times.
- **`Element` is an UNCONSTRAINED sort**, so "there are at least five points" has no
  expression.
- **Lemma-name guessing still fails**: `lessThanSucc` (really `lessThanSelf`),
  `nothingBelowZero` (`notLessThanZero`), `succReflectsLessThan` (`succReflectsOrder`).
  Grep the statement SHAPE, never the name you'd expect.
- **ℚ gaps:** no cancellation lemma (`field/units.b4m`'s is over `Nonzero`); has
  `addSuccLeft` but no `addSuccRight`.
- **Right-hand companions go missing in pairs** — `polyAddNegRight`, `polyAddZeroRight`,
  `polyMulAddDistribRight` all absent while every LEFT form existed; ℤ_n has
  `addInverseLeft` and no right form (the affine proof derives it inline in three steps,
  though `addCommutes` and `addIdentityRight` both exist). Each is two lines from its left
  twin plus commutativity. When a layer is built to satisfy one consumer's left-handed
  proofs, the right forms never get written — add both while the file is open.
- **A schema cannot recurse on its own argument**, and the growing-term form HANGS.
- **A test-harness failure message ECHOES the expected output.** Twice I read those lines as
  program output and hunted a nondeterminism bug that did not exist.
- **`assoc` CANNOT INSERT A CANCELLING PAIR.** Both of Judson's Second-Isomorphism
  regroupings insert `h h^-1`, so the sides are NOT equal by associativity alone — `assoc`
  right-nests both and compares; it cannot invent the pair. Each needs the cancellation
  written out (flatten, regroup, cancel, absorb the identity).
- **A `define` ALIAS NEEDS ITS PARAMETER.** `define inImage = homomorphism.inImage` fails
  with "expects 0 arguments, got 1"; write `define inImage(x) = homomorphism.inImage(x)`.
- **A TRANSFERRED AXIOM MAY ARRIVE IN THE OPPOSITE ORIENTATION.** `opGAssoc` through a model
  gave the associativity reversed from the source axiom, so regrouping needed a `symmetry`.
  Check the orientation rather than assuming it.
- **A lemma may live off the transfer path.** `inverseIdentity` is in
  `std/group/sequence.b4m` and `std/group/factor.b4m`, not `std/group.b4m`, so it is NOT on
  a model's transfer path — a local model of `std/group.b4m` at the target's symbols is the
  route. (Re-probed: still two copies, neither in the parent, which is also an instance of
  entry 3.)
- **Normality ORIENTATION.** std states it `inN(n) -> inN(g n g^-1)`; Judson writes
  `h^-1 n h`, which is the axiom at `g = h^-1`, so reaching his form needs an
  `invInvolution` rewrite.

---

# PART 4 — WHAT WORKED (process, kept because it was learned expensively)

## 24. READ THE SOURCE BEFORE SCOPING

Chapter 10's central lesson, learned three times in one chapter. A "we lack the machinery"
note is a claim about the SOURCE's proof, not about the tool — and it DECAYS. One such entry
claimed Judson's parity lemma needs induction over a non-ℕ well-founded order and stood for a
year; **both halves were wrong.** His proof is TWO NESTED ORDINARY INDUCTIONS, and both were
already in the library. Now proved: 57 theorems, hole-free.

## 25. Reason from a PROBE, not from the shape of a declaration

The root cause running through several wrong turns. Each was settled in minutes by a scratch
file, an `--axioms` run, or a `std.debug.print`. The corpus has cheap instruments; the failure
is not reaching for them before forming a view.

Worked examples: `theSubject` was declared a blocker and is actually a model PARAMETER (an
uninterpreted `func` with no defining axiom is as good as a parameter, because `model` is
exactly the mechanism for fixing parameters — the two-model probe takes minutes);
`polynomial` was assumed unable to do something it does; four claims that std lacked things
it has.

## 26. DECLARE, THEN MODEL — it costs almost nothing

`isomorphism.b4m` declares G and H with three axioms each, then two `model` blocks make both
real groups, so right identity, right inverse, cancellation and identity-uniqueness all
transfer instead of being re-proved twice. Six axioms of boilerplate for two full corpora.

Lagrange generalizes to ANY subgroup the same way: `inSubgroup` is a model source. And
**a fixed const/pred + axioms section IS a model source**, indistinguishable from dead code
until some fixture demonstrates the model.

## 26b. A coset is its MEMBERSHIP PREDICATE, and the source's equalities survive that

There is no sort of subsets of a group, so §10.1's `gN = Ng` is extensional agreement of two
predicates and `aN = bN` is `inSubgroup(a⁻¹b)`. **Both are exactly how Judson USES them** — he
never needs the coset as an object, only membership and equality — so the transliteration is
faithful rather than a workaround.

The general move: when the missing object is only ever USED through a predicate, the predicate
IS the encoding, and checking that against the source's usage is what tells you so.

## 27. Prove algebra at the layer that owns it, then transfer

ℚ[x]'s negation algebra was rebuilt generically at `ring_poly`; F[x] then paid SEVEN one-line
transfers instead of seven inductions. **Check the layer below before inducting** — ℚ[x]
hand-proved four negation theorems (305 lines) that an existing, already-complete model could
have transferred.

The cost of a missing generic theorem is not "it gets proved twice" — it is that the second
proof lands at the WRONG LAYER, by induction, and the next carrier faces the same choice. The
check is one `--axioms` call plus a grep of the layer below.

**And generic-vs-specific is decided by what a proof CITES, not what its statement mentions.**
Five ℚ[x] theorems full of `rational.mul` rest on zero field axioms — ring theorems wearing
ℚ's vocabulary. Conversely one that STATES a domain fact rests on `fieldInverse`. Naming
reveals neither direction; `--axioms` reveals both.

## 28. A conclusion that is TRUE but HARMLESS is the hardest defect to see

A theorem whose conclusion follows from fewer hypotheses than it lists checks green forever,
and the name usually claims more than the statement. Seen three times in one chapter.

**The checker verifies the steps prove the stated formula. It cannot tell you the formula is
weaker than you meant, or that the name oversells it.** Three tools do: the **dead-step
lint** (unused hypotheses are the loudest signal), **`--axioms`** (two independent constants
where one was intended shows as two axioms), and **asking what the conclusion rules out**
before naming it.

## 29. A predicate whose conjuncts are each provable can still be UNREACHABLE

Because the HYPOTHESES of the proving theorems do not match the CONCLUSIONS of the producing
ones. Counting conjuncts measures nothing. **The composition audit — matching each theorem's
demanded premises against what the chain supplies — is the only thing that found any of
these, and it found one every time it was run.**

One still open: the descent step gives `less_than(ZERO, e)` (POSITIVE only) and unbounded
divisibility, while coprimality needs all integer `e` (negative and zero matter, since `-1`
divides `ONE`) and a BOUNDED range.

Related reusable shape: **when a producer reports a BOUNDED fact and a consumer wants the
UNBOUNDED one, the missing premise is a DEGREE BOUND**, and it usually already exists in the
producer's own equation rather than needing a new axiom.

## 30. Top-down with `hole` pays for itself — and a `hole` cannot be stubbed mid-proof

The block decomposition and the parity lemma both came out of stating the endpoint first. And
because `hole` is a top-level declaration only, a gap must be its own NAMED hole with a fully
written statement — which forces a better factoring than stubbing mid-proof would.

## 31. `--library` is real pressure, not ceremony

The first draft of `isomorphism.b4m` reasoned entirely in H, so G's structure was declared but
idle and `check --library` failed with "2 unused axiom(s)". Adding Cayley's Theorem fixed it
GENUINELY rather than with a token example. The gate turned "I should probably do Cayley" into
"the library is inconsistent until I do".

Chapter 11 hit it three more times, each a real design problem rather than a formality:

1. `homomorphism.b4m`'s `opGAssoc` unused — the file was treating G as a SET WITH A MAP
   rather than as a group, and `GIsAGroup` was declared and never cited. Fixed by proving
   kernel-trivial-iff-injective, which actually consumes G's group structure.
2. `factor.b4m` with ALL FOUR of N's axioms unused — `clsCongruent` and `opQHom` already
   encoded that N is normal, so the lifted laws never cited N's structure. The gate was
   saying N was decorative. Fixed by proving, FROM N's axioms, what the posited ones require.
3. `correspondence.b4m` with three unused — each became a real theorem.

**The pattern: an unused axiom in a theory file means the theory is assuming structure it
does not use, which is nearly always a MISSING THEOREM rather than a spurious axiom.**

## 32. An ASSUMED axiom is never exercised by a proof

Check it against the DEGENERATE instances of every define it quantifies over. The trivial
transposition `(a a) = id` made an assumed parity lemma yield `2 | 1`, and everything
downstream was vacuously "proved". `--axioms` shows what is assumed; **nothing shows what is
inconsistent.**

## 33. Judson's route is not always cheapest — but prove that before diverging

§17.2's uniqueness step wanted degree ADDITIVITY; mutual divisibility was cheaper and
`twoGcdsDivideEachOther` already supplied it. The discipline that makes this legitimate: the
aata rule allows a divergent proof structure, noted in a `>` aside. The divergence gets
WRITTEN DOWN with its reason, not silently substituted.

## 34. Measurement hygiene

- **A counting measurement must EXCLUDE what you are about to delete.**
- **Before strengthening what feeds a proof, grep what the proof CONSUMES.**
- **Probe whether an accelerant already does it** before writing a helper.
- **Verify computationally first**, then look for the statement that drops the structure.
- **A generator should be demand-driven**, and precompute its table before branching. (I
  started a Python emitter four times and deleted it three.)
- **Cite a theorem by CONTENT, not by a derived number** — PreTeXt auto-numbers, so counting
  blocks in the XML is unreliable.

---

# RESOLVED AND REMOVED (ledger)

One line each, so nobody re-derives them. Chapter of origin in brackets.

**Died in the 2026-11-17 consolidation probe:**

- **An incomplete model discharge reports as a bare sort mismatch** [ch17 #2] — FIXED
  (`322c31a`, `c8d6b78`): both shapes now name the unmapped entity AND what to write for it
  (a `<-` discharge for an axiom, a `:` mapping for a symbol). Gated by
  `tests/cases/model/composed/` and `tests/cases/model/discharge/`. The up-front half shipped
  as `2b4m debug model` (`a6596db`): a model's mapping surface per source theory plus what it
  leaves `unmapped (:)` / `undischarged (<-)`. SYNTACTIC by design — the real obligation set
  is "whatever the proof cited", known only at elaboration — so a nonempty list is NOT an
  error: across `std`'s 83 models only 14 theory sections are fully covered, because a model
  need only cover what the theorems it transfers reach. Three false-positive classes stay
  excluded, each from a real rule: aliases whose ORIGIN is mapped (identity-by-origin), the
  model's own TARGETS (a same-file model's file declares both theories), and guards of target
  sorts. See `[[debug-model-command]]`.
- **The two schema-across-a-model diagnostics point opposite directions** [ch17 #3] — the
  message is now one clear sentence naming the undischarged schema obligation. The LIMIT
  (entry 4 above) is unchanged.
- **`abstract axiom` is needed to verify a model's qualifier axioms** — NOT NEEDED, and the
  mechanism is why: a transfer RE-PROVES the source body under the overlay, and an
  un-overloaded entity maps to ITSELF, so an undischarged citation fails by statement
  mismatch. Gated five ways.
- **A tactic's generated terms re-owe a guard a step in scope proved** — FIXED (`43f63f3`):
  the obligation becomes a stated antecedent the call site discharges.

**Earlier:**

- **A listing's length is not known to be unique (for groups)** [ch6] — re-proved as
  `anyTwoGroupListingsHaveTheSameLength`, 141 lines.
- **§6.3's stand-in schema is circular** [ch6] — resolved by the container theory the entry
  itself predicted; `std/indexed.b4m` carries it.
- **PARITY lives in an aata chapter file, not std** [ch10] — lifted to
  `std/permutation/alternating.b4m`.
- **The four-case cycle analysis needs concrete cycle arithmetic** [ch10] — retired by probe;
  extensionality plus `parity.b4m`'s deciders cover it.
- **Generation by a SET** [ch10] — never needed; Judson's step unpacks to an existing
  subgroup-products lemma.
- **A cycle's LENGTH / decomposition SHAPE / conjugation as relabelling** [ch10] — all three
  were already in std and asserted absent without grepping.
- **A FIXED-CONSTANT development is reachable only through a model nobody wrote** [ch6] — the
  model got written; see entry 26.

---

## Source files

Consolidated from `CHAPTER{5,6,7,9,10,11,17}-PAINPOINTS`, all deleted in favour of this file.
Their git history holds the per-chapter narrative if the context of a particular entry is
wanted.
