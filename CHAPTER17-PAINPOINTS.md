# Chapter 17 production pain points

Recorded 2026-10-31, while §17.3 (irreducible polynomials / Gauss's Lemma) was being built.
These are the things that cost real time, in rough order of how much. Several are already
queued elsewhere; this file is the chapter's own account, with the evidence that made each
one visible.

---

## 1. The convolution layer is now restated FIVE times

`qconvolution` + its three axioms were added to `std/rational/polynomial.b4m` (`fc4b179`)
because ℚ[x] had **no coefficient law for `qmulP` at all** — it was declared and mapped into
F[x], but F[x]'s convolution axioms were never discharged, so `qcoeff(qmulP(p,q), i)` was
completely opaque. Nothing could be proved about a product's coefficients.

That makes **five** copies of the same recursion in std: R[x], F[x], ℤ_p[x], ℤ[x], ℚ[x]. Each
is character-for-character the same but for the coefficient sort's name.

**Cost here:** finding it at all. The probe was `fieldpoly.convolution` rejecting a `QPoly`
(`expected sort 'Poly', got 'QPoly'`) — nothing in the file said multiplication was opaque.

**Already queued** as item 5 (generic polynomial theory). The measurement is in
`drafts/algebra-layering/README.md`: 54 axioms below the abstract layer, and the duplication is
in the *instantiation mechanism*, not the abstraction — `ring/polynomial.b4m` is genuinely
generic (`sort R` is abstract, all 19 theorems are about an arbitrary commutative ring); what is
missing is any way to say "`ring_poly` at coefficient sort `Q`" and have the sort and its
axioms come into being.

**What would have saved the time:** a `--library`-style check that a declared `func` with no
axiom mentioning it is flagged. `qmulP` was mapped but lawless, and nothing said so.

---

## 2. A model only transfers what every symbol the PROOF mentions is mapped for

Hit repeatedly across the chapter, and the error always surfaces *inside the source file*, far
from the model block:

- `std/ring/polynomial.b4m` aliases `ring.Ring`, so a transfer onto a new coefficient sort must
  also map `std/ring.b4m`'s own seven axioms (ℤ[x], ℤ_p[x] both carry that second half).
- **Transfers chain.** A theorem itself proved by a model transfer re-checks that inner
  transfer, demanding the inner layer too. `polyMulIsCommutative` is deliberately *not* carried
  into ℤ[x] for this reason — R[x] proves it through `tailConvolution` and `segment`.

**A transfer whose own source theorem transferred demands the inner layer too.** That is not a
wall — models compose, and `std` relies on it (see `NESTED-MODEL-COMPOSITION-ISSUE.md`); it
means the outer model must discharge every axiom the INNER proof reaches, not only the ones its
statement mentions. The failure surfaces as a sort error inside the source file, which is the
diagnostics defect that file records.

**Workaround that worked every time:** reprove the fact on the cut. It needs only the target's
own axioms plus any UNGUARDED model (ℚ as a whole is an ordered field, so
`RationalOrderedField` composes freely). The wall only bites when you want someone else's
*finished* theorem whose proof itself transferred. `anIntegerDividingOneIsAUnit`,
`aPositiveIntegerIsAtLeastOne` and the well-ordering pair were all obtained this way.

**Worth fixing properly:** the DIAGNOSTIC. The workarounds above are for not being told which
mapping is missing.

---

## 3. A theorem-SCHEMA will not cross a model

`std/indexed.b4m` already proves the index-pinned construction as `mappedListExists` — and its
own comment independently says "with prepend alone a prefix cannot be grown". But:

- mapping it is rejected — *"model maps only axioms; it materializes through the mapped axioms"*
- citing it through the model is rejected as an **undischarged schema obligation**
- the `<-` form the diagnostic suggests wants a **posited local schema** — an axiom, which the
  axiomatization rule forbids for something provable

So the induction was redone on ℚ's construction axioms. Same for
`nonnegWellOrdering`/`nonnegStrongInduction`, which are theorem-schemas over ℤ: ℚ's versions
are proved from scratch in `std/rational/natural-wellordering.b4m`.

**The two diagnostics point opposite directions**, which is the confusing part. One says "drop
the mapping", the other says "add the mapping". Neither says "a theorem-schema cannot cross".

---

## 6. A discharger's BINDER ORDER is part of its interface, and nothing checks it

`aNonnegGapMakesItLess` was declared `forall a, b, d` while `std/integer/order.b4m`'s
`lessThanIntro` declares `forall a, d, b`. A model maps a NAME to a name and does **not**
reorder binders, so `lessThanIntro(ZERO, ZERO, ONE)` silently bound `d := ONE`, `b := ZERO` and
every transferred ℤ-order theorem got a subtly wrong instance.

**I filed this as an engine bug before finding it was mine** (retracted in `3e23df2`). The
minimal repro I built *passed*, which should have redirected me immediately — a repro that does
not reproduce is evidence about the hypothesis.

**Worth fixing:** reject a permutation at the `<-` site by comparing binder sorts positionally.

---

## 7. An UNCONSUMED conjunct in a predicate gets no scrutiny at all

`isTheIntegerDecomposition`'s coprimality-of-(r,s) conjunct read

    coefficientsAreRelativelyPrimeUpTo(qaddP(qmonomial(r, 0), qmonomial(s, 0)), n)

Both monomials sit at index ZERO, so that polynomial's only nonzero coefficient is `r + s` —
the condition was about the single number `r+s`, **not** about `r` and `s` being coprime.
Judson says "and $r$ and $s$ are relatively prime". Fixed in `e3df93c`.

**It checked green from the day it was written and would have forever**, because nothing
downstream consumed it. This is the *restated argument* failure mode from the axiomatization
rule: a type-correct encoding of a different claim than the source makes.

**What found it:** building the consumer forced the question "what ARE this polynomial's
coefficients", and the probe answered `add(r, s)`. **Writing the consumer audits the
statement** — the top-down rule arriving from the other direction.

**Generalizes:** any std predicate with a conjunct nothing has consumed carries this risk.
Worth a sweep.

---

## 8. Smaller things that each cost a round or more

- **`simplify` CANNOT CONSUME A CITED EQUATION AS A PREMISE** — it proves identities, not
  consequences. A rearrangement like `0 = X + r·t ⟹ X = r·(−t)` is not a `simplify` goal at
  all, however simple it looks; measured, it reports
  `normal forms differ: 'X' vs 'mul(R, neg(T))'`. Easily the most frequent single friction in
  the chapter, hit at a dozen-plus sites across `integer-product.b4m`,
  `integer-division.b4m`, `polynomial.b4m` and `integer-polynomial.b4m`.

  Note `simplify` DOES chain substitutions — `A = B`, `B = C` ⊢ `f(A) = f(C)` passes. The
  boundary is consequence-vs-identity above, plus the rewrite limit on long chains.

  **When it does fail, write the explicit `rewrite` chain.** Each `rewrite EQ TARGET` is
  bidirectional and does one substitution, so an N-step rearrangement is N `rewrite`s with a
  named intermediate at each stage; since the one-ref form landed, a congruence needs no
  reflexive scaffold. Representative failures: a rewrite-limit loop
  (`theDenominatorCancels`'s precursor); `'ZERO' vs 'qcoeff(p, qdegree(p))'`; `'b' vs 'c'`;
  `'mul(g, mul(s, coefficient))' vs 'mul(g, mul(r, entry))'`;
  `'add(ZERO, ZERO)' vs 'qcls(add(…))'`.
- **An admitted `specialize` SHRINKS the proof `--fast` examines, masking sibling steps.**
  Hit on `theConstantMonomialProductAgreesCoefficientwise` (2026-11-02). `--fast` passed the
  lemma; strict rejected it with `simplify: normal forms differ`. But `simplify` KEEPS its
  decision under `--fast` (`design/acceleration.md`'s per-word table: "both sides normalized to a
  shared normal form"), so the step should have failed in both modes.

  It didn't because `--fast` never REACHED it: the enclosing `specialize` is admitted on
  literally "a head is present", everything else dropped, so the steps underneath were never
  demanded. The banner — `accelerated (admitted, not proved): specialize` — was the whole
  story and named the right word.

  **The general rule I got wrong twice in one turn.** It is NOT that `specialize` is uniquely
  able to admit what strict refutes; per the table, every word can, and the shared mechanism
  is WHAT A NAME DENOTES (a misbound operator, an alias colliding with a sibling theory's, a
  decision binding `add`/`mul`/`ZERO` by well-known name without checking the symbol obeys
  those laws). What IS special about `specialize` is narrower: it is the one word whose admit
  drops the claim-vs-instance match itself, and therefore the one whose admit reduces the
  amount of proof under examination. So **a `--fast` green over a proof containing a
  `specialize` says strictly less than a `--fast` green elsewhere** — the admitted subtree may
  hold failures that are not `specialize`'s kind of failure at all.

  Practical consequence for this chapter's cadence: `--fast` for the write loop is still
  right, but a lemma whose top-level justification is `specialize` is not evidence of anything
  until strict runs. That was already the standing rule ("never close a site on `--fast`
  alone"); the new part is the reason — not "fast is approximate" but "fast looked at less
  than you think".
- **`specialize` discharges antecedents POSITIONALLY, and there is no way to skip one.**
  Cost two rounds on the Gauss d = 1 branch. `gaussLemmaAtDOne` has seven antecedents with the
  scaling equation SIXTH; handing that equation over as the first ref matched it against
  antecedent one (`isInteger(c)`) and reported a claim/instance mismatch naming both formulas
  in full — a good diagnostic, once you read it as "your ref landed in the wrong slot" rather
  than "your fact is wrong".

  Reordering the CALLER's own hypotheses to match does NOT help: with no refs at all,
  `specialize` leaves every antecedent in place, so the instance still carries the scaling
  equation while the claim omits it.

  **What works: claim the instance VERBATIM — scaling antecedent included — then discharge
  that one antecedent with `tautology`**, which consumes an implication by its CONTENT rather
  than by position. Two steps instead of one, and the intermediate is honest about what the
  lemma actually says.

  Same root cause as the `--fast` masking entry above: `specialize` is positional, and its
  admit keeps only "a head is present".
- **A BOUNDED fact and an UNBOUNDED one are not interchangeable — and the gap is invisible
  until something consumes the wrong one.** Lemma 17.12 reports
  `hasIntegerCoefficientsUpTo(q, succ(n))`, because its descent runs over a finite index range.
  `integer-polynomial.b4m`'s `theProductIsIntegral` and
  `theModulusCannotDivideEveryProductCoefficient` both consume the unbounded
  `hasIntegerCoefficients`. The decomposition carries NO degree bound on `q` of its own, so
  bounded → unbounded is simply not available from it, and asserting the bridge would have been
  a textbook-sounding assumption about my own symbols (disguise #3 in the axiomatization rule).

  The honest route recovers the bound from the SCALING EQUATION instead:
  `aNonzeroScalingReflectsTheDegreeBound` — above the bound the scaled coefficient vanishes,
  and `noZeroDivisors` with a nonzero scalar forces `q`'s coefficient to vanish too. With a
  degree bound in hand the two integralities DO coincide
  (`aBoundedIntegralityWithADegreeBoundIsUnbounded`), because above the bound every coefficient
  is `ZERO` and `ZERO` is an integer.

  **The reusable shape:** when a producer reports a bounded fact and a consumer wants the
  unbounded one, the missing premise is a DEGREE BOUND, and it usually already exists somewhere
  in the producer's own equation rather than needing a new axiom.
- **A step cannot carry its own `proof … qed` block.** Hit TWICE this session, in two
  different files — `expected '[', got 'proof'`. A step is always `@label | formula [just…]`;
  an inner universal that needs its own induction or case split must be its own TOP-LEVEL
  theorem. The fix is mechanical (split it out and `specialize` it back in) but the error points
  at the step, not at the missing declaration, so it reads as a syntax slip rather than as
  "this wants to be a lemma".
- **`polynomial` is a SCALAR-layer tactic — it cannot do polynomial algebra.** It binds
  `add`/`mul`/`ZERO`/`succ` by WELL-KNOWN NAME, so over a polynomial carrier whose operations
  are `addP`/`mulP` it reports `the goal has no add/mul structure`. Confirmed across the
  corpus: every `using polynomial(...)` sits over `field` or `rational`, i.e. the COEFFICIENT
  ring, and not one is over polynomial operations.

  This is easy to misread as "the tactic is broken here", because the goal plainly *is* a ring
  identity. What it means is that a polynomial ring identity must be written as an explicit
  chain over named lemmas — distribute, split the negation, reassociate, fold — and the names
  must exist. Judson's one-line `b = p(1 - ar) + q(-as)` cost four lemmas and a dozen steps.

  **Corollary worth planning around:** a new polynomial layer should expect to state its own
  distributivity/identity/negation lemmas, since no tactic will supply them.
- **A model target must be a SYMBOL, not an expression.** `ring_poly.ONEP` could not map onto
  `monomial(oneF, ZERO)`; it needed a declared `func monomialOne()` with a defining axiom, and
  then the two coefficient obligations discharged from the monomial axioms. Cheap once seen,
  but the error does not say "write a symbol" — it says the name is not found.
- **Right-hand companions go missing in pairs.** Closing §17.2 needed `polyAddNegRight`,
  `polyAddZeroRight`, `polyMulAddDistribRight` and `aSumCancelsItsRightSummand`, none of which
  existed at the ring layer even though every LEFT form did. Each is two lines from its left
  twin plus commutativity. When a layer is built to satisfy one consumer's left-handed proofs,
  the right forms simply never get written — worth adding both while the file is open.
- **Prove algebra at the layer that owns it, then transfer.** The ℚ[x] negation algebra built
  during §17.3 was rebuilt generically at `ring_poly` here; F[x] then paid SEVEN one-line
  transfers instead of seven inductions, because `FieldPolyModelsRingPoly` already mapped every
  symbol (`--axioms` on `polyAddCancelRight`: 8 axioms, all mapped). The rule: if a second
  carrier is about to need the same induction, the induction belongs one layer down.
- **Judson's route is not always the cheapest route — but prove that before diverging.**
  §17.2's uniqueness step gets equal degrees from `deg d = deg d' + deg[ru + sv]`, i.e. degree
  ADDITIVITY, which needs the product-degree law in a form tracking the cofactor's own degree.
  Mutual divisibility turned out to be the cheaper premise, and `twoGcdsDivideEachOther` already
  supplied it — each divides the other, so neither degree is strictly below, and ℕ antisymmetry
  closes it.

  The discipline that makes this legitimate rather than a shortcut: the aata rule allows a
  divergent proof structure, noted in a `>` aside. So the divergence gets WRITTEN DOWN with its
  reason, not silently substituted. (Recorded in 17.2's aside.)
- **Check the layer below before inducting.** Measured: ℚ[x] hand-proved four negation theorems
  (305 lines) that `RationalPolynomialsOverARing` could have transferred — I verified the
  counterfactual transfer checks strict. The model was ALREADY complete; `ring_poly` simply did
  not carry the theorems yet.

  So the cost of a missing generic theorem is not "it gets proved twice" — it is that the second
  proof lands at the WRONG LAYER, by induction, and the next carrier faces the same choice. The
  check is one `--axioms` call plus a grep of the layer below. Full analysis in
  `POLYNOMIAL-GENERICIZATION.md`.
- **Generic-vs-specific is decided by what a proof CITES, not what its statement mentions.**
  Five ℚ[x] theorems whose statements are full of `rational.mul` and `qcoeff` turn out to rest
  on zero field axioms, zero domain axioms and zero ℚ-cut axioms — they are ring theorems wearing
  ℚ's vocabulary. Conversely `aNonzeroMultipleHasAtLeastTheDegree` STATES a domain fact but rests
  on `fieldInverse`, so relocating it to a domain layer would be a re-proof, not a move. Naming
  reveals neither direction; `--axioms` reveals both.
- **`tautology` sees atoms, not content** — documented, but still cost a round: `e = ONE` plus
  `ONE | ONE` does **not** give `e | ONE`, since an equation and a predicate are unrelated
  atoms. Fix is an explicit rewrite under `contradiction`.
- **`or` is LEFT-associative**, so trichotomy is `(k<0 or k=0) or 0<k` and a `case` split must
  nest accordingly. Cost two rounds in two different files.
- **Associativity orientation.** `mulIsAssociative` gives `(ab)c = a(bc)`; half my uses wanted
  the mirror and needed `symmetry`. Cheap individually, frequent in aggregate.
- **ℚ had no cancellation lemma at all.** `field/units.b4m`'s is over the `Nonzero` subsort;
  `aNonzeroFactorCancels` had to be proved from `fieldInverse`.
- **ℚ has `addSuccLeft` but no `addSuccRight`** — proofs commute both sides instead.
- **Lemma-name guessing**, still: `lessThanSucc` (actually `lessThanSelf`), `nothingBelowZero`
  (`notLessThanZero`), `succReflectsLessThan` (`succReflectsOrder`), `recipMulLeft`
  (`fieldInverse` + commutativity). `std/` has no index; grep the statement SHAPE, never the
  name you'd expect.
- **`unpack` syntax is `unpack v: Sort from step`**, not `unpack step as v`. Cost one round.
- **Nested `proof` blocks for a base case are not a thing** — use `@base-case-proof` + export.
- **A nullary `func` needs no parens; `theSubject` not `theSubject()`** — but a nullary `pred`
  does. Cost one round.
- **`import(X) law` yields the whole UNIVERSAL**, so every use at concrete arguments needs a
  `specialize` on top. Four sites in one theorem. Easy to forget because the citation reads like
  it is already the instance.

---

## 8b. A predicate whose conjuncts are each provable can still be unreachable

Each time the remaining work looked like "threading the pieces together", tracing it turned
up something unproved. One is still open:

**The descent step and coprimality do not line up:**

       coprimality needs:  forall e; isInteger(e) -> (e divides q BELOW n)
                                     -> e divides ONE
       descent step gives: less_than(ZERO, e)                  <- POSITIVE only
                           forall i; e divides q_i              <- UNBOUNDED

   So (a) negative and zero `e` are not covered — and they matter, since `-1` *does* divide
   `ONE`, so coprimality is not a statement about positive divisors only — and (b) bounded vs
   unbounded divisibility. Both need real lemmas.

**The pattern worth naming:** a predicate whose conjuncts are each individually provable can
still be unreachable, because the *hypotheses* of the proving theorems do not match the
*conclusions* of the producing ones. Counting conjuncts measures nothing. The composition
audit — matching each theorem's demanded premises against what the chain supplies — is the only
thing that found any of these, and it found one every time it was run.

---

## 12. `polynomial` cannot see inside a term with a Nat subterm (LIVE)

`[using polynomial(rational)]` fails with `expected sort 'Q', got 'Nat'` when the goal holds a
power whose exponent is a `Nat` — which is any `qpower(s, k)`. Hit twice in 17.14.

**Workaround:** state the algebraic law over ABSTRACT ℚ variables and `specialize` it at the
compound term, so the tactic never descends into the exponent. `addingAndSubtractingCancels`
and `theNegatedProductFromZero` in `std/rational/integer-division.b4m` exist only for this.

Related: `polynomial` also cannot CONSUME a cited equation as an input (it proves identities,
not consequences), so a rearrangement like `0 = X + r·t ⟹ X = r·(−t)` must be done by explicit
`rewrite` steps.

## 13. `polynomial`'s hardcoded rules cite source-space formulas under a transfer (ENGINE)

`polynomial`'s hardcoded rule set cites ring lemmas by well-known NAME with SOURCE-SPACE
formulas, so under a transfer the cite claims a guard-free universal while the resolved theorem
is relativized. The hardcoded rule set makes this a design question rather than a one-line fix.

## 14. `theSubject` is a model PARAMETER, not a fixed value

**I claimed (2026-11-02) that `theSubject` blocked Lemma 17.12 from ever being applied to two
polynomials, making irreducibility over ℚ structurally unreachable. That was WRONG, and the
user corrected it.**

`theSubject` is declared `func theSubject() => QPoly` with **no defining axiom** — nothing in
the file says which polynomial it is. So it is a model PARAMETER, and a model maps parameters.
Two models in one file, each mapping `theSubject` to a different constant, both transfer
`theIntegerDecompositionExists` strict-green (`drafts/two-subjects/probe.b4m`).

The one real cost, and it is small: `isADenominatorFor` is an uninterpreted pred whose
*defining axiom* mentions `theSubject`, so remapping the func alone leaves the pred pointing at
the old term. Each model needs its own instance of the pred plus its axiom as the discharge —
three lines per model.

**The actual lesson, which is the opposite of what I first wrote:** the fixed-`func` workaround
for the schema-arg-lambda limit (pain point 4) costs *far less* than it appears to. An
uninterpreted `func` is as good as a parameter, because `model` is exactly the mechanism for
fixing parameters. Before concluding that a `theSubject`-style encoding has painted you into a
corner, write the two-model probe; it takes minutes.

## 15. A conclusion that is TRUE but harmless is the hardest defect to see

A theorem whose conclusion follows from fewer hypotheses than it lists checks green forever,
and the name usually claims more than the statement. Seen three times in this chapter — a
conclusion that was immediate from one hypothesis while four others sat unused; a name
promising it "rules out a factorization" when the contradiction needed degree bookkeeping it
never did; and a hypothesis constraining one modulus while the conclusion spoke of an
independent one.

**The checker verifies that the steps prove the stated formula. It cannot tell you the formula
is weaker than what you meant, or that the name oversells it.** Three tools do:

- the **dead-step lint** — unused hypotheses are the loudest signal;
- **`--axioms`** — two independent constants where one was intended shows up as two axioms;
- **asking what the conclusion rules out** before naming it.

**The same root cause runs through §14: reasoning from the SHAPE of a declaration or a
statement instead of probing it.** Each of these was settled in minutes by a scratch file, an
`--axioms` run, or a `std.debug.print`. The corpus has cheap instruments; the failure is not
reaching for them before forming a view.
