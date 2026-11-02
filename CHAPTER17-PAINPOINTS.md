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

**And the hard version: a nested transfer cannot COMPOSE.** 2b4m re-checks an inner transfer
rather than composing two models, so ℕ → ℤ's `NonNeg` cut → ℚ's `isInteger` cut is
inexpressible. Concretely `lattice.gcdExists` and `int_order.signTrichotomy` both route through
`integer.nonnegCases`, itself a transfer, so neither reaches ℚ's cut:
`std/peano.b4m:857: expected sort 'Int', got 'Q'`.

**Workaround that worked every time:** reprove the fact on the cut. It needs only the target's
own axioms plus any UNGUARDED model (ℚ as a whole is an ordered field, so
`RationalOrderedField` composes freely). The wall only bites when you want someone else's
*finished* theorem whose proof itself transferred. `anIntegerDividingOneIsAUnit`,
`aPositiveIntegerIsAtLeastOne` and the well-ordering pair were all obtained this way.

**Worth fixing properly:** model composition. Everything above is a workaround for its absence.

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

## 4. A schema-arg lambda could not bind two sorts (FIXED)

`fun i: Nat, v: Q => …` was a parse error: the binder grammar was
`binders := ident (',' ident)* ':' ident` — one sort for the whole list. Every pre-existing
caller used the same sort twice (`fun y, z: Element =>` against `functionFromGraph`'s
`spec(Element, Element)`), so the gap had never been hit.

**It blocked the whole minimality assembly.** `anIndexPinnedChoiceIsRealized(spec(Nat, Q))`
could only be instantiated at a bare predicate name, which forces the subject pinned as a
file-scope nullary func — usable at exactly ONE divisor, while the descent needs it at `d·e`
with both bound inside the proof.

**Fixed** in `2f9c535` (comma-separated binder groups, each with its own sort).
`drafts/mixed-sort-schema-lambda/` has the repro and the dead-end analysis.

**Residual:** the `theSubject` workaround it forced is still in
`std/rational/integer-product.b4m` (`aDenominatorExistsForEveryIndex` reads its polynomial
through a nullary func). Now unnecessary; worth removing when that file is next touched.

---

## 5. Guarded models transferred NOTHING, for three independent reasons (FIXED)

Before 2026-10-30 **no guarded model in the corpus had ever transferred a theorem**.
`IntegersInRational` had been declared and documented for months with its only consumer in
`scratch-needswork/`. Three causes:

1. **No membership dischargers nominated** (`6478118`, a `std/` fix). A guarded model needs a
   ground fact per const and a closure per func. Without them a transferred proof's own
   `apply_at` leaks guards. **Nominations are load-bearing, not decoration.**
2. **`withGuardPremises` assumed guards form a LEADING run** (`2302392`). They do not: guards
   are injected in PARAM order and `freeFvarParams` *appends* the args' free variables, so a
   local-head `specialize` gives `head -> guard(freevar) -> hyp -> goal`.
3. **`projectBlockGuard` ignored `.unpack` blocks** (`61ead93`). A relativized `∃x: H` opens as
   `inH(w) and <body>`, so a `[by hypothesis]` restating `<body>` must and_elim past the guard.

**What this says about the gate:** a `model` block with no transfer through it is **dead code
that gates green** — obligations are checked per *transfer*, not at declaration.
`NaturalsInRational` is in the same position today. A `--library` check for an unconsumed model
would have caught all of this years earlier.

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

## 7b. Sequence and polynomial were two worlds with NO bridge between them

All of 17.12's machinery is over `QSeq` entries (`qat`); `isTheIntegerDecomposition` is over
`QPoly` coefficients (`qcoeff`). **Zero theorems in the corpus mentioned both**, and there was
no construction of a polynomial from a sequence at all — `grep -c 'exists p: QPoly'` returned 0
across both files.

Three theorems closed it: `coprimeEntriesMakeCoprimeCoefficients` and
`integerEntriesMakeIntegerCoefficients` transfer properties across a coefficient-matches-entry
hypothesis, and `aPolynomialMatchesASequence` (`f5053f1`) finally *supplies* that hypothesis by
building the polynomial monomial-by-monomial.

**What made the bridges possible at all:** `qpoly.dividesOnTheCut` is a `define` whose body is
character-for-character `dividesIntegrallyMeaning`'s right-hand side. Two predicates, two
files, same meaning, no stated relationship. Checked that before writing rather than trusting
the similar names.

**The lesson is about ORDER of discovery:** this was found by auditing whether the seven
conjuncts' theorems actually *compose* — matching each one's demanded hypotheses against what
the construction supplies — not by writing more theorems. Six conjuncts "had their machinery"
while the machinery could not be joined up.

---

## 8. Smaller things that each cost a round or more

- **`simplify` WILL NOT CHAIN TWO SUBSTITUTIONS** — easily the most frequent single friction in
  the whole chapter, hit at a dozen-plus sites across `integer-product.b4m`,
  `integer-division.b4m`, `polynomial.b4m` and `integer-polynomial.b4m`.
  The failure is always the same shape: a step wants "substitute equation A, then collapse with
  equation B", and `simplify` reports the two sides it could not reconcile
  (`normal forms differ: 'X' vs 'Y'`) or hits the rewrite limit.

  **Rule, now firm: `simplify` is for ONE shared normal form. The moment two different
  equations have to be applied in sequence, write the explicit `rewrite` chain.** Each
  `rewrite EQ TARGET` is bidirectional and does exactly one substitution, so an N-step
  rearrangement is N `rewrite`s with a named intermediate at each stage. Writing those
  intermediates out is not verbosity — it is the only form the tactic accepts, and the labels
  document the algebra.

  Representative instances: a rewrite-limit loop (`theDenominatorCancels`'s precursor);
  `'ZERO' vs 'qcoeff(p, qdegree(p))'`; `'b' vs 'c'`;
  `'mul(g, mul(s, coefficient))' vs 'mul(g, mul(r, entry))'` (three-equation chain);
  `'coefficient' vs 'mul(mul(r, recip(s)), entry)'`; `'add(ZERO, ZERO)' vs 'qcls(add(…))'`
  (needed the two vanishing classes substituted one at a time).

  **Related, same tactic, different cause:** `simplify` also cannot CONSUME a cited equation as
  a premise — it proves identities, not consequences. A rearrangement like
  `0 = X + r·t ⟹ X = r·(−t)` is not a `simplify` goal at all, however simple it looks.
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
  (`fieldInverse` + commutativity). `std/` has 1888 theorems and no index; grep the statement
  SHAPE, never the name you'd expect.
- **`unpack` syntax is `unpack v: Sort from step`**, not `unpack step as v`. Cost one round.
- **Nested `proof` blocks for a base case are not a thing** — use `@base-case-proof` + export.
- **A nullary `func` needs no parens; `theSubject` not `theSubject()`** — but a nullary `pred`
  does. Cost one round.
- **`import(X) law` yields the whole UNIVERSAL**, so every use at concrete arguments needs a
  `specialize` on top. Four sites in one theorem. Easy to forget because the citation reads like
  it is already the instance.

---

## 8b. "Packaging" was never pure assembly — three real theorems hid inside it

Each time I called the remaining work "threading the pieces together", tracing it turned up
something unproved. Logged because the estimate was wrong three times in the same way.

1. **Nothing constructed a polynomial from a sequence** (entry 7b) — the bridges took the
   coefficient match as a hypothesis and nothing supplied it.
2. **`isAMaximalCommonDivisorOfThePair` had no existence proof.** Every occurrence in
   `std/rational/integer-product.b4m` is a HYPOTHESIS, never a conclusion. Step 4 had always
   taken it on faith. A pair is a two-element sequence
   (`aTwoElementSequenceExists`, `ebcb8ac`) so the sequence descent covers it — but that is
   still a theorem, not assembly.
3. **The descent step and coprimality do not line up**, and this one is still open:

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

## 9. Process lessons (mine, not the tool's)

- **Probe each mechanism on a scratch file BEFORE writing the proof around it.** The first
  attempt at the minimality assembly wrote large hypothesis-threading wrappers and dead-ended
  at exactly the point a 30-line probe would have exposed in a minute. The second attempt
  probed first and landed.
- **Two nested wrappers threading nine identical hypotheses to reach one step** is the
  throwaway-abstraction smell. Caught and collapsed once; watch for it, because
  existential-heavy statements invite it.
- **Red/green is for ENGINE work.** I wrote the lambda fix implementation-first, added tests
  that passed immediately, then *deliberately broke one* to check it ran at all. That
  contortion is the tell: needing to sabotage a test to prove it runs means it was never red.
  (User correction; red/green does **not** apply to aata/std content, where `check` is already
  the loop.)
- **Probe before deferring.** Two "this cannot be expressed" notes I wrote in this chapter were
  both wrong: ℤ[x]↪ℚ[x] "needs an embedding" (ℚ carries its integers as a *cut*), and the
  denominator product "has no relational substitute" (`std/integer/product.b4m` has
  `productUpTo` with a real corpus, and `std/sequence.b4m` instantiates at ℚ cleanly because
  `Value: Q` is unguarded). Both were reasoned rather than measured.

## 11. The cut had no division algorithm, so no Bézout, so no Euclid (RESOLVED 2026-11-01)

**This was chapter 17's last blocker, and it is now closed** — `std/rational/integer-division.b4m`,
20 theorems. Recording it because the DIAGNOSIS took three tries and two of them were wrong.

**What was actually true:** ℤ's `divisionAlgorithmExists` and `coprimeBezout` cannot transfer
onto the cut — each reaches `nonnegCases`, itself a transfer of `peano.zeroOrSucc` through ℤ's
NonNeg cut, so composing ℕ → ℤ's NonNeg → ℚ's isInteger wants `Nat` to be both `Int` and `Q`
(`std/peano.b4m:857`). That is pain point 2 (no model COMPOSITION) biting again, and it is
structural.

**What I wrongly believed first:** that `euclidFromBezout` needed `div`, `mod`, `gcd`, `order`
and `wellordering` mapped, making the whole thing wait for the de-totalization. It needs 15
axioms, every one already mapped by `IntegersInRational`, and its `divides` is a `define` —
a macro, nothing to map. **I had read the FILE's symbol table instead of the theorem's
dependency set.** `check --axioms <file> <theorem>` answers that in one command, and I should
have run it before costing the route.

**What I also wrongly believed:** that `lessThanIntro`/`lessThanElim` blocked the cut.
`IntegerOrderOnTheCut` had discharged both on 2026-10-30 — the genuinely hard part was already
done, and a stale comment in that file still said it blocked 17.13/17.14/17.15.

**The resolution** was to prove the CONSTRUCTIONS natively on `naturalWellOrdering` and keep
Euclid taking the certificate as a HYPOTHESIS. That last choice is the load-bearing one: it
keeps the whole development off `gcd`/`div`/`mod`, so nothing here rests on what queue item 2
deletes.

**The process lesson, which is the reusable part:** a deferral note that names a DEPENDENCY
("waits on Gauss") rather than a measured missing theorem will keep being wrong, because the
dependency is the first thing that changes. Three successive versions of 17.14's note blamed
Gauss's open half; when Gauss closed it turned out the corollary never needed it at all. Name
the theorem, and measure it with `--axioms`.

## 12. `polynomial` cannot see inside a term with a Nat subterm (LIVE)

`[using polynomial(rational)]` fails with `expected sort 'Q', got 'Nat'` when the goal holds a
power whose exponent is a `Nat` — which is any `qpower(s, k)`. Hit twice in 17.14.

**Workaround:** state the algebraic law over ABSTRACT ℚ variables and `specialize` it at the
compound term, so the tactic never descends into the exponent. `addingAndSubtractingCancels`
and `theNegatedProductFromZero` in `std/rational/integer-division.b4m` exist only for this.

Related: `polynomial` also cannot CONSUME a cited equation as an input (it proves identities,
not consequences), so a rearrangement like `0 = X + r·t ⟹ X = r·(−t)` must be done by explicit
`rewrite` steps.

## 13. The accelerant param-guard gap, half fixed (ENGINE)

**FIXED (`f41c60f`):** a `simplify` whose rewrite set mentions a lemma quantified over a
MODEL-REFINED sort could not transfer at all — `simplify` abstracts the caller's `fix n` into
a schema param, the relativized lemma leaks `good(p1)`, and a param sits in no `fix`'s scope
so nothing can discharge it. `paramGuards`/`wrapParamGuards` exist for exactly this but were
wired only into `finishReorder`; `produceSimplify` never called them. Also `paramGuards` read
the SOURCE binder's refinement, which is `none` precisely when the model introduces it.

**STILL OPEN, same family:** `polynomial`'s hardcoded rule set cites ring lemmas by well-known
name with SOURCE-SPACE formulas, so under a transfer the cite claims a guard-free universal
while the resolved theorem is relativized. Different mechanism — a citation, not a param guard
— and the hardcoded rule set makes it a design question rather than a one-line fix.

**Process note:** I mis-diagnosed the fixed half twice (wrong refinement lookup, then wrong
accelerant path) by reasoning from the code's own comments, which described the mechanism as
if it were already wired everywhere. One `std.debug.print` settled it. Instrument first.

## 14. `theSubject` is a PARAMETER, not a fixed value — and I got this backwards

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

Three times in this chapter I wrote a theorem whose conclusion followed from fewer hypotheses
than it listed, and twice the name claimed more than the statement.

- `eisensteinOnTheCut` (deleted): concluded "not every coefficient is divisible", which under
  Eisenstein's own hypotheses is *immediate* from `N ∤ a_n`. The dead-step lint caught it —
  four unused hypotheses including the factorization itself.
- `eisensteinRulesOutAnIntegerFactorization` (committed, then found wanting): same conclusion,
  same problem. It does not rule out a factorization; the contradiction needs the DEGREE
  bookkeeping (both factors' degree bounds summing below n, so `N | a_i` for `i < n` plus
  vanishing above the degree sum forces `N` to divide *every* coefficient). The strict check
  and the dead-step lint both passed, because every step was valid — the statement was just
  weaker than its name.
- `theModulusCannotDivideEveryProductCoefficient` (fixed in `8bf3251`): hypothesis constrained
  `mod_n.N` while the conclusion spoke of an independent `QN`. `--axioms` showed BOTH
  congruence axioms in the base, which was the tell, in output I had already run.

**The pattern:** the checker verifies that the steps prove the stated formula. It cannot tell
you the formula is weaker than what you meant, or that the name oversells it. Three tools do:
the **dead-step lint** (unused hypotheses are the loudest signal), **`--axioms`** (two
independent constants where one was intended shows up as two axioms), and **asking what the
conclusion rules out** before naming it. I used the first two only after being surprised.

**The same root cause runs through §14 and the costing errors in §11: reasoning from the SHAPE
of a declaration or a statement instead of probing it.** Every one of these was settled in
minutes by a scratch file, a `--axioms` run, or a `std.debug.print` — and in each case I
produced a confident wrong answer first. The corpus has cheap instruments; the failure is not
reaching for them before forming a view.

## Numbering

There is no §10 — the list grew by insertion and the gap is left rather than renumber
references in commit messages that cite these by number.
