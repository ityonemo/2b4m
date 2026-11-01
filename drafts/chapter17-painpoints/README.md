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

- **`simplify` loops or stalls** where an explicit `rewrite` works. Three separate sites:
  a rewrite-limit loop (`theDenominatorCancels`'s precursor), `'ZERO' vs 'qcoeff(p, qdegree(p))'`
  normal-form mismatch, and `'b' vs 'c'`. Rule of thumb that emerged: when both sides need a
  *different* equation applied, chain `rewrite`s; `simplify` is for one shared normal form.
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

## 11. Euclid's Lemma is unreachable on ℚ's integer cut (BLOCKS 17.14 and 17.15)

**Measured 2026-11-01, after Lemma 17.12 and Gauss's d = 1 branch were both closed.**

Corollary 17.14 and Theorem 17.15 are each ONE theorem from done, and it is the same theorem:
from `r | a·b` on the cut plus `gcd(r, b) = 1`, conclude `r | a`.

Everything else is built. 17.14's "multiply p(r/s) = 0 through by s^n" is
`clearingTheDenominatorGivesTheClearedSum`, and the two end-splits
(`theClearedSumSplitsOffTheConstantTerm` / `…TheLeadingTerm`) deliver exactly
`r | a_0·s^(n+1)` and `s | a_n·r^n`. 17.15's minimal-index argument has its
least-witness extraction in `std/rational/natural-wellordering.b4m`.

**Why it is blocked.** Coprimality on the cut is the QUANTIFIED reading — every common
divisor divides ONE — which does not give Euclid without Bézout. And the cut has no Bézout
because it has no division algorithm.

**Three routes, all costed:**

1. Transfer ℤ's `bezout` through `IntegersInRational`. Blocked by pain point 2 (no model
   COMPOSITION): `bezout` is in `std/integer/divides.b4m`, a different namespace from the
   mapped `integer`, and the transfer re-checks the source proof — so it demands mapping that
   file's `pow`, `div`, `mod`, `abs`, `gcd`, `lcm` plus `order` and `wellordering`. Three of
   those are the total functions queue item 2 deletes.
2. Prove Bézout on the cut from `naturalWellOrdering` (least positive element of {ar+bs}).
   Needs division-with-remainder on the cut, which is also absent.
3. Wait for the de-totalization, then take route 1 against a smaller, stable surface.

Route 3 is the right one, and the queue already schedules it. **This is the only thing left
in chapter 17.**

**The lesson for the pain-point list itself:** three successive versions of 17.14's deferral
note blamed Gauss's open half. Gauss is now closed and the corollary turns out not to need it
at all — the proof is direct. A deferral note that names a *dependency* rather than a
*measured missing theorem* will keep being wrong, because the dependency is the first thing
that changes. Name the theorem.
