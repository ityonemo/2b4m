# Accelerated-tactic registry

An **accelerated tactic** is a decision procedure whose verdict the checker can
accept without a kernel derivation. Accelerated tactics are the deliberate
exception to bpa's otherwise-closed trust story: the kernel checks every
ordinary step, but an `.accelerated` step stands on the named procedure being
correct. Each invocation either **emits kernel steps** (a full chain of
kernel steps, staying kernel-checked) or **accelerates** (it trusted the procedure without a chain).

The trust is disclosed, never silent:

- every accelerated step **marks** its theorem accelerated with the tactic's
  name;
- citing an accelerated theorem (directly, via `simplify` rules, as a
  `tautology` premise, or through a schema instantiation whose proof cites one)
  inherits the accelerated-tactic names **transitively**;
- the summary line reports the split, e.g.
  `OK: 9 declarations, 5 theorems proven (4 accelerated: tautology)`;
- by default `bpa check` **rejects every accelerated step with a located
  error** — the goal must be kernel-checked. The accelerated verdict is accepted only
  under `--fast` (which then discloses it under a loud accelerated banner).

A cross-file `import` citation is itself a `using` word: under `--fast` (or
`--fast-only import`) the citation is *admitted* by matching the cited
statement, disclosed alongside any accelerant admissions. This trusts the
citation shape only — a demanded imported theorem is still re-checked in its
own file.

Tactics are **certificate-first**: an invocation that can emit ordinary
kernel steps does so and stays kernel-checked. Certificates are produced by an
ordered **certifier chain** (equation/order/exists → mixed-skeleton → Farkas →
future Cooper-replay/manual), walked first-success-wins; each link either
emits kernel steps or **declines with a reason**. When every link declines,
the default is a hard error listing each link's reason (so a valid goal on a
thin theory names the missing symbol/lemma to add — an actionable fix, not
"write a manual proof"); `--fast` accepts the accelerated verdict for that
goal, marking that use accelerated only. Certificate stages grow over time,
monotonically shrinking what needs `--fast` with no surface change.

The same elaborate-by-default / `--fast`-accelerated split applies to the
equational tactics `polynomial` and `assoc_commut` (below): their default path
emits kernel-checked rewrites citing the theory's proven ring/AC lemmas, and
only `--fast` presumes the vocabulary's algebra structurally and accelerates. A
tactic is acceleration-shaped precisely when it depends on a well-known stdlib
function and presumes its behavior — the acceleration discloses that
presumption; the theory argument (`polynomial(peano)`, `arithmetic(peano)`)
pins it to a vetted theory.

## Naming couplings — hardcoded defaults are fine, but MUST be overridable

Accelerators routinely *expect* conventional names: `arithmetic`/`polynomial`
presume a well-known `add`/`mul`/`succ`/`ZERO` vocabulary; a schema-driven tactic
may expect an `induction`. (`extensionality` sidesteps this entirely — its
lemmas are named EXPLICITLY as args, so there is no expected name to couple on.)
**Hardcoding such a default name is fine** — it keeps the common case terse. The
invariant is not "no hardcoded strings"; it is:

> **Every name an accelerator expects MUST be overridable — the user must be
> able to satisfy the expectation from a bpa file, never from editing the
> checker.** A hardcoded name that is *neither* overridable *nor* structurally
> derivable is a silent, unescapable coupling, and is forbidden.

The override mechanism is **the language's own remapping**, not a bespoke
argument on each tactic:

- **`alias`** overrides a single name. Your theory proves set-equality as `setEq`?
  `theorem addZeroLeft = mytheory.zeroPlus` and `arithmetic` finds it. (This is exactly
  what the `aata/*.md` files do — aliasing the book's notation onto the std
  names — and what `set.bpa` did aliasing the element sort.)
- **`model`** overrides a whole signature at once — the industrial-strength
  version of the same idea (see `MODEL-DESIGN.md`). Aliasing remaps one name; a
  `model` remaps an entire structure's worth of names, so a structure that spells
  everything its own way can satisfy an accelerator's expectations wholesale.
- The **theory argument** (`arithmetic(peano)`) already pins *which* vetted
  theory's names to use — itself a form of override/selection.

**Prefer structural derivation when the entity is recoverable from a cited
lemma's shape**, and prefer **explicit citation** when the entity is a lemma the
proof can name. `extensionality` takes its extensionality lemma + per-operator
unfold lemmas as EXPLICIT args, and reads the element sort off the cited lemma's
obligation binder — so there is no expected name to override at all (the
strongest form: zero coupling). This is preferred where available; a
hardcoded-but-overridable default is the acceptable fallback.

Historical note: `ext` (now `extensionality`) once looked the element sort up by
the literal name `"Universe"`, and once ENUMERATED the theory scope to find its
`<op>Member`/`<op>Apply` unfold lemmas by shape. Renaming the sort broke it; the
scope-scan couldn't survive the fetch-only demand engine and mis-derived
irregular names (`identityFn` → `identityApply`, not `identityFnApply`). Both were
fixed by making the couplings explicit/structural — the canonical example of this
rule.

## Registered accelerated tactics

### `tautology` — propositional consequence

- **Module**: `src/smt.zig`
- **Surface rule**: `[using tautology ref1 ... refN]` (refs are premise steps or
  statements; the goal must follow propositionally)
- **Verdict semantics**: atoms are the maximal subformulas that are not
  `and`/`or`/`not`/`->` (predicates, equations, quantified formulas — all
  opaque). `.valid` means premises AND not(goal) has no truth assignment over
  those atoms. Failures are located errors, never accelerated: a satisfiable
  skeleton reports its countermodel; more than 16 distinct atoms reports the
  cap.
- **Certificate status**: certificate-first (B2). Every valid goal within
  the step budget replays as ordinary kernel steps — an inline excluded
  middle plus or_elim per split atom, structural derivation at the leaves —
  so typical uses stay kernel-checked and check green by default. The accelerated
  verdict is admitted only under `--fast` as the over-budget fallback, marking
  that use accelerated only.

### `arithmetic` — linear (Presburger) arithmetic over Nat

- **Module**: `src/presburger.zig` (decision), `src/farkas.zig` (refutation
  search for the Farkas link)
- **Surface rule**: `[using arithmetic ref1 ... refN]`, or
  `[using arithmetic(<theory>) ref...]` naming a theory module. Refs are premise
  steps or statements. **Theory resolution**: bare `arithmetic` resolves the
  vocabulary + certificate lemmas by well-known name in **local scope** (the
  self-contained case). `arithmetic(<theory>)` resolves them against an
  imported module's scope regardless of local aliases — so a downstream or
  subdomain file elaborates without dragging the arithmetic vocabulary into its
  namespace. A **named** theory must provide every symbol the goal uses (a gap
  is a hard error naming it); a missing certificate *lemma* makes the relevant
  certifier decline (soft), surfaced at the terminal.
- **Fallback**: `[using arithmetic ... fallback(<thm>)]` names a manually-proven
  theorem to cite when the certifier chain declines a valid goal — instead of
  the hard error (default) or the accelerated verdict (`--fast`). The step stays
  **kernel-checked** (not accelerated), and any accelerated-tactic names `<thm>`
  itself carries are inherited. This is for goals the Presburger procedure
  *decides* but no certifier can *emit* — e.g. multi-fixed-variable `∀∀∃`
  (`tests/cases/cooper_gap.bpa`: `sumParity` reduces to the cooper-certified
  single-variable `evenOrOddArith` via a hand proof, and `fallback` cites it).
  The matcher accepts `<thm>` in either of two forms — **every goal `arithmetic`
  can decide is fallback-supportable**:
  1. **α-equal**: `<thm>`'s statement IS the goal → cite it directly.
  2. **specialized instance**: the goal is `<thm>` instantiated —
     `<thm> = ∀x⃗; A₁ -> … -> Aₘ -> C`, and `C` at some witnesses `x⃗` α-equals
     the goal. The matcher infers `x⃗` by first-order-matching `C` against the
     goal, discharges each antecedent `Aᵢ(x⃗)` from a supplied ref whose formula
     matches it (order-independent; the step's other refs are the `arithmetic`
     decision premises), and EMITS a `theorem_ref → forall_elim(x⃗) →
     modus_ponens(refs)` chain the KERNEL re-checks — so a mis-inferred witness
     can never pass. (`tests/cases/arithmetic_fallback_specialize.bpa`;
     `std/integer-divides.bpa`'s `modDifferenceIsMultiple`, cited at `b:=n, a:=r`
     from `aata/2.2-division-algorithm-exercises.md`.)
  `fallback` is a contextual modifier on `arithmetic` only (not a keyword —
  `fallback` is an ordinary identifier elsewhere); it is the
  decision-vs-certification escape hatch for a decision-backed procedure, so
  the structural presumers (`assoc`/`assoc_commut`) will never carry it.
- **Fragment**: terms over `ZERO`, `ONE`, `succ`, `add`, and `mul` where one
  side folds to a literal — all resolved by those well-known names in the
  theory scope; atoms `=`, `!=`, and `less_than`; the propositional
  connectives; `forall`/`exists` over Nat. Anything else — foreign
  predicates, nonlinear terms, quantified subformulas that are not wholly
  arithmetic — is an **opaque propositional atom** in an SMT combination
  (DPLL over the mixed skeleton in `src/smt.zig`, with the Presburger
  engine as the theory solver; refuted skeleton models are skipped).
  Opaque atoms are never instantiated: a goal needing a quantified opaque
  subformula's internals simply reports a countermodel naming it.
- **Verdict semantics**: Nat is modeled as the nonnegative integers (every
  variable carries an implicit `>= 0`). `.valid` means premises AND
  not(goal) is unsatisfiable, decided by Cooper's quantifier elimination
  (complete for Presburger arithmetic; divisibility atoms handle the
  periodicity, i128 arithmetic is overflow-checked, and elimination blowup
  hits an explicit work budget — both are honest errors). A satisfiable
  negation reports countermodel values for the fixed variables when a small
  witness exists.
- **Certificate status**: certificate-first (C2a–C2c, premise handling,
  D2). Goals replay as kernel steps when the well-known peano lemmas
  resolve in the use site's scope: ground and universally-quantified
  linear *equations* normalize to succ-towers over sorted sums (recursion
  axioms plus `addZeroRight`/`addSuccRight`/`mulZeroRight`/`mulSuccRight`/
  `addIsAssociative`; the residual permutation is a chain of
  `addIsCommutative`/`addLeftSwap` rewrites); *order* goals synthesize the
  difference witness d, certify `add(a, succ(d)) = b`, and close with a
  `lessThanIntro` instance; *existentials* search a constant witness tower
  and reduce via `exists_intro`. *Hypotheses* (cited `less_than`/`=`
  steps) enter by witness substitution: each order premise is
  `lessThanElim`-unpacked and its flipped witness equation becomes a
  ground rewrite rule, so difference-logic chains (including transitivity)
  certify; the conclusion exports back through `exists_elim`. When the
  rewrite-normalizer declines an equation goal that nonetheless follows by
  CANCELLING an equality premise — the premise's sides don't occur literally in
  the goal, so no rewrite fires, but the goal is a linear COMBINATION of it (e.g.
  `sub(a, r) = mul(b, q)` from `add(mul(b,q), r) = a`) — the *premise-combination*
  path (`premiseCombinationCert`) certifies it: for a premise `P_l = P_r` and goal
  `G_l = G_r` it proves the pure identity `add(P_l, G_l) = add(P_r, G_r)` via the
  ordinary equation join, rewrites `P_l→P_r` with the premise, and closes with
  `addCancelLeft` — all kernel-checked, so a wrong combination fails the join.
  Needs `addIsCommutative`/`addLeftSwap`/`addCancelLeft` in scope. *Mixed
  skeletons* (D2) replay as tautology-style case splits whose boolean dead
  ends close by deriving the conflicting arithmetic literal from the
  branch's assumptions, then `absurd`. *Farkas* (`src/farkas.zig`) certifies
  difference-logic constraint combinations — combining SEVERAL hypotheses,
  which the single-atom order cert cannot: an infeasible cycle `x < ... < x`
  (folded with `lessThanTransitive`), order composition (`a<b -> b<c -> a<c`, a
  path fold), an arbitrary/`false`-shaped conclusion (fold a cycle, contradict
  with `lessThanIrreflexive`, `absurd`), COEFFICIENT SCALING (`mul`-by-literal
  bounds scaled via `multiplicationPreservesOrder`), and SUMS of distinct-
  variable bounds (`a<b ∧ c<d -> add(a,c)<add(b,d)`, via
  `additionPreservesOrder` + `addIsCommutative` + transitivity). *Cooper-replay*
  (the `cooper` link, `src/Engine/ProveTask/presburger.zig` trace + `src/Engine/ProveTask/Prove.zig`
  `cooperInduction`) closes the **quantifier-alternation tail**: a
  `forall x…; exists y; body` goal replays its Cooper elimination as
  kernel steps — for a period-1 trace, a boundary witness under an `or_intro`;
  for a period-D trace (e.g. the parity `evenOrOdd`, `forall x; exists y; x=2y ∨
  x=2y+1`), a SYNTHESIZED induction on the fixed variable (predicate `P(k)` =
  the body, base `P(ZERO)`, step `P(k)→P(succ(k))` by unpacking the IH witness
  and shifting it per residue-class arm, then `instantiate induction`). Still
  accelerated when it cannot elaborate, honestly disclosed: quantified
  arithmetic subformulas used as skeleton atoms, and multi-variable / nested
  (`∀∃∀`) alternation (the cooper link declines these, so they fall to
  `--fast`).

### `polynomial` — nonlinear ring identities

- **Module**: `src/Engine/ProveTask/Polynomial.zig` + `Prove.zig` (`producePolynomial`) for the
  kernel-checked path; `polyNormForm` for the accelerated path)
- **Surface rule**: `[using polynomial(<theory>)]` / `[using
  polynomial_quantified(<theory>)]`. Theory-parameterized exactly like
  `arithmetic` (bare = local scope; `(theory)` = that imported module).
- **Elaborated path is the DEFAULT and is NOT accelerated.** Under the default,
  `polynomial` canonicalizes both sides to a sorted sum of sorted monomials by
  *resolving the theory's ring lemmas* (`mulAddDistrib*`, `mulIsAssociative`,
  `mulLeftSwap`, one/zero folds) and emitting a rewrite chain that CITES them —
  every step kernel-rechecked. Sound relative to the theory's proofs;
  kernel-checked; not accelerated. A theory too thin (lemmas absent) is a located
  decline, not an acceleration.
- **Accelerated verdict (only under `--fast`)**: skip the lemmas entirely and
  compare the *bare syntactic semiring normal forms* (`polyNormForm` —
  flatten/sort add/mul trees assuming commutativity, associativity,
  distributivity, 0/1 identities). `.valid` = the two normal forms are
  `alphaEq`. A false identity is still REJECTED (the procedure decides). What
  is accelerated (not kernel-checked) is the **presumption that `add`/`mul` form a
  commutative semiring** — the theory's own laws are never checked, so a
  pathological/wrong `add`/`mul` could make the presumed identity false.
  Accelerated-tactic name: `polynomial`.
- **Why an accelerated tactic at all**: it decides on theories too thin to
  kernel-check, and it trusts the ring structure of symbols it does not control —
  the honest, accelerated counterpart to the default's kernel-discharged trust.
- **No `fallback` (settled — don't relitigate).** Unlike `arithmetic` (whose
  Cooper decision genuinely exceeds what the certifier can emit — the ∀∀∃ /
  nested-alternation tail — so `fallback` bridges a real gap), `polynomial`'s
  kernel-checked path and accelerated path decide the *same* fragment: semiring
  identities over `add`/`mul`. **When the ring lemmas are present, the
  kernel-checked path always succeeds** on a true identity (terminating
  normalization, every rewrite cites a present lemma) — stress-tested to a
  wide-sum 4th power (256 monomials), 100-factor reversed products,
  `succ`-atoms, and 0/1 folds. The only case the accelerated path "wins" is a
  **thin theory** (`needs <lemma> in scope`), whose fix is to *add the lemma*,
  not to hand-prove around it. So there is no decision-vs-certification gap for
  `polynomial` to bridge, and it carries no `fallback`. (The audit also
  surfaced — and fixed — a stale-slice OOB crash in the accelerated normalizer
  on large expansions: `tests/cases/polynomial_oob.bpa`.)

### `extensionality` — extensionality-reduction

- **Module**: `src/Engine/ProveTask/Prove.zig` (`produceExtensionality` /
  `produceExtensionalityQuantified`).
- **Surface rule**: `[using extensionality(<extLemma>) <unfold lemmas…>]` for a bare
  `LHS = RHS`, or `[using extensionality_quantified(<extLemma>) …]` for
  `forall …; LHS = RHS`. The extensionality lemma and the per-operator unfold lemmas
  are EXPLICIT citations (no theory scan, no well-known names).
- **A STRUCTURE tactic**: the structure is *extensionality*; the SAME tactic proves
  set equations (`extensionality(extensionality) unionMember …`) and function
  equations (`extensionality(funcExtensionality) composeApply …`), and any future
  extensional theory. Prior art: Lean's `ext`.
- **What it does (emits kernel steps)**: reads the element sort **structurally** off
  the cited extensionality lemma's pointwise binder (`forall x: <elementSort>; …`);
  instantiates the lemma at (LHS, RHS) to reduce `LHS = RHS` to its pointwise
  obligation(s); for each obligation `fix x: <elementSort>`, unfolds the operators
  with the cited characterization lemmas, and closes the residue by its shape:
  - **set / predicate model**: the residue is propositional over `member(x, ·)`
    atoms → closed by `tautology`'s certificate (replayed as kernel steps).
  - **function / equational model**: the residue is an equation
    `apply(f, x) = apply(g, x)` → closed by the rewrite join (the `simplify`
    machinery over the cited `<op>Apply` lemmas).
  Then `forall_intro` each obligation and `modus_ponens` the chain to the equation.
  Like every accelerant it is a generated schema the kernel re-checks; `bpa debug
  accelerant` prints it.

### `assoc_commut` — associative-commutative reordering

- **Module**: `src/Engine/ProveTask/Prove.zig` (`produceAssocCommut` / `acPlan`)
- **Surface rule**: bare `[using assoc_commut]` / `[using assoc_commut_quantified]`
  (well-known `add`/`mul` triple), or the explicit form `[using
  assoc_commut(assoc, comm, swap)]` supplying the AC lemmas for a **custom
  operator** (operator recovered from the commutativity lemma's shape). Trailing
  refs are distributivity/pre-normalization lemmas. Exactly 0 or 3 args.
- **Kernel-checked path is the DEFAULT and is NOT accelerated.** Re-associate +
  bubble-sort by the operator's assoc/comm/swap lemmas, emitting kernel-checked
  swaps that cite them. The **explicit-triple form ALWAYS emits kernel steps** (the
  triple is checkable) — it has no accelerated path.
- **Accelerated verdict (only under `--fast`, bare form only)**: compare sorted
  multisets of summands structurally, resolving NO assoc/comm/swap lemma.
  `.valid` = same sorted multiset. A different multiset is still rejected. What
  is accelerated (not kernel-checked) is the **presumption that the operator is
  associative-commutative** — never checked, so an operator that is not
  (subtraction, function composition, matrix mul, …) could make the presumed
  reordering false. Accelerated-tactic name: `assoc_commut`.
- **Relation to `polynomial`**: `assoc_commut` is the single-operator special
  case; `polynomial` additionally distributes `mul` over `add`. Same trust
  story — both presume the vocabulary's algebra where the kernel-checked path
  proves it.

### `assoc` — associativity-only reordering

- **Module**: `src/Engine/ProveTask/Prove.zig` (`produceAssoc`)
- **Surface rule**: `[using assoc(assocLemma)]` / `[using assoc_quantified(assocLemma)]`.
  The associativity lemma is **REQUIRED** (exactly one arg — no bare form, no
  `add`/`mul` assumption); the operator is recovered from the lemma's shape
  `f(f(a,b),c) = f(a,f(b,c))`. The non-commutative sibling of `assoc_commut`
  (for group theory etc.), where reordering is forbidden — only re-nesting.
- **Kernel-checked path is the DEFAULT and is NOT accelerated.** Right-nest each
  side by the cited associativity rule (confluent + terminating → canonical
  form), `alphaEq`-compare, and emit a kernel-checked rewrite chain that cites
  the lemma. Sides that differ by more than associativity are a located error.
- **Accelerated verdict (only under `--fast`)**: structurally right-nest both
  sides over the operator and compare, WITHOUT emitting/kernel-checking the
  rewrite chain. A shape that isn't associativity-equal is still rejected. What
  is accelerated (not kernel-checked) is the **presumption that the operator is
  associative** — the rewrite is not discharged against the kernel.
  Accelerated-tactic name: `assoc`. (Unlike `assoc_commut`, the lemma is always
  resolved even in the accelerated path, since it's required to identify the
  operator; the acceleration is for the *undischarged rewrite*, not for an
  unresolved lemma.)
