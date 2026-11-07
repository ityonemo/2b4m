# Accelerated-tactic registry

An **accelerated tactic** is a decision procedure whose verdict can be provisionally
accepted without a kernel derivation.  This primarily serves to prune the evaluation
tree in `--fast` mode.  In strict mode, an accelerated tactic should be able to
generate a "certificate", which is a inspectable, machine generated theorem that
gets checked and placed in the internal pool of facts.

For each tactic's surface syntax, examples and errors, see `../GUIDE.md`. This file is
about the trust boundary.

The trust is disclosed, never silent:

- citing an accelerated theorem (directly, via `simplify` rules, as a
  `tautology` premise, or through a schema instantiation whose proof cites one)
  inherits the accelerated-tactic names **transitively**;
- the summary reports the split on its own line:

      OK: 9 declarations, 5 theorems proven
        — NOT FULLY VERIFIED: 3 theorem(s) accelerated (admitted, not proved): tautology

- by default `2b4m check` **rejects every accelerated step with a located
  error** — the goal must be kernel-checked. The accelerated verdict is accepted only
  under `--fast` (which then discloses it under a loud accelerated banner).

A cross-file `import` citation is itself a `using` word: under `--fast` (or
`--fast-only import`) the citation is *admitted* by matching the cited
statement, disclosed alongside any accelerant admissions. This trusts the
citation shape only — a demanded imported theorem is still re-checked in its
own file.

Tactics are **certificate-first**: an invocation that can emit ordinary kernel steps does
so and stays kernel-checked. Certificates come from an ordered **certifier chain**
(equation/order/exists → mixed-skeleton → Farkas → Cooper), walked first-success-wins;
each link either emits kernel steps or **declines with a reason**. When every link
declines, the default is a hard error listing each reason, so a valid goal on a thin
theory names the missing symbol or lemma to add:

    error: 'arithmetic' is valid but no certifier could prove it here:
      - equation/order/exists: form not in certification scope
      - mixed-skeleton: form not in certification scope
      - farkas: theory lacks symbol 'less_than'
      - cooper: form not in certification scope
    use --fast to accept the accelerated verdict

Certificate stages grow over time, monotonically shrinking what needs `--fast` with no
surface change.

A tactic is acceleration-shaped precisely when it depends on a well-known stdlib
function and presumes its behavior — the acceleration discloses that
presumption; the theory argument (`polynomial(peano)`, `arithmetic(peano)`)
pins it to a vetted theory.

## Rules for `--fast` evaluation truncation

`--fast` may succeed where strict fails in exactly these cases:

- **No certifier covers the goal.** The decision procedure determines the goal is true but
  no certifier can build a proof of it. (Resolved by naming a manual `fallback(thm)`.)
- **A trusted fact is incorrect.** A cited, well-known, or `fallback` fact is trusted on its
  STATEMENT but not checked; strict demands the proof behind it and may find it does not hold.

A decision's "no" must be read for WHAT IT ESTABLISHED. A genuine countermodel adjudicated
the statement and found it false — both modes reject. A refutation resting on an **abstracted
opaque subterm** (`sumTo(succ(k))`, `mul(a, b)`) adjudicated *nothing*: the decision replaced
the subterm with a fresh variable free to range, so the "countermodel" is an artifact of that
abstraction, and a cited premise may well pin the subterm's value. That is an **abstention** —
`--fast` accepts it and strict proceeds to the certifier.

**So the decision gate runs in BOTH modes, but an abstention must not be treated as a
rejection** — doing so lowers strict to the decision's reach and fails goals that are true
and certifiable. `examples/gauss.b4m` is the gate for exactly that.

## Where the boundary falls, per word

`--fast` runs the proof's shape checks and each accelerant's own interface — including its
DECISION — and declines only to EMIT and kernel-check the certificate.

**The one-line rule: the decision is a FILTER, the certificate is the AUTHORITY, and
`--fast` keeps every filter and drops the authority.**

| word | KEPT under `--fast` | DROPPED |
|---|---|---|
| `arithmetic` (+`_q`) | premise resolution; well-known symbol binding (incl. `nonneg`, which picks the ℕ-vs-ℤ fragment); the Presburger/mixed **decision** — admits only on `.valid`, fails on a countermodel or an undecidable shape | the certifier chain and its kernel certificate; `fallback(thm)` is never consulted |
| `simplify` (+`_q`) | cited rule STATEMENTS (via `elaborateFactStatement`, no ProveTask); rule orientation; **both sides normalized to a shared normal form** | the `EqCert` join certificate |
| `polynomial` (+`_q`) | goal has add/mul structure; ring vocabulary completion (`completePolyOps`, demanded in the read pass); **both sides canonicalized to one form** | `finishReorder`'s certificate |
| `assoc` (+`_q`) | the lemma ARGUMENT's statement and its `f(f(a,b),c) = f(a,f(b,c))` shape; **both sides right-nested to one normal form** | `finishReorder`'s certificate |
| `assoc_commut` (+`_q`) | arg count (0 or 3); cited rule statements; distribution pre-pass; **both sides sorted to the same summand multiset** | `finishReorder`'s certificate |
| `tautology` | premise step resolution; **`smt.tautology` — the goal is a propositional consequence** | the `TautAst` certificate |
| `chain` | goal is an equation; ≥1 cited equation; each equation's statement and eq-shape; **the BFS connects the goal's two sides** | the path's rewrite-step certificate |
| `extensionality` (+`_q`) | the ext lemma and every unfold lemma resolve; **`emitExtSetResidue`'s `smt.tautology` closes the pointwise obligation** — reached by running the emitter and discarding its steps, since the decision lives inside it | packaging the emitted steps as the synthetic schema |
| `model` | the model name resolves and is a model; exactly one cited theorem; **the transferred statement α-matches the claim** | the per-axiom OBLIGATION COVERAGE check (below) |
| `import` | the import resolves; exactly one cited theorem; **the imported statement α-matches the claim** | nothing further — citing a proven fact IS the justification, so there is no certificate to emit |
| `specialize` | the head resolves; its args elaborate in the caller's scope; **the instance's conclusion α-matches the claim** — one ∀ opened per arg at the elaborated argument, then some suffix of the `->` chain equals the goal (the antecedents before it are the refs' discharges plus refined-binder guards) | proving the instance, and discharging those guards from the caller's context (`withGuardPremises`) |
| `instantiation` | — | **nothing. Never trustable at all**: an instantiation's content IS the body's proof at the args, which is the only soundness gate |

## `model` — unchecked obligation coverage

Strict rejects a partial model whose cited theorem needs an unmapped axiom (the guard at
`Prove.zig:403`: "giving an axiom a free transferred leaf would let an unmapped axiom
through"). `--fast` does not reach that check, so a consumer can be handed, say, an
equivalence relation whose transitivity nothing supplied.

## The three phases, and the tactic union

Every tactic is one file under `src/Engine/ProveTask/Accelerants/` — a struct that is one
variant of `Prove.Tactic`, a `union(enum)` with a variant per trustable word (the
`_quantified` variants share a file and carry a `quantified` field). The scaffolding drives
each step through three phases, dispatching once per phase with
`switch (tactic) { inline else => |a| a.<phase>(…) }`:

The directory also holds the lowercase ENGINE modules the tactics share, layered so that no
engine imports a tactic and no two engines import each other: `symbols.zig` (the arithmetic
vocabulary table) and `rewrite.zig` (matching + innermost rewriting) are leaves;
`presburger.zig` (the ℤ decision) and `farkas.zig` (refutation search) sit on `symbols`;
`ac.zig` (the AC / succ-tower substrate) sits on `rewrite` + `symbols`; `polycanon.zig` (the
ring canonicalizer) sits on `ac`; `common.zig` is the tactic-side toolbox (goal abstraction,
premise bookkeeping, the fused decide) and `testrig.zig` the unit-test rig.

| phase | hook | may park? | who runs it |
|---|---|---|---|
| READ — demand what later phases will read | `read` | **yes** — the only phase with the suspend channel | both modes |
| DECIDE — accept or reject from what phase 1 fetched | `decide` | no | both; `--fast` admits on accept and stops |
| CERTIFY — build the synthetic schema the kernel checks | `certify` | no | strict only |

Phase 1's standard citations — the head, lemma args, refs — are not written per tactic: the
scaffolding derives them from three consts each tactic declares (`schema_slot`,
`premise_shape`, `lemma_args`) and demands them mode-appropriately, PROOFS under strict and
STATEMENTS under `--fast`. `read` is for whatever else a decision needs (`arithmetic`'s
well-known operator symbols, `polynomial`'s ring vocabulary in the selector's file).

**The scaffolding rule: no tactic-specific logic outside the union.** The read passes,
`admit`, `demandUsing`/`lowerUsing`, `accelerantPremises`, root seeding and `RefScan` contain
no rule-name comparison, no word list, no `switch (word)` arm naming a tactic. A behaviour
that must vary per tactic becomes a const or a phase hook on the tactic. The converse holds
too: a tactic file holds no scaffolding.

Most tactics' `decide` is still FUSED with `certify` — `common.decideFused` runs the producer
in admit mode and reads whether it reached its accept point. The contract is honoured at the
scaffolding; unfusing a producer is that tactic's own work. `specialize` is unfused: its
decide needs something certify never computes (the α-match against the elaborated instance).

## Building a tactic's decide

A decision admits on exactly ONE outcome: **the goal is TRUE.** A refutation fails, and a
shape the procedure cannot handle also fails — "I can't decide this" is not a verdict. Each
word has a regression fixture named `*_false_fast.b4m` beside it, asserting a false goal is
still refused.

Four rules, for a fused producer:

1. **Admit AFTER the decision, not before.** Clear `producer_premise_refs` when you do, or
   the admitted path resolves global rule names as step labels.
2. **But admit BEFORE a `fallback(thm)` resolves.** Resolving it needs that fact DEMANDED,
   which admit mode has not done. What adjudicates the goal is the cited theorem, whose own
   proof the strict pass checks.
3. **Demand in phase 1, never from inside decide or certify.** Parking from a producer via
   `error.Recover` reads as a diagnosed REJECTION, and rejecting a step DROPS ITS LABEL from
   the walk — surfacing later as "unknown reference" at the next step that cited it.
4. **Read a statement with the right-weight tool.** `elaborateFactStatement` reads a fact's
   STATEMENT and racks NO ProveTask, which is what a decision needs. Do NOT use it to PROBE
   readability: it writes diagnostics on failure, so `--fast` would report errors strict
   never gives. A name the file does not declare is a typo — leave it to the process pass,
   which diagnoses it with position (`Prove.citationDeclared`).

Some decisions hide INSIDE the emitter — `extensionality`'s pointwise obligation is closed
by an `smt.tautology` call inside `emitExtSetResidue`. There, admit means running the
emitter and discarding its steps.

**The cost objection does not survive measurement.** `--fast` over `std` is 16.8s against
strict's 233.7s. The decision is far cheaper than the certificate it replaces, which is why
the certify-first ordering exists at all.

## Naming couplings — hardcoded defaults are fine, but MUST be overridable

Accelerators routinely *expect* conventional names: `arithmetic`/`polynomial` presume a
well-known `add`/`mul`/`succ`/`ZERO` vocabulary. **Hardcoding such a default name is fine** —
it keeps the common case terse. The invariant is not "no hardcoded strings"; it is:

> **Every name an accelerator expects MUST be overridable — the user must be able to satisfy
> the expectation from a 2b4m file, never from editing the checker.** A hardcoded name that
> is *neither* overridable *nor* structurally derivable is a silent, unescapable coupling,
> and is forbidden.

The override mechanism is **the language's own remapping**, not a bespoke argument on each
tactic:

- **`alias`** overrides a single name. Your theory proves set-equality as `setEq`?
  `theorem addZeroLeft = mytheory.zeroPlus` and `arithmetic` finds it. (This is exactly what
  the `aata/*.md` files do — aliasing the book's notation onto the std names.)
- **`model`** overrides a whole signature at once — the industrial-strength version of the
  same idea (see `model-design.md`). Aliasing remaps one name; a `model` remaps an entire
  structure's worth, so a structure that spells everything its own way can satisfy an
  accelerator's expectations wholesale.
- the **theory argument** (`arithmetic(peano)`) pins *which* vetted theory's names to use —
  itself a form of override.

**Prefer structural derivation when the entity is recoverable from a cited lemma's shape**,
and prefer **explicit citation** when the entity is a lemma the proof can name.
`extensionality` takes its extensionality lemma and per-operator unfold lemmas as EXPLICIT
args, and reads the element sort off the cited lemma's obligation binder — so there is no
expected name to override at all (the strongest form: zero coupling). A
hardcoded-but-overridable default is the acceptable fallback.

Two shapes this rule forbids, both of which `extensionality` is built to avoid: looking a
sort up by a LITERAL NAME (a rename then breaks the tactic), and ENUMERATING a theory scope
to find unfold lemmas by shape (a scope scan cannot survive the fetch-only demand engine,
and derives wrong names for irregular symbols — `identityFn` would want `identityFnApply`,
not `identityApply`).

## Inputs are named; guard obligations are searched for

**An accelerant NEVER searches for its logical inputs.** Whatever the inference consumes is
a named ref in the claim: `[using <tactic> <tactic_args>(…) input1 input2 …]`. The tactic
reads that list and nothing else — no scanning the proof for a premise of the right shape,
no scanning the scope for a usable lemma. (A tactic may resolve *well-known names* from
scope — `arithmetic`'s `addZeroRight` and friends — which is name resolution, not search,
and is governed by the naming-couplings rule above.)

**A GUARD OBLIGATION, by contrast, is searched for, and should be.** When an accelerant
restates a term that owes a side condition — a `requires` guard, or a refined-sort qualifier
at an argument — the obligation is hoisted onto the generated synthetic as a leading
antecedent (`wrapObligations`), and the citing site discharges it from what the proof knows
in scope (`withGuardPremises` → `dischargeGoal` → `refForKnown`, which consults the `known`
table of propositions established so far). That is correct: the proposition is fully
determined by the term plus its declaration, so the only question is whether it holds here,
and that is the same question whether the term was hand-written or restated by a tactic.
There is exactly ONE search primitive in the engine (`Elab.Known.lookup`) and every path
into it is a guard obligation.

A guard could not simply join the input list, because it is not an antecedent of the cited
fact. A step can owe several guards AND supply hypothesis refs, so one list could not
separate the two roles without a positional convention the reader would have to know.

**Consequence for admitted steps.** The search's hit is what records that the supplying step
was consumed. An admitted step builds no certificate and never computes its obligations, so
it contributes no such record — which is why the dead-step lint is gated on the file's TRUST
SET (`verify.trusted.count() == 0`), not on whether a particular step was admitted. The rule
is one sentence: **`--fast` does not dead-check.** The standing invariant it protects:
`--fast` never reports an error strict does not.

## What no word checks, in either mode's decision

A decision binds its vocabulary by well-known NAME — `add`, `mul`, `ZERO`, `succ`,
`less_than`, `nonneg`, the ext lemma, the associativity lemma — and never verifies the bound
symbol OBEYS the laws it assumes. Over a theory whose `add` is not associative, Presburger
can return `.valid`.

**Strict still rejects such a goal**, because its certificate must discharge against the
theory's DECLARED AXIOMS and a misbound operator has no axiom to license the rewrite. That
is the certificate earning its keep. But from inside `--fast` this is indistinguishable from
the benign "decided true, no certifier covers the shape" case — both are a true verdict with
no certificate — so **naming things strangely is how shenanigans escape the boundary**, and
only strict notices.

## Registered tactics

| word | module | default (kernel-checked) path | what `--fast` presumes |
|---|---|---|---|
| `tautology` | `Accelerants/Tautology.zig` (decision in `smt.zig`) | replay as kernel steps — an inline excluded middle plus `common_conclusion` per split atom, structural derivation at the leaves | nothing but the step budget: past the 16-atom cap the certificate is skipped and the verdict admitted |
| `arithmetic` | `Accelerants/Arithmetic.zig` (decision in `Accelerants/presburger.zig`, refutation search in `Accelerants/farkas.zig`) | the certifier chain below | the peano lemmas it would otherwise cite |
| `polynomial` | `Accelerants/Polynomial.zig` | distribute, right-nest and bubble-sort each monomial, sort the outer sum, fold identities — emitting rewrites that cite the theory's ring lemmas | the vocabulary's ring algebra, structurally |
| `extensionality` | `Accelerants/Extensionality.zig` | reduce to a pointwise residue, closed by `smt.tautology` inside `emitExtSetResidue` | packaging only — the decision still runs |
| `assoc_commut` | `Accelerants/Assoc.zig` | sort both sides to the same summand multiset, emit the rewrite chain | the operator is associative *and* commutative |
| `assoc` | `Accelerants/Assoc.zig` | right-nest both sides by the cited lemma (confluent + terminating, so right-nesting is canonical), emit the chain | the operator is associative. The lemma is still resolved, since it identifies the operator |
| `simplify` | `Accelerants/Simplify.zig` | normalize both sides by the cited rules to a shared form, emit the `EqCert` join | the cited rules hold — statements are read, proofs are not |
| `chain` | `Accelerants/Chain.zig` | BFS a rewrite path between the goal's two sides, emit it | as `simplify` |
| `specialize` | `Accelerants/Specialize.zig` | instantiate the head at the args, emit `cite_ref → apply_at → modus_ponens` | the head's statement (the claim is still α-matched) |
| `model` / `import` | engine words, not term builders | re-prove the source under the mapping / cite the imported fact | the α-match only |

### `arithmetic` — the fragment, and `fallback`

**Fragment**: terms over `ZERO`, `ONE`, `succ`, `add`, and `mul` where one side folds to a
literal; atoms `=`, `!=`, `less_than`; the propositional connectives; `forall`/`exists`.
Anything else — foreign predicates, nonlinear terms, quantified subformulas that are not
wholly arithmetic — becomes an **opaque propositional atom** in an SMT combination (DPLL
over the mixed skeleton, with Presburger as the theory solver). Opaque atoms are never
instantiated: a goal needing one's internals reports a countermodel naming it.

**`nonneg` is opt-in.** Declaring a well-known `nonneg(x)` predicate is a theory's request
to constrain its variables: the engine then reads `nonneg(x)` hypotheses as `x >= 0`, and
the elaborator injects one per bound variable. **Absent, the fragment is pure ℤ** — no
nonnegativity is assumed anywhere. This is what picks the ℕ-vs-ℤ reading of one goal.

**Decision**: Cooper's quantifier elimination, complete for Presburger arithmetic.
Divisibility atoms carry the periodicity, i128 arithmetic is overflow-checked, and
elimination blowup hits an explicit work budget — both limits are honest located errors,
never verdicts. A satisfiable negation reports countermodel values for the fixed variables
when a small witness exists.

**`fallback(<thm>)`** names a manually-proven theorem to cite when the chain declines a
valid goal — instead of the hard error (default) or the accelerated verdict (`--fast`). The
step stays **kernel-checked**, inheriting any accelerated names `<thm>` itself carries. It
is for goals Presburger *decides* but no certifier can *emit*, e.g. multi-fixed-variable
`∀∀∃`. Two accepted forms, so **every goal `arithmetic` can decide is fallback-supportable**:

1. **α-equal** — `<thm>`'s statement IS the goal; cite it directly.
2. **specialized instance** — `<thm> = ∀x⃗; A₁ -> … -> Aₘ -> C`, and `C` at some witnesses
   `x⃗` α-equals the goal. The matcher infers `x⃗` by first-order-matching `C` against the
   goal, discharges each antecedent `Aᵢ(x⃗)` from a supplied ref whose formula matches it
   (order-independent; the step's other refs are the decision premises), and emits a
   `cite_ref → apply_at(x⃗) → modus_ponens(refs)` chain the KERNEL re-checks — so a
   mis-inferred witness can never pass.
   (`tests/cases/tactics/arithmetic/arithmetic_fallback_specialize.b4m`.)

`fallback` is a contextual modifier on `arithmetic` only — elsewhere it is an ordinary
identifier. It is the decision-vs-certification escape hatch for a decision-backed
procedure, so the structural presumers (`assoc`/`assoc_commut`) will never carry one.

**The certifier chain**, in order, each link declining with a reason:

- **equation/order/exists** — linear equations normalize to succ-towers over sorted sums
  (recursion axioms plus `addZeroRight`/`addSuccRight`/`addIsAssociative`, with the residual
  permutation a chain of `addIsCommutative`/`addLeftSwap` rewrites); order goals synthesize
  the difference witness `d`, certify `add(a, succ(d)) = b`, and close with `lessThanIntro`;
  existentials search a constant witness tower. Cited `less_than`/`=` steps enter by witness
  substitution — each order premise is `lessThanElim`-unpacked and its flipped witness
  equation becomes a ground rewrite rule — so difference-logic chains including transitivity
  certify.
- **premise-combination** (`premiseCombinationCert`) — when an equation goal follows by
  CANCELLING an equality premise whose sides do not occur literally in the goal
  (`sub(a, r) = mul(b, q)` from `add(mul(b,q), r) = a`): prove the pure identity
  `add(P_l, G_l) = add(P_r, G_r)` by the ordinary join, rewrite `P_l→P_r` with the premise,
  and close with `addCancelLeft`. Needs
  `addIsCommutative`/`addLeftSwap`/`addCancelLeft` in scope.
- **mixed-skeleton** — tautology-style case splits whose boolean dead ends close by deriving
  the conflicting arithmetic literal from the branch's assumptions, then `ex_falso`.
- **Farkas** — combines SEVERAL hypotheses, which the single-atom order cert cannot: an
  infeasible cycle `x < … < x` (folded with `lessThanTransitive`), order composition,
  coefficient scaling (`mul`-by-literal bounds via `multiplicationPreservesOrder`), and sums
  of distinct-variable bounds (via `additionPreservesOrder` plus transitivity).
- **Cooper-replay** — the quantifier-alternation tail. A `forall x…; exists y; body` goal
  replays its Cooper elimination as kernel steps: for a period-1 trace, a boundary witness
  under `either_lhs`/`either_rhs`; for a period-D trace (the parity
  `forall x; exists y; x=2y ∨ x=2y+1`), a SYNTHESIZED induction on the fixed variable.
  Multi-variable and nested (`∀∃∀`) alternation decline, and fall to `--fast`.

### `polynomial` — honest limits

Identities only (`=`), not inequalities. Whole-number coefficients. **No cancellation** —
`x·a = x·b ⊢ a = b` is not an identity; that stays with `arithmetic`/`mulCancel`. A
subtraction- or division-like shape is out of fragment and gives a located error rather than
a false countermodel. **`succ` is kept opaque**, a deliberate non-privileging decision.

It is a **scalar-layer** tactic: it binds `add`/`mul`/`ZERO`/`succ` by well-known name, so
over a carrier whose operations are `addP`/`mulP` it reports "the goal has no add/mul
structure". Polynomial-ring identities are therefore written by hand — budget for stating
distributivity, identity, associativity and negation lemmas yourself.

## Deliberately out of scope

- **Nonlinear inequalities** (SOS / Positivstellensatz): incomplete, so it would be a
  *disclosed* accelerant rather than certificate-first. A real but separate, later decision.
- **Gröbner-basis equality entailment** — proving an equation *from* other nonlinear
  equations rather than as an identity. Medium effort, certificate-producing (the reduction
  chain), worth it once a concrete need appears.
- **Full nonlinear decision**: impossible. Nonlinear integer arithmetic is undecidable
  (Hilbert's 10th / MRDP), so the goal is useful incomplete fragments, disclosed honestly
  where they fall back.
