# MODEL-DESIGN.md — the `model` mechanism (structure reuse / "X is-a Y")

The canonical spec for the shipped `model` accelerant (referenced from GUIDE.md,
ACCELERATION.md, and the model source). Status: **implemented and in use** — the
group→ring→ℤ chain and the guarded-model machinery are live; see "Still open" for
the remaining design questions.

## What it is

A `model` declaration is a **named namespace of overloads** mapping an imported
abstract theory's primitives+axioms onto local symbols+facts. Once declared, the
theory's entire derived-theorem corpus is available at the target, remapped, cited
through the model. It names the local facts that play the group axioms — hence the
keyword `model` (the model-theoretic "Int satisfies the group axioms").

Motivating cases: **ℚ under `+` is a group** (guard-free) and **ℚ∖{0} under `×`
is a group** (guarded by `nonzero`) — two models of the *same* theory on the
*same* sort, which is what forces named instances. (ℤ additive-group +
multiplicative-*monoid* was the earlier driver; ℚ is sharper because both are
groups, exercising the two-models-of-one-theory collision.) The original
forcing function remains **nonneg-ℤ is-a Peano ℕ** (guarded), to retire the
hand-duplicated ℕ-algebra-over-ℤ in `std/integer-ring.b4m`.

## Design philosophy — `model` is comptime structural transfer (the Zig way)

This is the framing that makes `model` 2b4m's distinctive contribution, and it is
a **design constraint**, not just a description. Every open question is decided by
whether the answer keeps `model` comptime-shaped.

The *capability* — prove theorems over an abstract theory, transfer them to a
concrete structure by discharging axioms — is exactly what **Lean typeclasses**,
**Isabelle locales**, and **Rocq module functors / structures** already do. 2b4m is
NOT claiming to do something they cannot. The distinctiveness is in the SHAPE:

> **`model` is to typeclasses/locales what Zig `comptime` is to C++ templates +
> concepts.** Same expressive target; opposite implementation values.

- **Explicit over implicit — no resolution engine.** Lean *searches* for the
  instance; `model` is NAMED at the cite site (`[using model(AdditiveGroup)
  group.cancelLeft]`). Zig has no trait search; you pass/name the thing. The named
  cite IS the Zig answer to instance resolution: refuse action-at-a-distance.
- **Structural over nominal.** `Rat` does not *declare conformance* to `Grp`; you
  assert a mapping and the checker verifies the shape (obligations discharge),
  failing at the use site if not — `comptime` duck-typing lifted to proofs. No
  subtype hierarchy, no `instance` declaration the theory has to know about.
- **Monomorphize-and-forget over carry-the-dictionary.** `remapFormula` is
  comptime codegen: it emits the concrete theorem's AST from the abstract one and
  is DONE. No dictionary passing, no vtable, no residual machinery at
  proof-checking time. The big provers carry the typeclass dictionary; 2b4m
  specializes the formula once and moves on.
- **Tiny kernel, power beside it.** `model` is a disclosed, tainted, kernel-EXTERNAL
  rewrite (an accelerant, see Trust model). The kernel never learns what a
  "structure" is — same architectural bet as Zig's small-language + comptime, and
  as 2b4m's small-kernel + accelerants. It came out this shape because it inherits
  Zig's values, not despite being written in Zig.
- **LLM-authorable.** A model block is a flat mapping table a language model can
  write and read; typeclass instance resolution is implicit action-at-a-distance
  that is hard to author without a feedback loop. Legibility is 2b4m's whole reason
  to exist, and the comptime shape is what keeps `model` legible.

### The invariant (the non-goal that defines the feature)

**Stay comptime-shaped: explicit at the cite, structural not nominal, resolved-to-
concrete-and-done, no dictionary, no search.** Test any proposed extension by:
*would this be a comptime transform, or would it need a runtime/resolution
mechanism?* If the latter, it is not 2b4m's `model` anymore — it is a worse
reimplementation of the thing the big provers already do well.

Concretely, these would BREAK the distinctiveness and are therefore NON-GOALS:
- **Automatic model discovery** ("find the model that makes this goal go through").
  The cite must always name the instance.
- **Transitive model chains resolved by search** (`group models monoid`,
  `Rat models group`, ∴ `Rat` gets monoid theorems automatically). If chaining is
  ever wanted, it must be an explicit, spelled-out composition — not search.
- **Coherence machinery** — two search paths to the same theorem needing to be
  reconciled. There are no search paths; there is one named cite.

## Syntax

### Declaration

A `model` is just a **named namespace of overloads** — a bag of `source: target`
mappings — and nothing more. There is no header, no `= carrier`, no `where` on the
declaration: only the name and the mappings.

```
model <InstanceName> {
  <source.entity>: <localTarget>       // a mapping (overload): source → local
  ...
  <source.axiom>:  <localFact>         // an axiom obligation, discharged by naming
  ...                                  //   a local fact of the (remapped) shape
}
```

- **`source: target` direction** (`group.Grp: Rat`, `group.op: add`). Left is the
  *source* entity, right is the local thing it maps to. This mirrors how
  `remapFormula` reads the table (walk source formula, look up each symbol → its
  target) AND makes the completeness check trivial: enumerate the source theory's
  primitives+axioms, verify every one appears as a key exactly once. A missing
  key is a clear error ("model `AdditiveGroup` doesn't map `group.opInverseLeft`").
- **Uniform lines.** Every line is `source: local`. There is nothing special about
  any one mapping — a sort-mapping (`group.Grp: Rat`) is just another overload in
  the bag, NOT a privileged "carrier header". Symbol mappings remap symbols; axiom
  lines map an obligation to a local FACT (not a proof block) — you *name* a local
  axiom/theorem whose formula already has the remapped shape. No
  `theorem … proof … qed` inside the block.
- **Named, header-free.** The declaration is just `model NAME {`. The name is
  mandatory: two models over the same source coexist (`AdditiveGroup`,
  `MultiplicativeGroup`), disambiguated at the cite by name. No `= …`, no `as`.
- **Guarding is inferred, not declared.** When a source sort is mapped onto a
  *predicated* (refined) target sort, the model is relativized by that sort's
  qualifier — every source binder over that sort picks up a `guard(bound) ->`
  antecedent (see Relativization). It rides on a MAPPING (a predicated target),
  not on a header.

Example:
```
model AdditiveGroup {
  group.Grp:      Rat
  group.E:        ZERO
  group.op:       add
  group.inverse:  neg
  group.opAssoc:  addIsAssociative   // + the other 4 axiom obligations
}
```

Guarded (the guard is inferred from the predicated target `NonzeroRat`):
```
sort NonzeroRat = Rat where nonzero
model MultiplicativeGroup {
  group.Grp:      NonzeroRat          // predicated target → relativized by `nonzero`
  group.E:        ONE
  group.op:       mul
  group.inverse:  inv
  group.opAssoc:  <a local fact, already guarded by nonzero>
}
```

### Citation (using a transferred theorem)

```
theorem addCancelLeft: forall a, x, y: Rat; add(a, x) = add(a, y) -> x = y
proof
  @conclusion |
    forall a, x, y: Rat; add(a, x) = add(a, y) -> x = y
    [using model(<InstanceName>) <source.theorem>]
qed
```

`model` is a **built-in justification-verb** (like `axiom`, `rewrite`) — NOT a
user-defined tactic (2b4m has none). `[using model(AdditiveGroup) group.cancelLeft]`
remaps `group.cancelLeft`'s formula through the `AdditiveGroup` mapping and checks
it equals the step goal. The cite names BOTH the instance (which mapping) and the
source theorem (what to transfer) — necessary because a sort has multiple models.

Spelling follows 2b4m's parameterized-tactic convention: the **instance is
parenthesized** (the mode selector, exactly like `assoc(opAssoc)`,
`polynomial(theory)`, `forall_elim(t) step`) and the **source theorem is a bare
ref** (the fact operated on). No `with` particle — the `by` grammar has none
anywhere; parens carry the configuration/operand distinction. The model name alone
resolves which namespace of overloads to apply — there is nothing else to name.

## The engine: `remapFormula`

The one genuinely new piece. `formula: TermId` PERSISTS on every checked `Fact`
(env.zig:44-70) — the statement AST survives after proof-checking (only the proof
is consumed). So every source theorem is a live `TermId` to walk; no re-parse, no
re-elaborate.

`remapFormula(formula: TermId, mapping, guard: ?pred) -> TermId`: a structural
walk over `term.zig`'s Node union emitting a new tree into the arena with

- **`SortId` substituted** (Grp→Rat) — including the `sort` field inside `fvar`
  and `quant` nodes, not just top-level;
- **`SymId` substituted** (op→add, E→ZERO, inverse→neg) in `app`/`pred` nodes;
- **guard injection** (guarded case): each `quant` over the mapped sort
  gets its body wrapped `guard(bound) -> body`.

This is ONE pass, run in BOTH directions:
- **IN** (obligation check): remap each source axiom, check it equals the named
  local fact's formula. `remapFormula(group.opAssoc, m) == addIsAssociative.formula`.
- **OUT** (theorem transfer): remap the cited source theorem, check it equals the
  cite goal.

Closest existing precedent is `instantiateSchema`'s symbol substitution, but that
substitutes term/predicate PARAMS, not sorts+arbitrary-syms across a whole
formula. No such helper exists yet — this is the build.

Note: `group`'s primitives are all opaque `func`/`const` (no `define`), so the
`definition: ?TermId` transparency path doesn't arise for this theory. Guard
against mapping onto a `define`d symbol later.

## Trust model — `model` is an ACCELERANT

Classified with `assoc`/`arithmetic`/Cooper-replay. (Vocabulary per
`accelerated-elaborated-vocab`: kernel-checked vs. accelerated/disclosed; flag is
`--fast` vs. default. There is NO `--pure`.)

- `[using model(…) …]` **taints** the citing theorem — `accelerated` gains
  `"model"` — **disclosed in the summary**.
- **`--fast`**: trust the transfer wholesale — remap only the source theorem's
  STATEMENT, α-match the goal, taint `accelerated: model`. Assume-true; check
  nothing about the proof. (MVP path — built.)
- **default (strict)**: **materialize the source proof, remapped, and let the
  kernel check it.** Not tainted — genuinely kernel-checked. See below.

### Strict mode = materialize the remapped proof tree (the real mechanism)

A `model` transfer is *strictly a lexical (AST) remapping* — including the PROOF
AST, not just the statement. So strict mode does exactly this:

1. `[using model(MyModel) sometheorem]` loads `MyModel`'s remap list and rewrites
   `sometheorem`'s ENTIRE PROOF through it, emitting a synthetic local theorem
   `MyModel$sometheorem` (name-mangled to avoid collision).
2. That remapped proof cites other things — `someothertheorem`, axioms. **Walk the
   dependencies**: each cited source theorem is recursively materialized the same
   way (`MyModel$someothertheorem`), and the citation is rewritten to the mangled
   name. Memoized per (model, source-theorem) so a diamond emits once.
3. Citations obey the CITATION RULE (below) — no cited fact silently changes
   meaning under the interpretation.
4. The **kernel checks the whole materialized tree** like any other proof. That
   checking IS the obligation discharge — automatic and exact. No taint, no
   `deps` provenance channel, no meta-argument.

#### The citation rule (soundness of materialization)

A materialized proof's every citation is repointed per this rule — the invariant
is *a materialized proof never cites a fact whose meaning the substitution shifts
without the model accounting for it* (which would be "using something unknowingly"
— the synthesized citation nobody authored). For each cited statement:

- **In the model's mapping** → cite the mapped target, KIND-MATCHED: an obligation
  discharged by a local *theorem* becomes a `theorem_ref`, by a local *axiom* an
  `axiom_ref`. (An abstract axiom mapped to a proven theorem is the common case —
  `divisibility.mulOneRight` → ℤ's `mulOneRight` theorem.)
- **Not mapped, and NOT affected by the substitution** (its statement mentions no
  substituted sort/sym) → cite AS-IS, walk ends. The remap is the identity on it,
  so it is a genuine shared fact — an untouched theorem or axiom both sides have.
- **Not mapped, affected, a THEOREM** → recursively materialize it (`Model$thm`).
- **Not mapped, affected, an AXIOM** → **FORBIDDEN.** Its meaning shifts under the
  interpretation and nothing discharges it → error, naming the axiom. The author
  must map it (to a theorem that proves it, or to a foundational axiom that IS it).

The "affected by the substitution" test is `Remap.affects` (term.zig): does the
formula mention any sort/sym the remap substitutes. This is what lets a genuine
shared fact (unaffected) be cited freely while a shifted-but-unmapped one is
caught. It is why discharging obligations is uniform (axiom-or-theorem, both are
facts) yet a synthesized proof can never lean on an axiom *unknowingly*.

Why this is right: the obligation set is NOT the source theory's declared axioms
(that universe is unbounded and cross-file — a group-powers proof may lean on an
`arithmetic` axiom three files away). It is *whatever the proof actually cited*.
Materializing the remapped proof makes the kernel enforce every such leaf
precisely: remap `add` to something where `1+1=2` is false, and the mangled step
citing the remapped arithmetic axiom simply won't check — caught for free, no
special dependency analysis.

Mangled theorems are emitted as real `Statement`s (so the kernel checks them and
citations resolve) but SUPPRESSED from the user-facing declaration/theorem count
(they are machinery, not authored). Memo keyed on the MODEL, so all cites through
one model share the materialized copies.

Subtlety vs. other accelerants: strict `model` is not a decision procedure and not
a bare trusted verdict — it is **proof materialization**: the source proof,
lexically remapped, kernel-checked locally. `--fast` skips the materialization and
trusts; strict does it and checks.

### Partial models are LEGAL — at the prover's risk (THE WARNING)

A model **need not map every source axiom.** A partial mapping is allowed; it is
an interpretation with an undischarged obligation. This is decided (was the
"completeness policy" open question): allow partial, and let the MODE enforce the
consequence.

The two modes make the risk asymmetric — and this asymmetry IS the feature:

- **`--fast`**: the transfer is trusted wholesale and NEVER inspects which source
  axioms the transferred theorem's proof depended on. So if you `[using model(M) …]`
  a theorem whose `group`-proof used `opInverseLeft`, and `M` never mapped
  `opInverseLeft`, **it PASSES.** The gap is invisible to `--fast` by construction
  (it checks nothing). Disclosed only as accelerated-by-`model` in the summary.
- **default (strict)**: elaboration checks that every source axiom the transferred
  theorem *depends on* is discharged by the model. It reaches the unmapped
  `opInverseLeft`, finds no discharging fact, and **REJECTS**, naming the missing
  obligation. The gap cannot hide.

> **THE WARNING.** A `--fast` green build over a partial model is a loaded gun the
> summary warns about; the SAME model may FAIL default/strict mode. If you lean on
> a transferred theorem that needs an axiom you didn't map, `--fast` lets it
> through and strict mode catches it. Treat a `--fast` pass with any partial model
> as provisional until it also passes strict.

Consequence for implementation: the per-axiom **dependency check lives only on the
default/strict path** (it must know which source axioms a source theorem's proof
cites, to reject precisely). `--fast` needs no dependency analysis at all —
"remap + taint" — which is also why `--fast` partial transfer is the natural MVP
and strict discharge is the follow-up. (An unmapped obligation is morally a
structure-level `hole`; whether it's tracked via the `holes` machinery or a
distinct "unmapped-axiom" marker is an implementation choice — either way it is
tracked+disclosed, never silent.)

### Partial models as a reverse-mathematics probe (a *feature*, not just a risk)

Because strict mode rejects precisely the transferred theorems whose proofs
*depend on* an unmapped axiom, a partial model is an **axiom-dependency probe**:
implement a full model, then **comment out one obligation line and re-run strict
mode** — the checker names exactly the transferred theorems that break, i.e. the
ones that genuinely used that axiom. This is reverse mathematics ("which axioms
are *necessary* for this theorem?") turned into comment-and-recheck:

- "Does `cancelLeft` actually need inverses, or only associativity + identity?"
  Unmap `group.opInverseLeft`, check strict: if `cancelLeft` still passes, its
  proof never touched inverses.
- Bisect the axiom set — unmap obligations one at a time — to reconstruct the
  corpus's dependency lattice empirically, no hand proof-tracing.

Sound as a probe precisely because strict rejection means the proof genuinely
cited the missing axiom (no false positives from the checker's side). This is why
partial models earn their place on principle, not just convenience.

### Long-range: the "wrap kernel steps into a named theorem" primitive (4 uses)

`model` strict materialization needs to WRAP synthesized/remapped kernel steps
into a named, checked environment theorem, then cite it (the cite path already
exists — it's `fallback`'s `theorem_ref`). That wrap primitive turns out to be
shared machinery with FOUR uses, which is why it's worth building well once:

1. **`fallback`** — CONSUME a named theorem as an accelerant's certificate (exists).
2. **`model` strict** — PRODUCE named theorems by remapping a source proof (this).
3. **accelerant debug mode** — wrap ANY certifier's steps into a reviewable named
   theorem (next; in proximal-todo). Today accelerant reasoning is opaque
   (`--fast` shows a taint; elaborated mode's inline steps vanish); reifying it as
   named theorems is the transparency lever for 2b4m's LLM-authored thesis.
4. **mechanical export (Lean/Isabelle/Rocq)** — an accelerant's *verdict* doesn't
   translate (an external prover won't accept "the Presburger procedure decided
   it"), but the materialized full KERNEL-STEP CHAIN does — it maps onto
   external tactic invocations. So the same wrap/materialize output is what export
   replays. The `model` step-remapping (retain lowered proof → remap step formulas
   + justification ids) is export-shaped by construction.

### Long-range: synthetic-theorem emission as a general accelerant debug mode

`model`'s strict materialization mints name-mangled environment-level theorems
(`MyModel$sometheorem`) — a mechanism NO other accelerant currently has (the
others splice anonymous inline steps, or in `--fast` show nothing). `model` needs
it because its output is a fixed, reusable artifact (materialize-once, cite-many),
unlike a per-goal certificate.

But it points at a general capability worth pursuing later (user, 2026-08-02):
**a debug/review mode in which ANY accelerant emits its full synthesized
derivation as named environment theorems for careful review.** Today an
accelerant's reasoning is opaque — `--fast` shows only a taint, and elaborated
mode's inline certificate steps vanish into the proof; you cannot point at "the
chain `arithmetic`/`ext` generated for this goal" and read it as standalone
objects. Reifying accelerant output as inspectable theorems is the transparency
lever for exactly the black-box spots — valuable for 2b4m's LLM-authored,
trust-legible thesis. `model`'s strict path is the prototype; generalizing it to
the other accelerants as an opt-in debug mode is the long-range direction.

## Relativization (the guarded case)

A guarded model (its sort-mapping targets `Rat where nonzero`) makes `remapFormula`
inject `guardPred(bound) ->` at every quantifier over the mapped sort — applied
UNIFORMLY in both directions:

- **OUT**: `group.cancelLeft`'s `forall a,x,y: Grp; op(a,x)=op(a,y) -> x=y` →
  `forall a,x,y: Rat; nonzero(a) -> nonzero(x) -> nonzero(y) -> mul(a,x)=mul(a,y) -> x=y`.
- **IN**: the author's discharging fact must ALREADY carry the `nonzero` guards
  (decision (A): the guard lives in the local fact, not synthesized/stripped by the
  checker). The predicated target sort (`Rat where nonzero`) is what tells
  `remapFormula` to inject; the same pass keeps IN and OUT symmetric.

## MVP staging (accelerant pattern, as with Cooper-replay/assoc)

1. **`--fast` transfer first** — parse `model` block, build the id→id mapping,
   `remapFormula` the cited source theorem (unguarded case), check it matches the
   goal, taint. NO dependency analysis, NO obligation check — a partial model
   transfers just fine here (that's the whole point / the WARNING). This alone
   proves the mechanism (sort-map + theorem-remap). Test: `Rat`/`Int` gets
   `cancelLeft`/`inverseUnique`/etc. under `--fast`.
2. **default-mode obligation discharge** — the strict path: for a transferred
   theorem, check every source axiom its proof DEPENDS ON is discharged by a mapped
   local fact (remap-and-match); reject naming any unmapped/mismatched obligation.
   Needs source-theorem→axiom dependency info. Then sound transfers are un-tainted.
3. **guarded models** — relativization pass; `where nonzero`; ℚ∖{0} mult-group and
   nonneg-ℤ-is-a-ℕ.

## Applications (std reuse candidates)

- **Abstract divisibility — DONE.** `std/divisibility.b4m`; `std/integer/divides.b4m`
  models it. First real in-library `model` on duplicated std code.
- **Group / set corpora moved to importable std — DONE.** `std/group.b4m` (10
  theorems + opt-in `opCommutative`), `std/set.b4m` (19 identities). Each aata
  transcription aliases back. This is what makes them modelable (locally, on
  demand, by any consumer).
- **`std/ring.b4m` models group additively — DONE.** The first TWO-LEVEL model
  (a `model` inside a modelable theory). Judson's first ring proposition
  (a·0=0·a=0; a(-b)=(-a)b=-(ab); (-a)(-b)=ab) proved by transferring the
  additive-group cancelRight/inverseUnique/invInvolution through the AdditiveGroup
  model.

- **ℤ thin model over ring — NEXT (the payoff / three-level chain).** Make
  `std/integer-ring.b4m` (or a new consumer) declare a `model IntegerRing { … }`
  over `std/ring.b4m` (its ring-sort mapping targeting `Int`), so ℤ inherits the
  ring corpus instead of hand-deriving it, and
  the ℤ→ring→group THREE-level materialization is exercised. Discharge audit: ℤ
  already has 7 of the 9 ring axioms as facts (addIsAssociative, addZeroLeft,
  addZeroRight axiom, addNegRight, addIsCommutative, mulIsAssociative,
  mulAddDistribLeft). **Missing 2-3 discharge lemmas ℤ must first prove:**
  `addNegLeft` (add(neg(n),n)=ZERO, from addNegRight + addIsCommutative);
  `mulDistributesRightOverAdd` (from a NEW `mulIsCommutative` + mulAddDistribLeft,
  or by direct induction). Then the model transfers negMulNeg/mulNegLeft/etc.
  Note: prefer ADDITIVE retrofit (add the model + transfers) over DELETING
  integer-ring's hand-proofs — downstream files cite negNeg/negAdd by name; a
  rename/removal ripples. The group-corpus-in-std prerequisite is already met.

## Still open (not yet decided)

- Do transferred theorems ALSO materialize as citable namespaced facts
  (`AdditiveGroup.cancelLeft`) at declaration time, or ONLY reachable via the
  `[using model(…) …]` cite? (Namespace-shadowing was raised then set aside; the
  cite-verb form is what's settled. Materializing would let other tactics see them.)
- Predicated-sort guards that aren't a single unary pred (e.g. a conjunction) —
  the guard is inferred from the mapped target sort's qualifier, so this needs a
  `sort … where <compound>` (a `define`d/`pred`-combined predicate today).
- Multi-sort source theories (a theory reasoning over two sorts) — mapping scales,
  but not exercised by group/monoid.
```
