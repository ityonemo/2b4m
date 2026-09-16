# bpa language guide

This guide covers the whole surface: every keyword, the proof rules, how
the kernel establishes trust, and the built-in automation. For naming and
style conventions see `CONVENTIONS.md`; for the accelerated-tactic registry see
`ACCELERATION.md`.

## Index (how to extract one rule/tactic/keyword)

This file is greppable by anchor. Every proof rule, accelerant, and declaration
keyword has a **leaf section** headed `### RULE: <name>`, `### TACTIC: <name>`, or
`### KEYWORD: <name>`. Each leaf is flat (it contains **no** sub-heading), so you
can print exactly one topic — from its anchor up to the next heading of any level —
with awk:

```
awk '/^#+ /{p=0} /^### RULE: or_elim$/{p=1} p' GUIDE.md
```

`/^#+ /` matches any markdown heading; `p` turns on at the anchor and off at the
next heading, printing just that section. Swap the anchor to look up any entry
below. The overview tables (`### Justification rules (overview table)`,
`## Query commands`) are *not* leaves — they are at-a-glance indexes.

| Anchor | Topic |
|---|---|
| `KEYWORD: sort` | declare a sort / predicated (subset) sorts |
| `KEYWORD: const` | uninterpreted constant of a sort |
| `KEYWORD: define` | name a term (transparent expansion) |
| `KEYWORD: func` | function symbol; `requires` guards |
| `KEYWORD: pred` | predicate (function into `Prop`) |
| `KEYWORD: axiom` | assert a formula without proof |
| `KEYWORD: theorem` | assert a formula with a checked `proof … qed` |
| `KEYWORD: hole` | aspirational placeholder (the "sorry"); `--draft` |
| `KEYWORD: schematic` | parameterized `axiom`/`theorem` (schemas) |
| `KEYWORD: intheory` | forward-declare a theorem (verified TOC) |
| `KEYWORD: import` | load another file under a namespace |
| `KEYWORD: alias` | local kind-checked view of an imported entity |
| `KEYWORD: model` | declare a local structure models an abstract theory |
| `RULE: axiom` | cite an axiom verbatim |
| `RULE: theorem` | cite a proven theorem verbatim |
| `RULE: hypothesis` | restate an enclosing block's assumption/witness |
| `RULE: predicate` | surface a predicated `fix h: H` binder's guard |
| `RULE: modus_ponens` | from `P -> Q` and `P`, conclude `Q` |
| `RULE: implies_intro` | discharge an `assume` block as an implication |
| `RULE: forall_intro` | discharge a `fix` block as a universal |
| `RULE: forall_elim` | specialize a universal at one or more terms |
| `RULE: exists_intro` | from `P[t]`, conclude `exists x; P[x]` |
| `RULE: exists_elim` | export an `unpack` block's witness-free conclusion |
| `RULE: and_intro` | conjunction from both conjuncts (rejects iff shape) |
| `RULE: and_elim_left` / `and_elim_right` | project a conjunction |
| `RULE: iff_intro` | a biconditional from its two directions |
| `RULE: iff_elim_forward` / `iff_elim_backward` | recover a direction of an iff |
| `RULE: or_intro_left` / `or_intro_right` | inject into a disjunction |
| `RULE: or_elim` | binary case analysis over a disjunction |
| `RULE: not_intro` | derive a negation from a contradiction |
| `RULE: absurd` | from a contradiction, conclude anything |
| `RULE: double_negation` | from `not not P`, conclude `P` |
| `RULE: reflexivity` | `t = t` |
| `RULE: symmetry` | from `x = y`, conclude `y = x` |
| `RULE: rewrite` | replace an equation's LHS by its RHS in a target |
| `RULE: iff_rewrite` | replace `P` by `Q` given `P iff Q` in a target |
| `TACTIC: instantiation` | monomorphize a schema (`using`) |
| `RULE: specialize` | apply a forall-theorem at args + discharge antecedents, in one step |
| `RULE: chain` | prove A = Z from equations used any direction + congruence |
| `RULE: model` | transfer a theory's theorem through a named model |
| `TACTIC: simplify` | equational rewriting to a common normal form (documents `simplify_quantified` inline) |
| `TACTIC: assoc_commut` | associative-commutative reordering of a sum |
| `TACTIC: assoc` | associativity-only reordering (non-commutative) |
| `TACTIC: polynomial` | nonlinear `add`/`mul` polynomial identities |
| `TACTIC: extensionality` | extensionality-reduction (sets/functions) |
| `TACTIC: tautology` | propositional consequence |
| `TACTIC: arithmetic` | linear arithmetic over Nat |

(The `_quantified` variant of a tactic — `simplify_quantified`, `assoc_commut_quantified`,
`assoc_quantified`, `polynomial_quantified`, `extensionality_quantified` — is documented inside its
base tactic's leaf; it peels a leading `forall` prefix without a hand `fix`.)

## Files and checking

A `.bpa` file is a sequence of declarations. `bpa check file.bpa` verifies
them in order; every failure is reported as `file:line:col: error:
<message>` on stderr, and success prints one summary line:

```
OK: 18 declarations, 6 theorems proven
```

**One theorem.** `bpa check <file> <theorem>` proves only that theorem and
whatever it cites — the file's other proofs never run. That is the iteration
loop for a long file (pair it with `--fast`). A name that is not there is
`reference not found`; a SCHEMA is reported as checked at its instantiations
(it has no proof of its own to run); an axiom is a legitimate target — its
statement is elaborated, and the run says `0 theorems proven`.

**A directory.** `bpa check <dir>` checks every `.bpa` and `.md` under it,
recursively, in ONE engine pass — so a fact two files cite is proved once, not
once per file — and prints one aggregate line:

```
OK: 47 files, 1862 declarations, 468 theorems proven
```

A `.md` with no ```` ```bpa ```` block parses to nothing and costs nothing. A
theorem argument selects within one file, so it cannot be combined with a
directory.

**What a proof rests on.** `--axioms` reports the axioms the checked
theorem(s) transitively bottom out in, with the site each was declared at. It
follows the demand graph, not the surface syntax, so it sees through accelerant
certificates, `instantiation`, model transfers and imports — things `query
uses` cannot:

```
$ bpa check examples/gauss.bpa gaussSum --axioms
OK: 72 declarations, 1 theorems proven
  — rests on 7 axiom(s):
      sumToZero  (examples/gauss.bpa:44)
      sumToSucc  (examples/gauss.bpa:45)
      addZeroLeft  (std/peano.bpa:39)
      …
      induction  (std/peano.bpa:81)
```

(`bpa query uses` shows `gaussSum` citing five facts by name; the other two —
`addSuccLeft`, `mulSuccLeft` — arrive only inside the certificates its
`arithmetic` steps generate, which is exactly the gap a syntactic scan leaves.)

A `hole` is an axiom as far as the kernel is concerned, so it is listed too and
marked `— HOLE`. Default mode rejects a hole-bearing run before the report, so a
marked hole appears only under `--draft`.

**A library owes its own examples.** `--library` (a directory) additionally
FAILS on any axiom declared in that directory that no theorem in it rests on.
An axiom no derivation ever touches is one whose binders, guards and direction
have never been checked, so `std/` carries a `<namespace>/examples.bpa` per
theory demonstrating exactly those axioms nothing else exercises. A fact a
`model` names as a discharger (`src <- local`, a `@`-projection, a guard
witness) counts as used — that is consumption by the model machinery rather
than by a citation.

**When a run does something you cannot explain from the source**, `--trace-facts` reports
which fact each citation actually resolved to, and in which namespace — the question a name
alone cannot answer once model transfers have published second copies of a theory's theorems.
See `agents/debug-guide.md` for that flag and the other diagnostics.

By default `bpa check` **verifies everything**: `by arithmetic`/`by
tautology` must produce a checkable certificate (an accelerated fallback is a hard
error), and every `using` step (accelerant / model / import) is verified.
`--fast` defers that verification per `using` WORD during development and says
so loudly in the summary — a trusted word's step is *admitted* (accepted by
its own cheap check / statement match) rather than kernel-checked:
- `--fast` — trust ALL `using` words
- `--fast-only W…` — trust ONLY the listed words (allowlist)
- `--fast-except W…` — trust all words EXCEPT the listed (denylist)
  Words are accelerant tactics (`arithmetic`, `tautology`, `polynomial`,
  `simplify`, … + their `_quantified` variants) and the engine words `model` /
  `import` (group word `engine`). `instantiation` is never trustable.
- `--draft` — allow `hole`s (aspirational placeholders); orthogonal to the
  above. Default mode rejects any file with holes and lists them.

Re-run plain `bpa check` to fully verify before finalizing. `bpa fmt`
normalizes whitespace and indentation (`--check` reports instead of
rewriting).

## Declaration keywords

### KEYWORD: sort

Declares a sort (a domain of discourse). `Prop`, the sort of propositions,
is currently the only built-in. Sorts are typically capitalized; the
following declares "Natural Numbers":

```bpa
sort Nat
```

**Predicated sorts (`sort H = G where inH`).**
A **predicated sort** names `G` restricted to the elements satisfying a unary
predicate `inH` — the natural way to write a subset (a subgroup, the
nonnegatives, …). It introduces no new kernel sort: `H` *is* `G`, and every use of
`H` desugars to `G` with the guard `inH` injected — as a hypothesis, an obligation,
or a postcondition, depending on position. Pure sugar; everything stays
kernel-checked.

```bpa
pred inH(g: G)
sort H = G where inH          // H is "G where inH holds"
sort HK = G where inH and inK // several qualifiers: the guard is their CONJUNCTION
```

Chained `and` qualifiers (or a refined sort refining another refined sort) accumulate
into one CONJOINED guard `(inH(x) and inK(x)) ->` — the canonical shape the kernel's
guarded `forall_intro` derives, so statements, `fix` blocks, and model transfers all agree.

The guard appears at each position `H` is used:

- **Quantifier binders** — `forall h: H; P` means `forall h: G; inH(h) -> P`;
  `exists h: H; P` means `exists h: G; inH(h) and P` (an existential over `H`
  *asserts* membership).
- **`fix h: H`** — the fix block carries `inH(h)` as its guard: surface it with
  `[by predicate <fix-label>]`, and `forall_intro` concludes the relativized
  `forall h; inH(h) -> …`. `unpack h: H` needs nothing special — the existential
  it opens already carries `inH(h)` as a conjunct (project it with `and_elim_left`).
- **Function arguments** — `func f(x: H): R` makes every call owe `inH(t)` for the
  actual argument `t` (an undischarged obligation is an error), like a `requires`.
- **Function results** — `func op(a: H, b: H): H` asserts `op` is *closed* on `H`
  (an uninterpreted function's signature is an assertion, on par with an axiom):
  each application `op(x, y)` makes `inH(op(x, y))` available, so a downstream
  `f(op(x, y))` composes for free — the subgroup-closure pattern.
- **Constants** — `const E: H` asserts `E ∈ H` (the nullary case of a function
  result): a reference to `E` makes `inH(E)` available, so `f(E)` composes.

An **anonymous** predicated sort may be written inline anywhere a sort appears,
without a named `sort` declaration:

```bpa
func f(x: G where inH): R              // inline-refined argument
theorem t: forall h: G where inH; P(h) // inline-refined binder
```

The `where` clause is a bare predicate name (applied to the bound variable); for a
conjunction of conditions, `define` a predicate for it and refine by that name.

### KEYWORD: const

Declares an uninterpreted constant of a sort.

```bpa
const ZERO: Nat
```

### KEYWORD: define

Names a term or a proposition.  Expansion is performed transparently at
elaboration — the kernel only ever sees the underlying term, so definitions add
nothing to the trusted surface and work everywhere a term does, including inside
automation. Definitions may build on each other. The sort is inferred.

```bpa
define TWO = succ(succ(ZERO))
define FOUR = succ(succ(TWO))
```

A define may take PARAMETERS, making it a macro function or predicate. **Parameters
take no sort** — a define is not a declaration, it is an expansion: the arguments
arrive already elaborated at each use, and the body's own elaboration types every
use of them. A declared param sort would be a second source of the same fact, able
only to agree (noise) or to disagree (a spurious error). Writing one is an error.

```bpa
define divides(d, n) = exists k: Int; n = mul(d, k)   // parameters are bare names
define even(n) = divides(TWO, n)                      // defines build on defines
```

A define is a MACRO, not a declaration: it is substituted wherever it appears, before
anything else looks at the text (imports resolved, body substituted, repeated until
nothing changes). So a define can stand anywhere an expression can — including as a
`where` guard (`sort Big = Nat where isBig`, `forall x: Nat where isBig; …`) and as a
model mapping's target (`model M { src.UNIT: DOUBLED }`) — and can be re-exported by an
alias (`pred does_divide = int_divides.divides`). It has no identity of its own, so it
cannot be *named* where a symbol is required (a model mapping's SOURCE, a citation).

A define that merely FORWARDS an opaque symbol in the same argument order —
`define lt(a, b) = ordering.less_than(a, b)` — is an ALIAS written as a macro, and
is rejected (`--draft` allows it). Write the alias form `pred lt = ordering.less_than`
instead: an alias binds the name to the target's identity, so it keeps its KIND and
downstream files can alias it in turn. A PERMUTED forward (`define gt(a, b) =
ordering.less_than(b, a)`) is a genuine macro and is fine.

### KEYWORD: func

Declares a function symbol with argument and result sorts. An optional
`requires` clause guards the function: every application incurs a proof
obligation that the guard holds, discharged against facts available at the
use site (an undischarged obligation is an error).

```bpa
func succ(n: Nat): Nat
func div(a: Nat, b: Nat): Nat requires b != ZERO
```

### KEYWORD: pred

Declares a predicate (a function into `Prop`). Zero-argument predicates
are atomic propositions and may be written bare.

```bpa
pred less_than(a: Nat, b: Nat)
pred raining
```

### KEYWORD: axiom

Asserts a formula without proof. Axioms are the file's assumptions; a proof cites
one with `[by cite NAME]`, and `bpa query uses` lists every fact a proof cites.

```bpa
axiom addZeroLeft: forall b: Nat; add(ZERO, b) = b
```

### KEYWORD: theorem

Asserts a formula with a `proof ... qed` block, which the kernel checks.

```bpa
theorem addZeroRight: forall n: Nat; add(n, ZERO) = n
proof
  ...
qed
```

### KEYWORD: hole

An **aspirational placeholder** — a claim stated up front, accepted mechanically
like an `axiom`, but tracked as a hole. Use it to **scaffold** (state a lemma,
build the proof that needs it, fill it in later) or to **reason conditionally**
("suppose an odd perfect number exists; here is what follows"). Cited exactly
like an axiom: `[by cite myHole]`.

```bpa
hole zeroIsEven: even(ZERO)
```

Holes are **disclosed, never silent**: a theorem that (transitively) rests on a
hole is tracked, and **default mode REJECTS the file** — it exits nonzero and
lists each hole with its `file:line` and the theorems that depend on it, so a
hole-bearing result is never mistaken for complete. `--draft` allows holes
(exit 0) with a loud banner naming them. Holes are **orthogonal** to the speed
flags: `--fast` never accepts a hole; only `--draft` does. Once you prove a
hole, turn it into a `theorem`.

### KEYWORD: schematic

Schematic axioms and theorems.
A parenthesized parameter list makes an `axiom` or `theorem` **schematic**:
a stored form with `comptime` semantics. Each `instantiate` use substitutes
concrete, written-out arguments and (for theorem schemas) re-checks the proof at
that instance. Formula-valued parameters are supplied as `fun` lambdas.

```bpa
axiom induction(prop: Nat -> Prop):
  prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)

theorem contrapositive(p: Prop, q: Prop): (p -> q) -> (not q) -> (not p)
proof
  ...
qed
```

**Schema well-formedness (the per-instance gate).**
A theorem schema's proof body is verified **once per instantiation site**: at
each `[using instantiation NAME(args) …]`, the body is elaborated at the real
arguments and kernel-checked. That per-instance proof is the *only* soundness
gate, and it always runs — `instantiation` is never `--fast`-trustable (admitting
it shape-only would skip exactly this proof; see #93).

A schema need **not** be a true universal. A narrow schema whose body only holds
for some arguments is bad form, not an error — it simply declares fine and fails
at the first instantiation whose arguments make the body unprovable (the prover
catches you there). There is no declaration-time check: an *uninstantiated*
schema is never verified (nothing demands its body).

The rule of thumb: **a schema is checked where it is used**, like a macro whose
expansion must prove out at each call. If you want a schema treated like a
theorem (proved standalone), instantiate it — or wrap it in a named theorem.

Instantiations are **not cached**: a plain theorem is checked once and cited
by reference thereafter, but a schema's proof is re-run at every instantiation
site (the parameters differ, so there is no single fixed result to cache). If
an expensive instance is reused, **realize it into a named theorem** — write a
plain `theorem` whose one step is `[using instantiation NAME(args) ...]`, and cite
that theorem from then on. Naming pays the instantiation cost once and reuses
it through the ordinary `proven`-flag mechanism; it also keeps the reuse
explicit and greppable rather than hidden in a kernel memo table.

(This is guidance for today, not a guarantee. We may cache instantiations
directly in the future — but a proof checker whose *soundness surface* has to
care about assistant speed is a design smell, so any such cache would have to
earn its keep without expanding what must be trusted. For now, caching stays
in the language, as named theorems.)

### KEYWORD: intheory

Forward-declares a theorem: `intheory <name>` promises that `<name>` will be
proved later in this file — a verified table of contents. (The name reads as
"in theory it holds — you're on the hook to prove it later.") A missing or
wrongly-kinded definition is an error at the `intheory` line.

```bpa
intheory addIsCommutative
```

A theory whose proofs live in sub-theory files makes the same promise with a
FORWARD — an alias to the fact another file proved — grouped in the same
section:

```bpa
import divides_theory <<< "std/integer/divides.bpa"
theorem gcdGreatest = divides_theory.gcdGreatest
```

`intheory` promises a fact proved later in THIS file; a forward is that promise
kept in another. Forward a theory's takeaway RESULTS, not the lemmas that got
there — a consumer wanting a lemma imports the sub-theory directly. Name the
import so it cannot collide with what it forwards (`divides_theory`, not
`divides`).

### KEYWORD: import

Loads another file under a namespace. Members are referenced with
qualified names (`peano.Nat`, `peano.addZeroLeft`). Paths beginning
`std/` resolve in the standard library (`$BPA_STD_DIR`, default `./std`);
other paths resolve relative to the importing file.

```bpa
import peano <<< "std/peano.bpa"
```

A cross-file citation is an `import` `using` step. By default it is fully
verified; under `--fast` (or `--fast-only import`) it is *admitted* — accepted
by matching the cited statement — and disclosed in the summary. Admitting the
word trusts the citation SHAPE, not the imported proof: a demanded imported
theorem is still re-checked in its own file, so a broken import is caught
regardless of the flag. Imported schematic theorems are always re-checked at
each instantiation (`instantiation` is never trustable).

### KEYWORD: alias

Any declaration keyword followed by `= qualified.name` creates a
kind-checked **view** of an imported entity — a local name for the same
thing, not a copy, so facts proved through either spelling interoperate.

```bpa
sort Nat = peano.Nat
func add = peano.add
axiom addZeroLeft = peano.addZeroLeft
theorem addIsCommutative = peano.addIsCommutative
```

### KEYWORD: model

Declares that a local sort **is a model of** an imported abstract theory, so
that theory's whole proven corpus transfers to the local sort — a working
feature used throughout `std/`. A `model NAME { … }` block interprets the
abstract theory's primitives as local symbols (with `:`) and discharges its
axiom obligations with local facts (with `<-`), and in exchange every theorem the
theory proves becomes citable at your sort via `[using model(NAME) source.thm]`.
Where an alias
identifies one entity with another, a `model` is a **named namespace of overloads** —
you map each of the theory's primitives (its sorts, operations, constants) and
discharge each of its axioms, and in exchange every theorem the theory proves becomes
citable at your sort.

```bpa
import group <<< "std/group.bpa"

model AdditiveGroup {
  group.Grp:      Rat               // `:` — a sort interpretation
  group.E:        ZERO              // `:` — primitives: source symbol : local symbol
  group.op:       add
  group.inverse:  neg
  group.opAssoc   <- addIsAssociative  // `<-` — an axiom obligation discharged by a local fact
  // ... one `<-` line per remaining group axiom
}
```

There is **no header of any kind** — a `model` is just its mappings, a bag of
overloads. Two line forms, distinguished by operator:
- **`source : target`** — INTERPRET a source sort or symbol as a local one (a
  sort-mapping like `group.Grp: Rat` is just one more overload in the bag). The
  target's arity/sort-shape must be compatible with the source's.
- **`source <- localFact`** — DISCHARGE a source axiom obligation with a local
  axiom or theorem whose formula, seen through the mapping, *is* that axiom.
Using `:` on an axiom (or `<-` on a symbol) is a hard error — the two relations
are distinct (interpretation vs. verification) and the syntax must say which you
mean. A source *theorem* is not mappable at all (it materializes through the
mapped axioms). The `@`-projection value (`src.ax <- OtherModel@src.thm`,
discharging via a theorem transferred through another model) is a `<-` form only.

**Guarded models — mapping onto a refined (subset) sort.**
A model is **GUARDED** (relativized to a subset) exactly when a sort-mapping's
target is a **predicated sort** — e.g. `group.Grp: GrpH` where
`sort GrpH = Grp where inH`. Each transferred theorem is then RELATIVIZED — a
`inH(x) ->` guard is injected at every binder over the mapped sort (a
multi-qualifier sort `Grp where inH and inK` injects the **conjunction**
`(inH(x) and inK(x)) ->`). Re-running the source proof, an instantiation at a
witness `t` owes `inH(t)`; the model must supply the fact that establishes it. It
does so by NOMINATING dischargers, right on the `:` symbol-map that introduces the
obligation — with a spelling that differs by symbol kind:

- **`src.C: TGT(fact, …)`** — a CONST mapped to `TGT` nominates the GROUND base
  fact(s) proving `TGT`'s membership, one per guard predicate of the target sort
  (parens form). E.g. `group.E: ZERO(zeroInH)` where `axiom zeroInH: inH(ZERO)`.
- **`src.op: F -| closure, …`** — a FUNC mapped to `F` nominates the CLOSURE
  fact(s): `F` preserves membership. E.g. `group.op: add -| addClosed` where
  `axiom addClosed: forall a, b; inH(a) -> inH(b) -> inH(add(a, b))`. The `-|`
  reverse-turnstile reads like `<-`: the obligation-bearer on the left, the
  discharging fact on the right. A comma list gives one closure per guard predicate.

Using the parens form on a func (or `-|` on a const) is a hard error. At each
membership obligation the transfer walks the witness term: a const cites its base
fact, a `fix`-bound variable uses its block guard, a composite `op(a, b)` applies
`op`'s nominated closure and RECURSES on the guarded arguments. An UNCONDITIONAL
source axiom mapped to itself is auto-WEAKENED (`∀a; P ⊢ ∀a; inH(a) -> P`), no
hand-written relativized copy needed.

```bpa
// the subgroup H ⊆ G is a group: map group's sort onto `Grp where inH`, nominate
// the membership facts, and the whole group corpus transfers relativized to H.
sort GrpH = Grp where inH
axiom identityInH: inH(E)
axiom invClosed:   forall a: Grp; inH(a) -> inH(inverse(a))

model SubgroupIsGroup {
  group.Grp:     GrpH
  group.E:       E(identityInH)          // const → base fact
  group.op:      op -| opClosed           // func → closure fact
  group.inverse: inverse -| invClosed
  group.opAssoc  <- group.opAssoc         // unconditional axiom, auto-weakened
}
```

A `<- OtherModel@src.thm` projection discharges an obligation by transferring a
theorem THROUGH another model — the composition that layers `subgroup`-is-a-group
onto `group`-is-a-group (see `tests/cases/model_subgroup_transfer.bpa`).

A model **may leave some axioms unmapped**. Citing a transferred theorem whose
proof depends on an unmapped axiom is **rejected**: under the transfer the unmapped
source axiom stays the source axiom, so its formula fails to match the transferred
step's (relativized) claim, and the step doesn't check.

The head is just `model NAME {` — there is NO `=` header or `where` on the head.
No mapping is distinguished: the sort a source theory reasons over is mapped by an
ordinary line in the block, and any guard is inferred from a predicated target
sort (below). The instance is **named** because one sort can model one theory more
than one way — ℚ is a group under `+` *and* (on ℚ∖{0}) under `×`. Each named model
keeps its own mapping; a use names which.

**Guarded models.** A model is relativized to a subdomain NOT via a header, but by
mapping the source theory's sort onto a **predicated (refined) sort** — the guard is
inferred from that sort's qualifier:

```bpa
sort NonzeroRat = Rat where nonzero   // the refined (predicated) sort
model MultiplicativeGroup {
  group.Grp:      NonzeroRat          // predicated target → the model is guarded by `nonzero`
  group.op:       mul
  group.E:        ONE
  group.inverse:  reciprocal
  // ... axiom obligations, each already guarded by `nonzero`
}
```

Mapping `group.Grp` onto the predicated `NonzeroRat` (= `Rat where nonzero`) makes
the model guarded: every transferred theorem picks up a `nonzero(...)` guard on each
of its bound variables (a `forall a: Grp; P(a)` becomes `forall a: Rat; nonzero(a)
-> P(a)`), and the local facts discharging the axioms must carry the same guards.
The guard is a **single unary predicate** over the mapped sort; for a compound
condition, `pred`-declare it (and, once where-reification lands, a `define` too).

**Using a transferred theorem** — cite it through the model with the `model`
justification rule (see *Justification rules* / *Automation*):

```bpa
theorem addCancelLeft: forall a, x, y: Rat; add(a, x) = add(a, y) -> x = y
proof
  @conclusion |
    forall a, x, y: Rat; add(a, x) = add(a, y) -> x = y
    [using model(AdditiveGroup) group.cancelLeft]
qed
```

`[using model(AdditiveGroup) group.cancelLeft]` takes `group`'s abstract
theorem, rewrites it through the `AdditiveGroup` mapping (relativizing by the
guard if any), and checks the result equals the goal. It is an **accelerant**:
under `--fast` the transfer is trusted wholesale and marks the theorem
accelerated (disclosed in the summary); in default mode it is legitimate because
the model's axiom obligations were themselves checked and the source theorem was
already proven over the abstract sort — so nothing is trusted that wasn't
derived.

**Transferring a SCHEMA.** A model can also transfer a source theory's *schema*
(an induction/recursion family like `peano.induction`, parameterized by a
predicate). Add an ordinary mapping line whose source is the schema and whose
target is a **locally-declared schema** of the same shape — an axiom *or* a
theorem:

```bpa
model NonNegInt {
  peano.Nat: NonNeg          // NonNeg = Int where non_neg  (guards the transfer)
  peano.succ: succ
  // ... axiom obligations ...
  peano.induction: nonnegInduction
}
```

The discharge target (`nonnegInduction`) must itself be a schema; its statement
must be the **guard-relativized remap** of the source's body (every `∀` over the
sort gains `non_neg(x) ->`). That match is verified once, at the model declaration
(even if the schema is never cited). Then `[using model(NonNegInt) peano.induction]`
inside a schema body instantiates the discharge at the caller's predicate
parameter — kernel-checked, untainted. (A schema transfer is only cited *inside a
schema body*, where a predicate parameter exists to instantiate.)

Note a schema transfer moves the *shape*, not any free lunch: a model's sort
still owns whatever axiomatic commitment the schema encodes (the discharge is
typically a local `axiom`). E.g. ℤ-induction cannot be derived from ℕ — the
nonneg model gives only the conditional nonneg schema — so ℤ still axiomatizes
its induction; the transfer just guarantees the nonneg schema is exactly ℕ's,
relativized.

> `model` is bpa's lightweight take on what typeclasses (Lean), locales
> (Isabelle), and module functors (Rocq) do — but explicit and search-free: you
> name the instance at every use, the mapping is one level deep, and the transfer
> is a checked source-to-source rewrite that never enters the kernel. No instance
> resolution, no coherence machinery. (See `MODEL-DESIGN.md`.)

## Formulas

Quantifier binders end with a semicolon; connectives are words; `->` is
implication (right-associative), `and`, `or`, `not` are the other boolean
operators, `iff` is the biconditional (lowest precedence), and `=` / `!=`
compare terms of the same sort.

`P iff Q` is **surface sugar** — it desugars to `(P -> Q) and (Q -> P)` and never
reaches the kernel. So a biconditional is proved with `iff_intro`, eliminated with
`iff_elim_forward`/`iff_elim_backward`, and — because `tautology` sees the
desugared conjunction — `tautology` decides `iff` goals and consumes `iff`
hypotheses for free. `iff_rewrite` substitutes across it (see Justification rules).
Because the shape `(X -> Y) and (Y -> X)` is canonically a biconditional, `and_intro`
is forbidden from producing it (use `iff_intro`) and `iff_intro` requires it.

**Mixed boolean operators require explicit parentheses.** A same-operator
chain is fine unparenthesized (`a or b or c`, `a -> b -> c`, `not not a`),
but nesting *different* boolean operators must be spelled out — `a and b or c`
is a parse error; write `(a and b) or c` or `a and (b or c)`. This applies to
all four operators, so `not p` as an operand of `and`/`or`/`->` also needs
parens (`(not p) and q`, `a -> (not b)`). The rule removes the classic
precedence-memory footgun: a formula reads one way to everyone, or it doesn't
parse. (`=` / `!=` are comparisons, not boolean operators, so they never need
parens against a connective: `x = y and p` is `(x = y) and p`.)

```bpa
forall a, b: Nat; add(a, b) = add(b, a)
exists w: Nat; add(x, succ(w)) = y
(not (p or q)) -> ((not p) and (not q))
```

`fun (k: Nat) => ...` lambdas appear only as schema arguments; they are
beta-reduced away during instantiation.

## Proofs

A proof is a sequence of steps. Each step is an `@`-sigiled label on its own
line, then — indented beneath it — the formula and its bracketed
justification:

```bpa
@have-imp |
  p -> q
  [by cite pImpliesQ]
@conclusion |
  q
  [by modus_ponens have-imp have-p]
```

The `@` marks a step **definition**; it sits at the left margin so labels form
a scannable gutter column. Citations of a label are **bare** (no `@`) — the
sigil distinguishes a definition from a use. The final step of the proof must
state the theorem's formula. Labels are the reference currency: rules cite
earlier steps and enclosing blocks by (bare) label.

### Subproof keywords

**`assume`** opens a block under a hypothesis; discharging it with
`implies_intro` yields the implication, with `not_intro` the negation.

```bpa
@hyp |
  assume less_than(a, b) {
    ...
  }
@imp |
  less_than(a, b) -> less_than(a, succ(b))
  [by implies_intro hyp]
```

**`fix`** opens a block with a fresh, arbitrary variable; discharging it
with `forall_intro` yields the universal. Fix variables must be globally
fresh within the proof.

```bpa
@gen |
  fix n: Nat {
    ...
  }
@all |
  forall n: Nat; ...
  [by forall_intro gen]
```

**`unpack ... from`** opens a block naming the witness of a previously
established existential; `exists_elim` exports any witness-free conclusion.

```bpa
@use-witness |
  unpack u: Nat from witnessed {
    @hu |
      add(a, succ(u)) = b
      [by hypothesis use-witness]
    ...
  }
@exported |
  less_than(a, b)
  [by exists_elim use-witness]
```

**`case ... on`** states a goal, then proves it by splitting a previously
established disjunction into one arm per disjunct — sugar for a (possibly
nested) `or_elim`. Each arm is an `assume`-block over one disjunct that must
conclude the goal. A left-nested `(A or B) or C` fans out automatically; you
write N arms, not a hand-nested `or_elim` tree.

```bpa
@result |
  q1 = q2
  case tri-q1q2 {
    @arm-lt |
      assume less_than(q1, q2) {
        ...
        @out |
          q1 = q2
          [by ...]
      }
    @arm-eq |
      assume q1 = q2 {
        @out |
          q1 = q2
          [by hypothesis arm-eq]
      }
    @arm-gt |
      assume less_than(q2, q1) {
        ...
        @out |
          q1 = q2
          [by ...]
      }
  }
```

The disjunction (`tri-q1q2`) is any prior step proving `A or B or ...`; the
"kind" of split is whatever lemma produced it (`trichotomy`, `zeroOrSucc`,
…). To split an existential, `unpack` its witness first, then
`case` on a disjunction about the now-in-scope witness. `case` is elaborator
sugar: the kernel checks the synthesized `or_elim` exactly as if hand-written,
so it adds no trust.

Steps may cite labels across the whole enclosing block regardless of textual
order (resolution is topologically sorted; a citation cycle is an error).
Nothing inside a closed subproof leaks out except through its discharge rule.

### Justification rules (overview table)

Every step ends with a bracketed justification whose FIRST word is one of **two
keywords** — the parser enforces the split:

- **`[by <rule> <refs>]`** — a KERNEL PRIMITIVE: pure inference the kernel checks
  directly (everything in this table down to `iff_rewrite`, plus `cite`). Refs are
  step or block labels (and fact names for `cite`). Term arguments go in parens:
  `[by forall_elim(succ(b)) some-step]`.
- **`[using <name> <refs>]`** — ENGINE PROOF-GENERATION: an ACCELERANT (the tactics
  below — `simplify`, `assoc_commut`, `polynomial`, `tautology`, `arithmetic`,
  `specialize`, …) or `instantiation` / `model`. These generate a kernel-checked
  certificate; `using` marks exactly the steps a future `--fast` could trust, so a
  `by`-only proof means the same under every mode.

Writing `using` on a kernel primitive, or `by` on an accelerant, is a hard parse
error (with an actionable message). This table is the at-a-glance index; the
gotcha-heavy and non-obvious rules get their own greppable `### RULE: <name>` leaf
below it (see the Index for the full anchor list).

**The complete partition** (every rule word is on exactly one side):

- **`by`** (kernel primitives): `cite`, `hypothesis`, `predicate`, `modus_ponens`,
  `implies_intro`, `forall_intro`, `forall_elim`, `exists_intro`, `exists_elim`,
  `and_intro`, `and_elim_left`, `and_elim_right`, `iff_intro`, `iff_elim_forward`,
  `iff_elim_backward`, `or_intro_left`, `or_intro_right`, `or_elim`, `not_intro`,
  `absurd`, `double_negation`, `reflexivity`, `symmetry`, `rewrite`, `iff_rewrite`.
- **`using`** (engine proof-generation): `instantiation`, `model`, `import`, and the
  accelerant tactics — `simplify`, `simplify_quantified`, `assoc_commut`,
  `assoc_commut_quantified`, `assoc`, `assoc_quantified`, `polynomial`,
  `polynomial_quantified`, `tautology`, `arithmetic`, `arithmetic_quantified`,
  `specialize`, `chain`, `extensionality`, `extensionality_quantified`.

| Rule | Meaning |
|---|---|
| `cite NAME` | cite a fact (axiom OR theorem) verbatim — kind-agnostic; the kernel picks its arm by the resolved fact's kind |
| `hypothesis BLOCK` | restate an enclosing block's assumption (or unpacked witness fact) |
| `predicate FIXBLOCK` | surface the guard of a predicated `fix h: H` binder — the fact `inH(h)` its refined sort provides |
| `modus_ponens IMP ANT` | from `P -> Q` and `P`, conclude `Q` |
| `implies_intro BLOCK` | discharge an assume block as an implication |
| `forall_intro BLOCK` | discharge a fix block as a universal |
| `forall_elim(t, ...) STEP` | specialize a universal at one or more terms — `forall_elim(A, B)` peels two binders in one step (the intermediate chain is synthesized) |
| `exists_intro(t) STEP` | from `P[t]`, conclude `exists x; P[x]` |
| `exists_elim BLOCK` | export an unpack block's witness-free conclusion |
| `and_intro L R` | conjunction from both conjuncts. REJECTS a biconditional-shape goal `(X -> Y) and (Y -> X)` — use `iff_intro` |
| `and_elim_left STEP` / `and_elim_right STEP` | project a conjunction |
| `iff_intro FWD BWD` | a biconditional `P iff Q` from its two directions (`P -> Q` then `Q -> P`). Requires an `iff`-shaped goal (a plain conjunction is `and_intro`'s job) |
| `iff_elim_forward STEP` / `iff_elim_backward STEP` | recover a direction of `P iff Q` (`P -> Q` / `Q -> P`) |
| `or_intro_left STEP` / `or_intro_right STEP` | inject into a disjunction |
| `or_elim DISJ LBLOCK RBLOCK` | case analysis: both assume blocks conclude the claim |
| `not_intro BLOCK S1 S2` | the assumption led to the contradiction `S1`/`S2`, so its negation holds |
| `absurd S1 S2` | from a contradiction, conclude anything |
| `double_negation STEP` | from `not not P`, conclude `P` |
| `reflexivity` | `t = t` |
| `symmetry STEP` | from a proven `x = y`, conclude `y = x` |
| `rewrite EQ TARGET` | replace occurrences of the equation's left side with its right side in `TARGET` |
| `iff_rewrite BICOND TARGET` | the propositional analogue of `rewrite`: from `P iff Q`, replace the sub-proposition `P` by `Q` at any position in `TARGET` (under connectives and quantifiers). A kernel-checked rule, no accelerant taint |
| `using instantiation NAME(args) refs...` | monomorphize a schema; refs discharge its leading antecedents |
| `simplify refs...` | tactic: join both sides of an equation by rewriting (see Automation) |
| `simplify_quantified refs...` | tactic: `simplify` under a `forall` prefix, without a hand `fix` (see Automation) |
| `assoc_commut [(assoc, comm, swap)] [refs...]` | tactic: reorder an associative-commutative sum by its A/C laws — bare uses well-known `add`/`mul`; `(assoc, comm, swap)` supplies the triple for a custom operator; cited refs (e.g. distributivity) pre-normalize first (see Automation) |
| `assoc_commut_quantified [(assoc, comm, swap)] [refs...]` | tactic: `assoc_commut` under a `forall` prefix, without a hand `fix` (see Automation) |
| `assoc(assocLemma)` | tactic: prove `s = t` when equal by **associativity alone** of one operator — right-nests both sides and compares. The associativity lemma is required; no reordering, no commutativity (see Automation) |
| `assoc_quantified(assocLemma)` | tactic: `assoc` under a `forall` prefix, without a hand `fix` (see Automation) |
| `polynomial(theory)` | tactic: prove an `add`/`mul` polynomial identity `s = t` by expanding both sides to a canonical sorted sum of sorted monomials (see Automation) |
| `polynomial_quantified(theory)` | tactic: `polynomial` under a `forall` prefix, without a hand `fix` (see Automation) |
| `tautology refs...` | tactic: propositional consequence (see Automation) |
| `arithmetic refs...` | tactic: linear arithmetic over Nat (see Automation) |
| `model(INSTANCE) source.theorem` | transfer an abstract theory's theorem to a sort that models it, remapped through the named model (see `KEYWORD: model` and `RULE: model`) |
| `import(I) thm` | cite a fact (axiom or theorem) from import `I`'s file across the file boundary (see `RULE: import`) |

The leaves below cover each rule that has a gotcha or a non-obvious ref count;
the simple rules get a one-line leaf too, so every rule name is greppable.

### RULE: cite

`[by cite NAME]` — cite a fact (an `axiom`, a proven `theorem`, or a `hole`)
verbatim; no refs. The goal must be the cited fact's formula exactly (up to
α-equivalence). KIND-AGNOSTIC: you don't name axiom-vs-theorem — the kernel picks
its arm by the resolved fact's kind. (`by axiom NAME` / `by theorem NAME` were the
old forms; they are no longer rule words — use `cite`.)

### RULE: hypothesis

`[by hypothesis BLOCK]` — restate an enclosing `assume` block's assumption, or the
witness fact of an enclosing `unpack` block. One ref: the block label.

```bpa
assume less_than(a, b) {
  @h |
    less_than(a, b)
    [by hypothesis <this-block-label>]
}
```

### RULE: predicate

`[by predicate FIXBLOCK]` — surface the guard of a predicated `fix h: H` binder:
the fact `inH(h)` that the refined sort `H = G where inH` provides. One ref: the
`fix` block label. See `KEYWORD: sort` (predicated sorts).

### RULE: modus_ponens

`[by modus_ponens IMP ANT]` — two refs: a step proving `P -> Q` and a step proving
`P`; concludes `Q`.

```bpa
@q |
  q
  [by modus_ponens have-imp have-p]
```

### RULE: implies_intro

`[by implies_intro BLOCK]` — one ref: an `assume P { … }` block whose last step is
`Q`; concludes `P -> Q`.

### RULE: forall_intro

`[by forall_intro BLOCK]` — one ref: a `fix x: S { … }` block whose last step is
`P(x)`; concludes `forall x: S; P(x)`. The fix variable must be globally fresh.
(For a predicated `fix x: H`, the conclusion is the relativized
`forall x: G; inH(x) -> P(x)`.)

### RULE: forall_elim

`[by forall_elim(t, ...) STEP]` — one step ref (a universal) plus a **parenthesized
term list**. The **multi-arg form peels several binders in one step**:
`forall_elim(A, B) STEP` on `forall x; forall y; P(x, y)` yields `P(A, B)` — the
intermediate `forall y; P(A, y)` chain is synthesized for you. Supply one term per
binder you want to peel.

```bpa
@specialized |
  P(A, B)
  [by forall_elim(A, B) universal-step]
```

### RULE: exists_intro

`[by exists_intro(t) STEP]` — one step ref proving `P[t]` plus the witness term `t`
in parens; concludes `exists x; P[x]`.

### RULE: exists_elim

`[by exists_elim BLOCK]` — one ref: an `unpack u: S from WIT { … }` block whose
last step is **witness-free** (does not mention `u`); exports that conclusion. The
eigenvariable `u` may not escape — a conclusion mentioning `u` is a kernel error.

```bpa
@exported |
  less_than(a, b)          // no `u` here
  [by exists_elim use-witness]
```

### RULE: and_intro

`[by and_intro L R]` — two refs, one per conjunct; concludes `L and R`. **REJECTS a
biconditional-shaped goal** `(X -> Y) and (Y -> X)` — that shape is canonically an
`iff`, so use `iff_intro` for it. Conversely, a plain (non-iff) conjunction is
`and_intro`'s job, not `iff_intro`'s.

### RULE: and_elim_left

`[by and_elim_left STEP]` — one ref proving `L and R`; projects the left conjunct
`L`. (`and_elim_right` projects `R`.)

### RULE: and_elim_right

`[by and_elim_right STEP]` — one ref proving `L and R`; projects the right conjunct
`R`.

### RULE: iff_intro

`[by iff_intro FWD BWD]` — two refs: a step proving `P -> Q` and a step proving
`Q -> P`; concludes `P iff Q`. **Requires an `iff`-shaped goal.** `and_intro`
rejects that shape, and `iff_intro` rejects a plain conjunction — the two are
complementary. `iff` is surface sugar for `(P -> Q) and (Q -> P)`.

```bpa
@bicond |
  P iff Q
  [by iff_intro forward-imp backward-imp]
```

### RULE: iff_elim_forward

`[by iff_elim_forward STEP]` — one ref proving `P iff Q`; recovers the forward
direction `P -> Q`. (`iff_elim_backward` recovers `Q -> P`.)

### RULE: iff_elim_backward

`[by iff_elim_backward STEP]` — one ref proving `P iff Q`; recovers the backward
direction `Q -> P`.

### RULE: or_intro_left

`[by or_intro_left STEP]` — one ref proving `P`; concludes `P or Q` for the goal's
right disjunct `Q`. (`or_intro_right` proves `Q` to conclude `P or Q`.)

### RULE: or_intro_right

`[by or_intro_right STEP]` — one ref proving `Q`; concludes `P or Q`.

### RULE: or_elim

`[by or_elim DISJ LBLOCK RBLOCK]` — **THREE refs, and it is BINARY**: a step proving
`A or B`, then two `assume` blocks — `assume A { … }` and `assume B { … }` — **each
of which must conclude the same goal**. That shared conclusion is the result.

```bpa
@goal-from-cases |
  R
  or_elim disj {
    @left  | assume A { … @out | R | [by …] }
    @right | assume B { … @out | R | [by …] }
  }
```

Footgun: `or_elim` is **not N-ary**. A three-way split `(A or B) or C` needs either a
hand-nested `or_elim` (elim the outer, then elim `A or B` inside the left arm) or —
far better — the `case` sugar, which fans out a left-nested disjunction into N
arms automatically (see `case ... on` under Subproof keywords).

### RULE: not_intro

`[by not_intro BLOCK S1 S2]` — **THREE refs**: an `assume P { … }` block and two of
its steps `S1`, `S2` that contradict each other (`S1 = X`, `S2 = not X`). Concludes
`not P`. The contradiction pair is named explicitly; both steps must live inside the
block.

```bpa
@neg |
  not even(ONE)
  [by not_intro assumed-block contra-a contra-b]
```

### RULE: absurd

`[by absurd S1 S2]` — two refs proving `X` and `not X`; concludes **any** goal
(ex falso). Use it to close an unreachable arm.

### RULE: double_negation

`[by double_negation STEP]` — one ref proving `not not P`; concludes `P`.

### RULE: reflexivity

`[by reflexivity]` — no refs; proves `t = t` (the goal must be a syntactic equality
of a term with itself).

### RULE: symmetry

`[by symmetry STEP]` — one ref proving `x = y`; concludes `y = x`.

### RULE: rewrite

`[by rewrite EQ TARGET]` — two refs: an equation `a = b` and a target step; replaces
occurrences of `a` with `b` — **or** `b` with `a` — in the target. **Bidirectional:**
the kernel tries both orientations, so you do **not** need a preceding `symmetry`
step just to reorient the equation (a true `a = b` licenses substituting either
way). A claim reachable in NEITHER direction is rejected. (The tactic `simplify`
rewrites both sides to a common form when many rewrites would be needed.)

```bpa
@rewritten |
  P(b)
  [by rewrite eq-a-b target-Pa]
```

### RULE: iff_rewrite

`[by iff_rewrite BICOND TARGET]` — two refs: a biconditional `P iff Q` and a target
step; the **propositional analogue of `rewrite`**. It replaces the sub-proposition
`P` by `Q` — **or `Q` by `P`** (bidirectional, like `rewrite`) — at any position in
the target, **under connectives and quantifiers**, which plain `rewrite` (a
term-equation rule) cannot reach. A kernel-checked rule with **no accelerant taint**.

```bpa
@rewritten |
  R(Q)
  [by iff_rewrite bicond-P-Q target-R-of-P]
```

### TACTIC: instantiation

`[using instantiation NAME(args) refs...]` — monomorphize the schema `NAME` at the
written-out `args` (formula params supplied as `fun … => …` lambdas). Trailing refs
discharge the instance's **leading antecedents** (its `->` premises), left to right.
The proof body is re-checked at this instance (see `KEYWORD: schematic`). Reusing an
expensive instance? Realize it into a named theorem and cite that instead.

```bpa
@applied |
  (not q) -> (not p)
  [using instantiation contrapositive(fun => p, fun => q) have-p-imp-q]
```

### RULE: specialize

`[using specialize HEAD(args) hyps...]` — apply a `forall`-quantified fact `HEAD` in
ONE step: it ∀-elims `HEAD` at each written-out `args` (peeling the universal
prefix), then modus_ponens each trailing hyp ref against a leading `->` antecedent,
left to right. The result must be the goal. **`HEAD` may be a declared THEOREM/AXIOM
name OR a LOCAL STEP LABEL** — a `forall`-shaped fact held in a proof step (an
`assume`d, unpacked, or derived universal). So a local universal gets the same
one-liner as a named lemma (no need to hand-roll `forall_elim` + `modus_ponens`).

This is pure sugar over `forall_elim` + `modus_ponens` — it EMITS those kernel
steps as a certificate the kernel re-checks, so it is fully verified and carries no
`--fast` taint. It exists to collapse the ubiquitous three-step "apply a lemma"
ritual (`@rule | ∀…; P->Q [by cite L]` / `@at-a | P(a)->Q(a) [by forall_elim(a)
rule]` / `@got | Q(a) [by modus_ponens at-a hyp]`) into a single step with no
throwaway `-rule`/`-at-args` labels.

```bpa
// forall a, d; d>0 -> exists q,r; a = dq+r ∧ 0≤r<d, applied at (a, d):
@decomposed |
  exists q: Int; exists r: Int; a = add(mul(d, q), r) and (is_nonneg(r) and less_than(r, d))
  [using specialize divisionAlgorithmExists(a, d) d-is-positive]
```

Multi-arg peels several binders; multiple hyps discharge several antecedents in
order. With NO hyps it is a bare specialization (just the ∀-elim chain). For a
parameterized SCHEMA (a `prop`-parameter), use `instantiation` instead — `specialize`
is for ordinary quantified theorems.

### RULE: chain

`[using chain eq1 eq2 ...]` — prove an equality goal `A = Z` from the cited
equations, used in ANY direction and closed under congruence. Each `eqN` is a
proven step / axiom / theorem of the form `X = Y`; `chain` searches (BFS) for
a rewrite path connecting `A` to `Z`, using each equation forward OR backward, and
because rewriting substitutes congruent SUBTERMS it gets congruence
(`a = b ⟹ f(…a…) = f(…b…)`) for free.

Where `simplify` orients each equation left-to-right and reduces both sides to a
normal form (and FAILS when the equations must point in conflicting directions),
`chain` is orientation-free — it is the tool for a hand-run transitivity
chain (`A = B`, `C = B`, `D = C` ⊢ `A = D`). It emits a `reflexivity` +
`symmetry`/`rewrite` certificate the kernel re-checks (no `--fast` taint).

```bpa
// A = B, C = B (backwards), D = C ⊢ A = D, plus a congruence in one:
@a-equals-d |
  mul(pu(s, k), at(s, k)) = mul(pu(t2, lprev), at(s, k))
  [using chain s-succ-product-splits equal-products t2-product-is-l-product tm-equals-sk]
```

Use `simplify` for oriented normal-form equalities (ring identities), `chain`
for stitching a bag of equations (some used backward) into `A = Z`.

**Args and hyps INTERLEAVE by formula structure.** `specialize` walks the cited
formula: at each `forall` it consumes the next argument, at each leading `->` it
consumes the next hypothesis, in the order the formula dictates. So the common
guarded-induction shape `forall k; guard(k) -> forall s, t; …` is applied in one
step — the args `(k, s, t)` and the hyps thread through the interleaved binders and
antecedents automatically:

```bpa
// forall k; is_nonneg(k) -> forall s,t,l; is_nonneg(l) -> … -> k = l
@k-equals-l |
  k = l
  [using specialize factorizationLengthUnique(k, s, t, l) k-nonneg l-nonneg s-primes t-primes eq]
```

### RULE: model

`[using model(INSTANCE) source.theorem]` — transfer an abstract theory's proven theorem
to a sort that models it. It takes the source theorem, rewrites it through the named
model's mapping (relativizing by the guard if the model is guarded), and checks the
result equals the goal. See `KEYWORD: model` for the mapping block.

```bpa
@conclusion |
  forall a, x, y: Rat; add(a, x) = add(a, y) -> x = y
  [using model(AdditiveGroup) group.cancelLeft]
```

It is an **accelerant**: in default (strict) mode it is legitimate because the
model's axiom obligations were checked and the source theorem was already proven, so
nothing untrusted enters — but under `--fast` the transfer is trusted wholesale and
marks the theorem accelerated. A model that leaves some source axioms unmapped is
**rejected** in strict mode when a cited transferred theorem depends on a missing
obligation (named in the error); `--fast` passes it provisionally.

### RULE: import

`[using import(I) thm]` — cite a theorem `thm` from import `I`'s file across the file
boundary. `I` names an `import` in scope; `thm` is a theorem (or axiom) that file
proves; the goal must equal its formula (up to α-equivalence).

```bpa
import lib <<< "std/lib.bpa"
// ...
@conclusion |
  forall n: Nat; succ(n) = succ(n)
  [using import(lib) congThm]
```

This is the explicit cross-file-citation **accelerant** — the file-boundary trust
seam, mirroring `model`, and the PREFERRED way to cite an imported theorem: a
cross-file citation is an accelerated step a future `--fast` can trust as a unit.
(A qualified `[by cite lib.thm]` also works and is mechanically identical today —
both resolve the imported fact and the kernel re-matches its formula — but it is a
re-checked obligation with no accelerant seam; use `using import(I) thm` for cross-
file citation, and `by cite` for a SAME-file fact.)

## The kernel

The trusted core is deliberately tiny, and everything else is built to
keep it that way.

- **Only concrete first-order logic ever reaches it.** The kernel checks a
  lowered proof: a flat list of steps and blocks, each step carrying its
  formula and justification. It re-derives every rule application itself —
  claim mismatches, inaccessible references, unclosed blocks, and
  eigenvariable violations are all kernel errors.
- **The elaborator is untrusted.** Parsing, name resolution, sort
  checking, schema monomorphization, and every tactic live outside the
  trust boundary. They can only *prepare* steps; the kernel accepts
  nothing on their word (with the single, disclosed exception of accelerated
  steps — see below).
- **Terms are locally nameless.** Bound variables are de Bruijn indices,
  free variables are named and sorted. Substitution can never capture,
  alpha-equivalence is structural equality, and eigenvariable conditions
  are simple occurrence checks.
- **Schemas are checked per instance.** A schema body is stored as a form;
  instantiation substitutes the written-out arguments (capture-proof by
  construction) and produces a concrete formula the kernel can check. A
  theorem schema's stored proof is re-elaborated and re-checked at every
  instantiation.
- **Guards become obligations.** Applying a `requires`-guarded function
  raises a proof obligation, wrapped in whatever logical context surrounds
  the application (binders, antecedents, left conjuncts) and matched
  against facts available where it is owed.

## Automation

Three tactic rules discharge goals in one step. All three follow the same
trust policy, **certificate first, accelerated fallback**:

1. The tactic first tries to emit a *certificate*: ordinary kernel steps
   (rewrites, case splits, witness introductions) synthesized into the
   proof and checked like hand-written ones. A certificated use **emits kernel steps**
   — exactly as trustworthy as a manual proof.
2. Only when the goal is decidable but outside the certificate fragment
   does the tactic reach for its *accelerated* path: the decision procedure's verdict.
   By default this is a **hard error** — the goal must certify. Only under
   `--fast` is the accelerated verdict accepted (without a derivation); its name
   then **marks** the theorem accelerated, transitively through citations, and the
   summary discloses it: `6 theorems proven (1 accelerated:
   arithmetic)` under a loud not-fully-verified banner.

A failed tactic never marks anything accelerated: wrong goals produce located errors
with copy-pasteable detail (unjoinable normal forms, propositional
countermodels, concrete arithmetic counterexamples).

### TACTIC: simplify

Equational rewriting (always emits kernel steps).

`[using simplify f1 f2 ...]` proves an equation by rewriting both sides to a
common normal form using the cited facts (universally quantified equations
or equation steps) as left-to-right rules. The certificate *is* the
rewrite chain; there is no accelerated path. Cycling rule sets hit a hard rewrite cap
instead of hanging.

```bpa
@succ-case |
  add(succ(k), ZERO) = succ(k)
  [using simplify addSuccLeft inductive-hypothesis]
```

`simplify` proves a bare equation; on a `forall x…; s = t` goal use
`simplify_quantified`, which peels the universal prefix (no hand `fix`),
runs the same core on the body, and closes with `forall_intro`. Each tactic
suggests the other if you pick the wrong one for the goal shape.

### TACTIC: assoc_commut

Associative-commutative reordering.

`[using assoc_commut]` proves `s = t` when both are sums over an associative-
commutative operator with the same multiset of summands, differing only by
associativity and commutativity — including sums whose summands are **arbitrary
opaque terms** (`sumTo(k)`, `mul(k, k)`), which `simplify` cannot reorder (a
commutativity rewrite rule loops) and `arithmetic` treats as opaque and
declines. It re-associates each side to a canonical form and emits the swap
chain as kernel steps; different multisets are a located `assoc_commut: sides
have different summands` error.

```bpa
@swapped |
  add(add(a, b), add(c, d)) = add(add(a, c), add(b, d))
  [using assoc_commut]
```

**Two forms, no partials** — you either supply the whole AC triple or rely on
the well-known one:

- **bare `assoc_commut`** — the operator is chosen from the goal's left-hand-
  side head (`add` or `mul`) and its AC triple (`addIsAssociative`/
  `addIsCommutative`/`addLeftSwap`, or the `mul` triple) is resolved **by
  well-known name in scope**.
- **`assoc_commut(assoc, comm, swap)`** — supply the three AC lemmas
  explicitly, for a **custom operator** whose lemmas aren't named by the
  convention. The operator is recovered from the commutativity lemma's shape
  (`f(a, b) = f(b, a)` → `f`). Exactly three args, or a located error.

```bpa
// a custom operator `join` with its own (non-conventionally-named) AC laws
@reorder |
  join(join(a, b), join(c, d)) = join(join(a, c), join(b, d))
  [using assoc_commut(joinAssoc, joinComm, joinSwap)]
```

**Under a `forall` prefix**, use `assoc_commut_quantified` (peels the binders,
no hand `fix`), the AC analog of `simplify_quantified`.

**Distributivity**: cite rewrite lemmas (e.g. `mulAddDistribRight`) as trailing
refs and `assoc_commut` applies them L→R to each side as pre-normalization
*before* the reorder — so `mul(add(a, b), c) = add(mul(b, c), mul(a, c))`
certifies in one step (distribute, then AC-sort the resulting sum of products):

```bpa
@conclusion |
  forall a, b, c: Nat; mul(add(a, b), c) = add(mul(b, c), mul(a, c))
  [using assoc_commut_quantified mulAddDistribRight]
```

**The `--fast` accelerated path** (bare form only): a theory that declares an operator
but doesn't *prove* its AC laws can't certify — the default declines ("needs
`addIsAssociative` in scope"). Under `--fast`, `assoc_commut` **decides** the
reordering by comparing sorted multisets structurally, WITHOUT resolving any
lemma — **trusting** that the operator is associative-commutative. That
presumption about a symbol whose laws are never checked is why the result is
**accelerated** (`accelerated: assoc_commut`). The explicit-triple form always
certifies (the triple is checkable), so it has no accelerated path.

### TACTIC: assoc

Associativity-only reordering.

`[using assoc(assocLemma)]` proves `s = t` when both are equal by **associativity
alone** of a single operator — the non-commutative sibling of `assoc_commut`.
It right-nests each side (associativity is confluent and terminating, so
right-nesting is a canonical form) and compares; no reordering, no
commutativity. This is what you reach for in **non-commutative** algebra (group
theory: rearranging `(ab)c` ↔ `a(bc)`), where `assoc_commut` does not apply.

```bpa
// a custom group operator `op` with its associativity axiom `opAssoc`
@rearrange |
  op(op(op(a, b), c), d) = op(a, op(b, op(c, d)))
  [using assoc(opAssoc)]
```

**The associativity lemma is REQUIRED** — there is no bare form and no
assumption the operator is `add`/`mul`. `assoc` takes exactly one argument, the
lemma of shape `f(f(a,b),c) = f(a,f(b,c))`, and recovers the operator `f` from
it. This keeps `assoc` fully parameterized by its cited axiom (zero dependence
on ambient scope or well-known names). Bare `[using assoc]` is a located error;
sides that differ by more than associativity report `assoc: sides differ by more
than associativity`. **Under a `forall` prefix**, use `assoc_quantified`.

**The `--fast` accelerated path**: under `--fast`, `assoc` skips *emitting* the rewrite
certificate — it structurally right-nests both sides and compares, presuming the
operator is associative without kernel-checking the rearrangement — and is marked accelerated
(`accelerated: assoc`). By default it certifies (the rewrite chain is checked).

### TACTIC: polynomial

Nonlinear identities.

`[using polynomial(theory)]` proves an `add`/`mul` polynomial identity `s = t`
when both sides expand to the same polynomial — the nonlinear analogue of
`assoc_commut`. It canonicalizes each side to a **sorted sum of sorted
monomials**: distribute `mul` over `add`, sort each monomial's factors, sort the
sum, and fold identity/zero factors. Where `assoc_commut` reorders a sum with a
*fixed* multiset of summands, `polynomial` first *expands* products — so
`(a+b)² = a²+2ab+b²` certifies in one step, which neither `assoc_commut` (it
doesn't distribute the square) nor `arithmetic` (nonlinear, `mul` of two
variables is opaque) can do. It emits a ring-rewrite certificate the kernel
re-checks; different expansions are a located `polynomial: sides expand
differently: '<nf(s)>' vs '<nf(t)>'` error.

```bpa
@square |
  forall a, b: Nat;
    mul(add(a, b), add(a, b)) = add(mul(a, a), add(mul(a, b), add(mul(a, b), mul(b, b))))
  [using polynomial_quantified(peano)]
```

Like `arithmetic`, it is **theory-parameterized**: `polynomial(peano)` resolves
the ring vocabulary (`add`/`mul`) and lemmas against the named upstream module,
independent of local aliases; bare `polynomial` resolves against local scope.
**Under a `forall` prefix**, use `polynomial_quantified` (peels the binders).

In a **ring theory** (`neg`/`sub` and their lemmas in scope, e.g. `integer`),
`polynomial` also:
- **expands `sub`/`neg`** — `sub(a,b)` unfolds to `add(a, neg(b))` and `neg`
  pushes to the leaves (`neg(a·b) = neg(a)·b`, `neg(neg x) = x`), so
  `a·(b−c) = a·b − a·c` certifies in one step;
- **cancels additive inverses** — `t + neg(t) → 0`, so `a·r + neg(a·r) = 0`;
- **folds numeral coefficients by expansion** — a `succ`-tower coefficient
  expands into repeated addition (`mul(TWO, q)` and `add(q, q)` meet at the same
  sum), so `2q + 2q = 4q`, `(2q)² = 4q²`, and `(2q+1)² = 4q² + 4q + 1` certify
  directly. (In a pure-ℕ theory like `peano`, `neg`/`sub` are absent and those
  folds are simply skipped — `polynomial(peano)` is unchanged.)

Scope: identities only (`=`); cancellation (`x·a = x·b ⊢ a = b`) is not an
identity — that stays with `mulCancel`/`arithmetic`. `neg(x)` on a bare variable
stays an opaque atom (the coefficient model is unsigned), so `x + neg(x)` cancels
but `polynomial` does not reason about the *sign* of an isolated `neg` variable.

**The `--fast` accelerated path**: on a theory too thin to certify (`add`/`mul` declared
but the ring lemmas absent), the default declines ("needs `mulAddDistribLeft`
in scope"). Under `--fast`, `polynomial` **decides** the identity by comparing
pure syntactic semiring normal forms — no lemmas consulted — **trusting** that
`add`/`mul` form a commutative semiring. That presumption about symbols whose
laws are never checked is why the result is **accelerated** (`accelerated:
polynomial`). A false identity is still rejected (the accelerated tactic *decides*); the
acceleration is for the unproven ring-structure assumption, not for the comparison.

### TACTIC: extensionality

Extensionality-reduction.

`[using extensionality(<extLemma>) <unfold lemmas…>]` proves an equation `LHS = RHS`
between extensional objects by the *element-chase*: reduce `LHS = RHS`, through the
cited extensionality lemma, to its pointwise obligation; fix an element; unfold the
operators with the cited characterization lemmas; and close the residue. It is the
mapping/set analogue of `polynomial` — a **structure tactic**: the SAME tactic proves
set equations and function equations (and any extensional theory), selected by the
lemmas you cite. Under a `forall` prefix, use `extensionality_quantified`.
(Prior art: Lean's `ext`.)

```bpa
@intersection-commutes |
  forall a, b: Set; intersection(a, b) = intersection(b, a)
  [using extensionality_quantified(extensionality) intersectionMember]

@compose-associates |
  forall h, g, f: Fn; compose(compose(h, g), f) = compose(h, compose(g, f))
  [using extensionality_quantified(funcExtensionality) composeApply]
```

The parenthesized argument is the theory's extensionality lemma (`set.extensionality`,
`function.funcExtensionality`, or a local alias of either); the element sort is read
off that lemma's pointwise binder, so nothing is looked up by name. The remaining
refs are the unfold lemmas for the operators the equation mentions (`unionMember`,
`differenceMember`, `composeApply`, `identityApply`, …) — cite exactly the ones the
sides use. The tactic reads the residue's shape to pick its closer: a **set** equation
unfolds `member(x, ·)` and closes the propositional residue with `tautology`; a
**function** equation unfolds `apply(·, x)` and closes the equational residue with the
rewrite join. One line replaces the ~85-line hand element-chase; every emitted step is
a kernel tactic. A false identity is rejected — the pointwise residue reports a
countermodel or the rewrite join fails to meet.

### TACTIC: tautology

Propositional consequence.

`[using tautology refs...]` proves any goal that follows propositionally from
the cited premises, treating non-propositional subformulas as opaque
atoms. Valid goals replay as certificates (case splits via an inline
excluded middle); non-consequences report a countermodel
(`countermodel: p := true, q := false`). Atom limit: 16.

### TACTIC: arithmetic

Linear arithmetic over Nat.

`[using arithmetic refs...]` decides goals over `ZERO`, `ONE`, `succ`, `add`,
`mul`-by-literal, `=`, `!=`, and `less_than`, with full propositional
structure and quantifiers over Nat; anything else becomes an opaque
propositional atom in an SMT-style combination. The vocabulary is
recognized by those well-known names in the current scope, and
certificates additionally use the standard peano lemmas
(`addZeroRight`, `addIsCommutative`, `addLeftSwap`, `lessThanIntro`,
`lessThanElim`, ...) when they resolve — import them from `std/peano.bpa`
to keep uses emitting kernel steps. Certificates cover ground and universally quantified
linear goals, order goals, constant-witness existentials, hypothesis
chains, and mixed skeletons; goals whose replay would itself require
induction fall back to the accelerated path. False statements report concrete
values: `arithmetic: false at a := 0, b := 0`; a relation that is only
undecidable because it hides a nonlinear term (e.g. `mul(a, b) = mul(b, a)`)
reports `'mul(a, b)' is outside linear arithmetic` rather than a countermodel.

```bpa
@conc-in |
  less_than(a, succ(b))
  [using arithmetic have]
```

> [!WARNING]
> This may be expanded in the future to support signed integers (exact, as
> everything in bpa).

The full trust statement for each accelerated tactic — module, verdict semantics,
certificate coverage — lives in `ACCELERATION.md`.

## Query commands (read-only inspection)

`bpa query <op>` inspects `.bpa` files (and `.md` literate documents — the
`bpa` blocks are extracted the same way `check` does) without checking them,
for navigating a proof corpus. grep is the right tool for most searches (label
audits, "who uses `[using arithmetic]`", counting); these cover the cases grep
can't do cleanly.

| Command | What it does |
|---|---|
| `bpa query outline <file> [theorem]` | the proof *skeleton*: one line per step (bare label), with a header on each block opener (`fix`/`assume`/`unpack`/`case`). No theorem arg = every proof in the file. |
| `bpa query claims <file> [theorem]` | the same skeleton as `outline`, but each step shows its **claim formula** instead of its label — the propositions the proof establishes, label-free (block openers keep their `fix`/`assume`/`case` headers). Reads as the mathematical content; `outline` reads as the table of contents. Works on proof-carrying schemas too. |
| `bpa query theorem <file> <name> [--sig]` | the full verbatim source of one declaration — statement + `proof … qed` + leading doc-comment. Follows aliases across files to the real proof; axioms are marked. `--sig` prints **just the statement** (kind + name + formula), wrap-collapsed to one line — handy for reading binder order/arity before a `forall_elim`. |
| `bpa query whereis <file> <identifier>` | trace an identifier through every alias/import hop to its **origin** — the file-chase as one command. Works for any named decl (theorem/axiom/func/pred/sort/const/define/schema) and for import namespaces. Each hop shows `file:line` + the source line; the origin is marked. |
| `bpa query search <path> <query>` | fuzzy-search theorem/axiom **names + statements** — find a lemma by concept when you don't recall its name (`search std cancel` → `mulCancelLeft`, `addCancelLeft`, …). `<path>` is a **directory** (search every `.bpa` under it — corpus discovery) or a **file** (search it + everything it transitively imports — only results citable from there). Ranked, one line per hit: `file:line  <kind> <name>: <statement>`. Query terms are AND'd. Self-contained/deterministic (no ML). |

```
$ bpa query whereis std/peano/parity.bpa addZeroRight
addZeroRight
  std/peano/parity.bpa:30:  theorem addZeroRight = peano.addZeroRight
  std/peano.bpa:79:  theorem addZeroRight: forall n: Nat; add(n, ZERO) = n  [origin]
```

## Lint

`bpa lint <file>` reports **convention** violations that `check` deliberately
ignores because they don't affect validity — the point is corpus consistency, so
mechanisms that match on syntactic shape stay frictionless. Today it enforces one
rule: **canonical binder order** — a leading `forall` must bind its variables in
first-appearance order (`forall a, b, c; add(add(a, b), c) = …`, never `forall c,
b, a`). A permuted order is logically identical but fails α-matching, which breaks
`model`'s axiom discharge (forcing a hand-written reordering adapter). Reads `.md`
too; naming/casing rules (future) are suspended for literate transliterations,
which mirror their source's notation. See `CONVENTIONS.md`.

## Debug (inspect an accelerant's output)

`bpa debug accelerant <file> <selector>` reprints the **synthetic theorem** an
accelerated step produced — statement + proof, as valid bpa. In strict mode every
`[by <tactic> …]` wraps its certificate into a kernel-checked, count-suppressed
theorem (`<tactic>$n`, context-free — it cites nothing from the environment; see
`ACCELERATION.md`); `debug` materializes and prints it. The selector is a **line
number** or an enclosing **theorem + step-label** pair.

```
$ bpa debug accelerant tests/cases/farkas.bpa belowBothWaysIsAbsurd conclusion
theorem arithmetic: forall a: Nat; forall b: Nat; less_than(a, b) -> less_than(b, a) -> less_than(a, a)
proof
  ...
      @s8 |
        less_than(a, a)
        [by modus_ponens s7 s2]
  ...
qed
```

The output round-trips: fed back through `bpa check` it re-verifies from scratch.
It loads through the full multi-file loader, so it works on files with imports
(and on recursive synthetics like a `model` materialization citing another). The
kernel-steps → bpa-source renderer underneath is also the IR a mechanical
Lean/Isabelle/Rocq export would consume.

`bpa debug taint <file> [theorem]` is the companion trust-entry audit: per proof,
every step whose rule can fall back to an accelerated verdict (`arithmetic`,
`tautology`, `polynomial`, `assoc_commut`, `assoc`, `extensionality`, and quantified
variants), at its `file:line:col`. A syntactic upper bound — a flagged step may
still certify — so a clean report guarantees every step is kernel-checked. Pure
over the AST (no elaboration), like the `query` commands.
