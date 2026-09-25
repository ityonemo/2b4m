---
name: 2b4m-query
description: Inspect and navigate a 2b4m proof corpus (.b4m files) with the `2b4m query` commands — outline a proof's structure, print a theorem's full source or one-line signature, trace an identifier to its origin across alias/import hops, fuzzy-search for a lemma by name/concept, or audit what a proof depends on (rules + cited axioms/theorems). Use these BEFORE grepping for anything that involves a proof's shape, a theorem's exact statement/binder-order, following an alias to another file, finding a lemma when you don't recall its name, or "which proofs use rule/lemma X" / "what does theorem X depend on". (To flag a proof's accelerated tactics — "is this fully kernel-checked, where does trust enter" — use `2b4m debug taint`, not a query.) For plain text searches (counts, listing declarations, raw label greps) prefer grep — these tools cover only what grep can't do cleanly.
---

# 2b4m query — navigating a proof corpus

`2b4m query <op>` reads `.b4m` files (and `.md` literate documents — the ```2b4m
blocks are extracted, like `check`) without checking them, for navigation. Build
the binary first if needed (`zig build`); it lands at `./zig-out/bin/2b4m`.

**Guiding principle: we love grep.** grep/sed/awk are the default for plain
text searches over the corpus — counts, listing `^theorem`/`^forward`/`^axiom`,
raw label greps (`grep -rhoE '@[a-z-]+' std/*.b4m`). Reach for `2b4m query` for
the things grep does badly: a proof's *structure*, a theorem's *exact statement*
(which may wrap across lines), *following aliases across files*, *finding a
lemma by concept* when the name is fuzzy, and — the semantic questions grep gets
*wrong* — *what a proof depends on* and *which proofs use a rule or lemma*
(a `[by …]` can wrap across lines and an alias hides the real target, so a grep
both misses and misreports) and *whether a proof can accelerate*. Each command below
exists precisely because grep can't do that one thing correctly in one step.

## The six commands

### `2b4m query outline <file> [theorem]`
The proof **skeleton**: one line per step (bare label), with a header on each
block opener (`fix`/`assume`/`unpack`/`case`). No theorem arg → every proof in
the file. Use to grasp a proof's shape without reading the whole body.

```
$ 2b4m query outline std/peano.b4m addZeroRight
theorem addZeroRight
  add-zero-left
  base-case
  induction-step  fix k
    given-inductive-hypothesis  assume add(k, ZERO) = k
      ...
  conclusion
```

### `2b4m query claims <file> [theorem]`
The same skeleton as `outline`, but each step shows its **claim formula** instead
of its label — the propositions the proof establishes, label-free (block openers
keep their `fix`/`assume`/`case` headers). `outline` reads as the table of
contents; `claims` reads as the mathematical content. Works on proof-carrying
schemas too. Use when you want the *argument* (what is proved, step by step)
rather than the *structure*.

```
$ 2b4m query claims std/peano.b4m addZeroRight
theorem addZeroRight
  add(ZERO, ZERO) = ZERO
  fix k
    assume add(k, ZERO) = k
      add(k, ZERO) = k
      add(succ(k), ZERO) = succ(k)
    add(k, ZERO) = k -> add(succ(k), ZERO) = succ(k)
  forall k: Nat; add(k, ZERO) = k -> add(succ(k), ZERO) = succ(k)
  forall n: Nat; add(n, ZERO) = n
```

### `2b4m query theorem <file> <name> [--sig]`
The full verbatim source of one declaration — statement + `proof … qed` + its
leading doc-comment. **Follows aliases across files** to the real proof; axioms
are marked. `--sig` prints **just the statement** (kind + name + formula),
wrap-collapsed to one line — the fast way to read **binder order / arity before
a `forall_elim`** (its args are outermost-first, and the statement may wrap in
source, so grep+head is unreliable).

```
$ 2b4m query theorem std/peano-ordering.b4m multiplicationPreservesOrder --sig
theorem multiplicationPreservesOrder: forall c, b, a: Nat; less_than(a, b) -> less_than(mul(succ(c), a), mul(succ(c), b))
```

### `2b4m query whereis <file> <identifier>`
Trace an identifier through every alias/import hop to its **origin** — the
file-chase as one command (grep finds one hop; you'd re-grep per hop). Works for
any named decl (theorem/axiom/func/pred/sort/const/define/schema) and for import
namespaces. Each hop shows `file:line` + the source line; origin marked.

```
$ 2b4m query whereis std/peano/parity.b4m addZeroRight
addZeroRight
  std/peano/parity.b4m:30:  theorem addZeroRight = peano.addZeroRight
  std/peano.b4m:79:  theorem addZeroRight: forall n: Nat; add(n, ZERO) = n  [origin]
```

### `2b4m query search <path> <query>`
Fuzzy-search theorem/axiom **names + statements** — find a lemma by concept
when you don't recall its name. `<path>` is a **directory** (every `.b4m` under
it — corpus discovery) or a **file** (that file + everything it transitively
imports — only results citable from there). Query terms are AND'd; ranked by
name-exact > name-substring > statement-token. One line per hit. Self-contained
and deterministic (no ML — semantic search is a future, caching-era upgrade).

```
$ 2b4m query search std cancel
std/peano-ordering.b4m:1094:  theorem lessThanAddCancelLeft: forall c, a, b: Nat; less_than(add(c, a), add(c, b)) -> less_than(a, b)
std/peano-ordering.b4m:1960:  theorem mulCancelLeft: forall c, a, b: Nat; c != ZERO -> mul(c, a) = mul(c, b) -> a = b
...
```

### `2b4m query uses <file> [theorem]`
The **dependency audit** of a proof: per proof, the **rules/tactics** it invokes
(with counts) and the **external axioms/theorems/schemas** it cites (its own
step labels excluded). No theorem arg → every proof in the file. This answers
"**what does theorem X depend on?**" and, run over a file/corpus and filtered,
"**which proofs use `assoc` / this accelerated tactic / this lemma?**" — semantic and
alias-aware, where a multi-line `[by …]` and alias indirection defeat grep.

```
$ 2b4m query uses aata/3.2-groups.md invProduct
theorem invProduct
  rules: assoc axiom×2 forall_elim×4 rewrite×3 theorem modus_ponens symmetry forall_intro×2
  cites: inverseRight identityLeft inverseUnique
```

"Which proofs use `assoc`?" — `2b4m query uses <file> | grep -B1 'rules:.*assoc'`
(the query gets the semantics right; grep just filters its clean output).

### `2b4m debug taint <file> [theorem]` (NOT a query — under `debug`)
The **trust-entry audit**: per proof, every step whose rule is an **accelerated
tactic** (`arithmetic`, `tautology`, `polynomial`, `assoc_commut`, `assoc`, `ext`,
and their quantified variants), flagged at its `file:line:col`. These are the
steps that *could* accelerate (and do, under `--fast`, when they can't elaborate).
A clean report means the file's proofs are fully kernel-checked.
`simplify`/`simplify_quantified` never accelerate, so they are never flagged.
(It lives under `2b4m debug`, not `2b4m query` — see `2b4m debug accelerant` for the
companion "what did this accelerated step actually prove".)

```
$ 2b4m debug taint examples/peano.b4m
theorem twoPlusTwo
  examples/peano.b4m:192:9: arithmetic
...
$ 2b4m debug taint std/peano/divides.b4m
no accelerated tactics — every step is kernel-checked
```

## Typical workflow

Writing a proof and need a lemma:
1. `2b4m query search std <concept>` — find candidates by name/statement.
2. `2b4m query theorem <file> <name> --sig` — read its exact statement + binder
   order before citing it in a `forall_elim`.
3. `2b4m query whereis <myfile> <name>` — if it's aliased, see where it really
   lives (and confirm it's reachable from your file's scope).
4. `2b4m query outline <file> <similar-theorem>` — model your proof's structure
   on an existing one.

Auditing a proof or a file:
- `2b4m query uses <file> <theorem>` — what a proof leans on (before refactoring
  a lemma: who depends on it? run `uses` over the corpus and filter).
- `2b4m debug taint <file>` — is it fully kernel-checked, and if not, exactly
  which steps are the ones that accelerate, to make certificate-clean.

For plain text (counts, `^theorem`/`^axiom` listings, raw label greps), grep.
