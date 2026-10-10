---
paths:
  - "**/*.b4m"
  - "aata/**/*.md"
  - "examples/**/*.md"
---

# 2b4m cheat-sheet (dense)

The load-bearing mechanics + gotchas for writing `.b4m` proofs, in one page.
`GUIDE.md` is the comprehensive reference; this is the lookup you keep in head.
For depth on one thing, extract its GUIDE section (leaf sections are bounded by
the next heading of any level):

```
awk '/^#+ /{p=0} /^### RULE: common_conclusion$/{p=1} p' GUIDE.md      # a proof rule
awk '/^#+ /{p=0} /^### TACTIC: tautology$/{p=1} p' GUIDE.md  # an accelerant
awk '/^#+ /{p=0} /^### KEYWORD: sort$/{p=1} p' GUIDE.md      # a declaration keyword
```

Naming/label conventions are a SEPARATE doc — see `agents/style-guide.md`.

## Checking workflow (ITERATE FAST, CONFIRM STRICT)

While writing/fixing a proof, run **`2b4m check --fast <file>`** every iteration —
it trusts accelerated verdicts and skips kernel-certificate generation, so it's
much faster feedback for the write-check-fix loop. It gives you the same
pass/fail signal for your proof structure.

While iterating on ONE proof in a long file, add its name — **`2b4m check --fast <file>
<theorem>`** proves only that theorem and what it cites, so you are not waiting on the
file's other proofs (a wrong name, an axiom, or a schema is diagnosed).

Then, ONCE, before you declare the file done (and before it hits a gate), run
plain **`2b4m check <file>`** over the WHOLE file (strict — full kernel verification).
**`2b4m check <dir>`** checks every `.b4m` and `.md` under a directory in one pass
(a fact two files cite is proved once) and prints one aggregate line. This is the real
guarantee. A proof can pass `--fast` but FAIL strict (an accelerant couldn't
produce a kernel certificate) — the final strict pass catches that. A file is not
"done" until plain `2b4m check` is green with NO `NOT FULLY VERIFIED` banner.

(Flags: `--fast` trusts ALL `using` words; `--fast-only W…` only the listed;
`--fast-except W…` all but the listed; `--draft` allows `hole`s. `instantiation`
is never trustable. Use `--fast` for the loop; plain check to finalize.)

**`--axioms`** reports what a proof bottoms out in — every axiom it transitively
rests on, with the site each was declared at. It follows the demand graph, so it
sees what `query uses` cannot: axioms pulled in by an accelerant's certificate, an
`instantiation`, or a model transfer. A `hole` is an axiom to the kernel, so it is
listed and marked `— HOLE` (visible only under `--draft`, since default mode
rejects holes first). **`--library`** (on a directory) additionally FAILS on any
axiom declared there that no theorem there rests on — which is why `std/` carries a
`<namespace>/examples.b4m` per theory: a library demonstrates its own axioms rather
than leaving a caller to be the first to exercise one. If you add an axiom to
`std/`, add the example that uses it.

## THE AXIOMATIZATION RULE — write `hole` FIRST, always

**`axiom` is reserved for a result you can point to in the literature.** Everything else —
the source's own mathematics, your modelling decisions, your reconstructions of an argument,
anything you believe but cannot cite — is a `hole`.

**The habit that matters: a new declaration you cannot cite goes in as `hole` from the
start.** Not `axiom`-then-audit. The audit pass is where rationalization happens, and it is
reliably too weak to catch your own reasoning: a plausible name plus a confident comment
survives self-review almost every time. `hole` inverts the default — strict `check` refuses
the tree until the thing is proved or you find the actual citation, and there is no interval
in which a bogus axiom sits there looking settled.

Measured failure rate on exactly this (the openai-wiles formalization, 2026-10-09): applying
the test *after* writing axioms caught 4 of 29 as violations; the round that CLOSED those
holes introduced 5 new violations, 3 of them written during the round whose stated purpose
was applying the test. Self-audit does not converge. Writing `hole` first does.

### Closing a hole means PROVING it

Closing is **never** relabelling. These are all the same prohibited move:

- `hole X` → `axiom X` (the bare version)
- `hole X` → `axiom X2` where `X2` is `X` renamed, or `X` with a premise bolted on
- `hole X` → `theorem X` proved from `axiom Y` where `Y` is `X`'s content under a new name

A hole is closed when it is a `theorem` whose leaves are all genuine citations. Expect the
axiom count to **rise** when you do this honestly — one large assumption becomes several
small cited ones. A count that stays flat while holes vanish is the signature of relabelling.

### The four ways a bogus axiom disguises itself

All four were committed in one session, with confident comments on each:

1. **The swallow.** An axiom whose statement produces the goal's whole existential, named as
   if it were a lemma (`aCycleClassDecomposesIntoIntegralSubvarieties`). Test: does its
   conclusion look like what you set out to prove?
2. **The invented hypothesis.** A guard attributed to the source that the source does not
   state — found by reading a lemma's STATEMENT and never its PROOF, where the real
   conditions live. Cost here: a confident, published, wrong diagnosis.
3. **The textbook-sounding assumption about your own symbols.** "A group is cancellative",
   "projections are linear" — true of groups and projections, but the symbol in your file is
   an opaque `func` with no theory attached, so nothing makes it true. Test: is the structure
   the claim relies on actually declared?
4. **The restated argument.** You formalize a *determination* argument as a *vanishing*
   argument, or assert a ground equation where the source gives a per-index identity. It
   type-checks, it is not the source's reasoning. Test: can you map each axiom to a specific
   sentence, with its quantifiers intact?

### Verification hygiene

- **Never write "verified against the source" unless you read the source**, in this session,
  and can quote it. A false axiom with a confident comment checks green forever.
- **Axiomatize a reference from the REFERENCE, not from the paper citing it.** A convention
  mismatch between source and citer is invisible to a formalization built the other way — it
  inherits exactly the error it was meant to detect. "Does the paper quote [6] correctly" and
  "does [6]'s claim mean the same thing in the paper's convention" are different questions.
- **An orphaned proof is a silent failure.** If you prove a lemma and then `axiom` the
  conclusion it was meant to feed, the proof carries no weight and nothing reports it. Check
  that each theorem you prove is actually cited by something above it.
- **An UNCITED hole is invisible** (see the gotcha list). Delete dead stubs; don't leave them.
- `--axioms` is the deliverable, not the green checkmark. Read the statements it lists, not
  their names.

## STRATEGY: build DOWN from the goal, or UP from the primitives?

Both work. Picking wrong costs rework, so decide deliberately. The rule of thumb:

> **Bottom-up when the statement is GIVEN. Top-down when the statement is YOURS to invent.**

A textbook hands you its lemmas verbatim — transcribe those bottom-up, their shape is not
in question. The *plumbing between them* (what your loop body consumes, what your
induction hypothesis carries, what an internal helper must report) is yours to design,
and that is exactly where guessing an interface costs a rewrite.

**TOP-DOWN, with `hole` (see `### KEYWORD: hole` in GUIDE.md):**

1. State the goal as a `theorem` and every missing piece as a `hole`.
2. Write the goal's proof. `check --draft` — the checker names each unresolved
   reference, so it becomes your worklist. Stub each as another `hole`.
3. Discharge holes leaf-first, turning each into a `theorem`.
4. Plain `check` (no `--draft`) is the finish line: default mode REJECTS holes and prints
   each one with the theorems resting on it.

**What this buys you (measured on Judson's parity lemma, 2026-09-29):** the consumer
*settles* the interface instead of you guessing it. Two bottom-up attempts at a loop-body
statement were subtly wrong; written against the caller it was right immediately, and
turned out to need none of the letter/position/invariant parameters I had been threading.
Writing the ENDPOINT also exposed a missing invariant half that bottom-up had hidden — the
loop needed "entry j MOVES the letter", not just "entries above j fix it", because the
first alone is not contradictory at position 0.

**What it does NOT buy you:** the hard proof stays exactly as hard. Top-down makes you
right about interfaces sooner; it does not shrink the mountain.

**Costs, all real:**
- **A hole in `std/` poisons the library gate.** One hole anywhere under `std/` forces the
  whole `check std --library` sweep into `--draft`, blinding it to every other file. Keep
  hole-bearing scaffolds OUTSIDE the library (this repo uses `drafts/`), and move them in
  once filled. Bottom-up never pays this.
- **An UNCITED hole is invisible, not flagged.** Holes are disclosed by what *depends* on
  them, so a stub you never wire up is dead weight rather than a tracked to-do. Don't use
  holes as a task list; use them as load-bearing stubs.
- **You cannot stub mid-proof.** `hole` is a top-level declaration, never a step
  justification (`[by hole]` is a parse error). To sketch a proof with a gap, the gap must
  be its own NAMED hole with a fully written statement — which is most of the design work.

**Practical hybrid, and what I would do again:** transcribe the source's own lemmas
bottom-up; the moment you are inventing a signature, stop and write its consumer first.

## Proof skeleton

```2b4m
theorem foo: forall a: Nat; P(a)
proof
  @generalize-a |
    fix a: Nat {
      @some-fact | <formula> [by cite someAxiom]
      @conclusion-inner | P(a) [by ...]
    }
  @conclusion | forall a: Nat; P(a) [by generalize generalize-a]
qed
```

- Every step is `@label | <formula> [<keyword> <rule> <refs>]` (label, formula, justification — the formula and `[…]` indented two spaces under the label). Blocks nest two spaces.
- **TWO justification keywords**: `[by <rule> …]` for KERNEL PRIMITIVES (pure inference, always kernel-checked — the whole proof-rule table below); `[using <name> …]` for ACCELERANTS + `instantiation` + `model`/`import` (engine proof-generation). The parser ENFORCES the split: `by` on an accelerant, or `using` on a primitive, is a hard parse error. `--fast` can trust MOST `using` words (accelerants + `model`/`import`), but NOT `instantiation`: an instantiation's content is the schema body's proof at the args — the per-instance proof is the only soundness gate, so it is ALWAYS kernel-checked even under `--fast` (#93).
- A `fix x: S { … }` block generalizes; a SEPARATE `generalize <block-label>` step discharges it (the block is not itself the universal). Same for `assume F { … }` + `discharge`.
- Inside an `assume F { … }` block, restate the assumption with `[by hypothesis <block-label>]`. Inside a `fix h: H` (refined sort), get its guard `inH(h)` with `[by predicate <block-label>]`.
- Refs are SPACE-separated: `[by both a b]` NOT `a, b`.
- Term arguments go in parens on the rule: `[by apply_at(succ(b)) some-step]`.

## Proof rules — EXACT ref counts (the drift-prone part)

| rule | refs | notes |
|---|---|---|
| `cite NAME` | 0 (names a stmt) | kind-agnostic fact citation (cites an axiom OR a theorem; the kernel picks the arm by resolved kind). Must introduce a cited fact AS A STEP before a later `apply_at` references it — `@a \| forall …; … [by cite foo]` then `apply_at(t) a`. (`axiom`/`theorem` are no longer rule words.) |
| `hypothesis BLOCK` | 1 block | restate an enclosing assume/unpack assumption |
| `predicate FIXBLOCK` | 1 block | guard `inH(h)` of a refined `fix h: H` |
| `modus_ponens IMP ANT` | 2 | order: implication FIRST, antecedent second |
| `discharge BLOCK` | 1 block | discharge `assume` → implication |
| `generalize BLOCK` | 1 block | discharge `fix` → universal |
| `apply_at(t, …) STEP` | 1 step (+ term args) | multi-arg peels several binders in one step |
| `witness(t) STEP` | 1 step (+ witness term) | |
| `unpacked BLOCK` | 1 block | export an `unpack` block's witness-free conclusion |
| `both L R` | 2 | REJECTS a biconditional-shape goal `(X->Y) and (Y->X)` — use `make_equivalence` |
| `and_lhs STEP` / `and_rhs STEP` | 1 | |
| `make_equivalence FWD BWD` | 2 | forward `P->Q` then backward `Q->P`; goal must be `P iff Q` shape |
| `equiv_forward STEP` / `equiv_converse STEP` | 1 | recover `P->Q` / `Q->P` from `P iff Q` |
| `either_left STEP` / `either_right STEP` | 1 | |
| **`common_conclusion DISJ LBLOCK RBLOCK`** | **3 (1 step + 2 blocks)** | **BINARY only.** A 3-way split needs `case <disj> { … }` (see below), NOT a 3-ref common_conclusion |
| `contradiction BLOCK S1 S2` | 3 (1 block + 2 steps) | the block's assumption yielded contradiction S1/S2 |
| `ex_falso S1 S2` | 2 | from a contradiction, conclude anything |
| `double_negation STEP` | 1 | `not not P` → `P` |
| `reflexivity` | 0 | `t = t` |
| `symmetry STEP` | 1 | `x=y` → `y=x` |
| `rewrite EQ TARGET` | 2 | replace EQ's lhs by rhs (or rhs by lhs) in TARGET — **bidirectional**, no `symmetry` needed to reorient |
| `equiv_rewrite BICOND TARGET` | 2 | from `P iff Q`, replace sub-prop P by Q (or Q by P) in TARGET (any position). Bidirectional, kernel-checked, no taint |

(`instantiation`/`model` are NOT in this table — they are `using` accelerants, below.)

`case <disj-step> { @when-left| assume A { … } @when-right| assume B { … } }` — the 3-way (or N-way) disjunction eliminator. Use this instead of trying to give `common_conclusion` more than 2 arms.

## Formula syntax edges

- Connectives are WORDS: `and`, `or`, `not`, `->` (right-assoc), `iff` (lowest precedence). No `<->` symbol — it's the keyword `iff`.
- **Mixed boolean operators need explicit parens.** Same-op chains are fine (`a or b or c`, `a -> b -> c`); DIFFERENT ops must be parenthesized: `a and b or c` is a parse error → `(a and b) or c`. This includes `not` as an operand (`(not p) and q`, `a -> (not b)`) and `iff` (`(a and b) iff c`, `a -> (P iff Q)` — an iff under `->` needs parens).
- `=` / `!=` are term comparisons, NOT boolean ops — never need parens against a connective (`x = y and p` parses as `(x = y) and p`).
- Quantifier binders end with `;`: `forall a, b: Nat; …`, `exists w: Nat; …`.
- No infix minus, ever — write `sub(a, b)`.

## iff (surface sugar)

`P iff Q` desugars to `(P -> Q) and (Q -> P)`; the kernel never sees `iff`. Therefore:
- Prove with `make_equivalence fwd bwd`; eliminate with `equiv_forward` / `equiv_converse`.
- `tautology` DECIDES `iff` goals and CONSUMES `iff` hypotheses for free (it sees the desugared conjunction).
- `equiv_rewrite BICOND TARGET` substitutes P↔Q across a goal (subformula congruence).
- The shape `(X -> Y) and (Y -> X)` is CANONICALLY an iff: `both` refuses it (use `make_equivalence`), `make_equivalence` requires it. So write biconditionals as `iff`, not hand-rolled conjunctions.

## Accelerants (tactics) — cited with `using`, NOT `by` — one-liners; detail at `### TACTIC: <name>` in GUIDE.md

All of these take the `using` keyword: `[using simplify …]`, `[using specialize HEAD(args) …]`,
`[using instantiation NAME(args) refs…]` (monomorphize a schema; refs discharge its leading
antecedents), `[using model(M) src.thm]` (transfer a source theorem through model M),
`[using import(I) thm]` (cite a fact — axiom or theorem — from import I's file — the PREFERRED cross-file
citation; `[by cite I.thm]` is the same effect but a plain re-checked obligation. Use
`import(I)` across a file boundary, `by cite` for a same-file fact).

- `simplify` — equational rewriting to a shared normal form (always emits kernel steps).
- `assoc_commut` / `assoc_commut_quantified` — reorder an A/C sum; bare = add/mul, `(assoc,comm,swap)` for a custom op; `_quantified` peels a `forall` prefix.
- `assoc(assocLemma)` — associativity-ONLY equality (required lemma arg; no commutativity).
- `polynomial(theory)` — nonlinear `add`/`mul` identity by canonical expansion. In a **ring theory** (`neg`/`sub` in scope) it also expands `sub`/`neg`, cancels inverses (`t+neg(t)→0`), and folds numeral coefficients by expansion (`2q+2q=4q`, `(2q+1)²=4q²+4q+1`); pure-ℕ (`peano`) unaffected.
- `specialize HEAD(args) hyps…` — apply a `forall`-quantified fact in one step (∀-elim at args + modus_ponens each hyp; emits the kernel chain). `HEAD` may be a declared THEOREM/AXIOM name **or a LOCAL STEP LABEL** (a `forall`-shaped assumed/derived step) — no need to hand-roll `apply_at`+`modus_ponens` for a local universal.
- `ext` — extensionality reduction (sets/functions) → propositional residue.
- `tautology refs…` — propositional consequence (decides iff goals; consumes iff/`and`/`or`/`->` hyps). Atom cap 16. **Every non-propositional subformula is an OPAQUE ATOM** — see the gotcha below.
- `arithmetic refs…` — linear arithmetic over Nat (Presburger). `arithmetic(module)` / `fallback(thm)` variants. `fallback(thm)` cites a proven theorem for a decide-but-can't-certify goal; the goal may be `thm` VERBATIM or a SPECIALIZED INSTANCE (the matcher infers the ∀-witnesses and discharges `thm`'s `->` antecedents from the step's refs, emitting a kernel-checked apply_at+mp chain).
- **Inputs are NAMED; guard obligations are FOUND.** The list after a tactic is exactly
  what the inference consumes — `[using <tactic> <args>(…) input1 input2 …]`: the hyps
  `specialize` modus-ponenses (in the cited lemma's antecedent order), `chain`'s equations
  (in the order they must meet), `simplify`'s rewrites / `tautology`'s premises /
  `arithmetic`'s facts (a SET — order carries nothing). A tactic never searches for these.
  What it DOES search for is a guard obligation a written term owes — a `requires` guard
  (`div(a,b)` owes `b != ZERO`), or a refined-sort qualifier (applying `forall f: Perm` at a
  plain `Fn` owes `invertible(f)`) — met from `fix`-block guards, enclosing `assume`
  hypotheses, or proved steps in scope. Never name those; an undischargeable one is an
  `unproved obligation` error. Detail: `### WHAT A TACTIC IS GIVEN vs WHAT IT FINDS` in GUIDE.md.
- Discipline: in `std/*.b4m` use accelerants freely (shortest kernel-checked proof). In `aata/*.md` do NOT accelerate a step Judson spells out — transcribe it; accelerants only for algebra the book elides. (See `.claude/rules/aata-guide.md`.)

## DEFINITION BLOCKS — a declaration may carry its defining clauses

A `pred`/`func` declaration followed by `:` takes the clauses that characterize
it, `;`-separated. Each clause is written EXACTLY as the axiom it becomes.

```2b4m
pred isZero(n: Nat):
  isZero(n) iff n = ZERO          // a predicate: one clause, writes its connective

func add(a: Nat, b: Nat) => Nat:
  add(ZERO, b) = b;               // a function: one clause per case
  add(succ(k), b) = succ(add(k, b))

func gcd(a: Nat, b: Nat) => Nat:  // guards when the heads don't distinguish
  gcd(a, b) = a                  when b = ZERO;
  gcd(a, b) = gcd(b, mod(a, b))  when b != ZERO
```

- **Every clause states its own condition IN FULL.** Clauses are not ordered and
  there is no first-match-wins: each is a standalone axiom, and axioms have no
  precedence. Overlapping clauses that disagree are inconsistent, unchecked.
- **Cite with `by definition`** — `[by definition isZero]` for a predicate,
  `[by definition(0) add]` for a function clause (ZERO-indexed).
- **It is SUGAR.** `pred p(x: T)` + a separately-named `axiom` means the same
  thing; only the axiom's name differs (and so `by cite thatName` cites it).
- **NOT `define`.** A `define` is a macro — substituted before anything looks at
  it, invisible to the kernel, so it cannot be cited, model-mapped, or named
  where a symbol is required. A definition block declares a REAL symbol.
- `--axioms` marks a clause `— DEFINITION` rather than listing it beside genuine
  assumptions; `--library` still fails on an unused one, naming it a definition.

## Declaration keywords — one-liners; detail at `### KEYWORD: <name>` in GUIDE.md

`sort` (a type; `sort H = G where inH` is a refined subsort; `where inH and inK` conjoins guards), `const` (0-ary), `func` (returns a term-sort, never Prop — RESULT SORT AFTER `=>`: `func f(a: T) => U`), `pred` (opaque predicate; ALWAYS writes its parens — a nullary one is `pred q()`, used/parameterized/passed as `q()`, never bare; a nullary `func` stays bare, being `const`-shaped), `axiom`, `theorem`, `hole` (aspirational placeholder — a top-level DECLARATION, NOT a `[by hole]` step; default rejects, `--draft` allows), `intheory <name>` (forward-declare a theorem — "in theory it holds; you owe the proof later"), `import X <<< "path"`, aliases (`sort A = X.B`, `func f = X.g`; a FACT re-export is always `fact T = X.t` — one keyword whatever the target's kind, since an alias cannot know it and `--axioms` reports the origin's true kind anyway. `axiom T = X.t` / `theorem T = X.t` are hard errors, and `fact` has no local form), `model NAME { src: tgt … ; srcAxiom <- localFact … }` (interpret an abstract theory's primitives with `:` + discharge its axioms with `<-`, so its theorems transfer; cite `[using model(NAME) src.thm]`. `:` on an axiom or `<-` on a symbol is a hard error; a source theorem isn't mappable; `@`-projection is `<-`-only). GUARDED model (sort mapped onto `G where inH`): NOMINATE membership dischargers on the `:` map — a CONST `src.C: TGT(baseFact…)` (parens; one ground fact per guard pred), a FUNC `src.op: F -| closureFact…` (`-|`; closure preserves membership). Transferred theorems relativize (`inH(x) ->` per binder); an unconditional axiom mapped to itself auto-weakens.

## `import` and `model` — unlearn the Python prior (these are two different axes)

A recurring wrong assumption, imported from Python, is that `import` dumps names into your namespace and that `model` is some flavor of import. Neither is true.

- **`import` is LIKE a Zig import, not a Python one.** `import peano <<< "std/peano.b4m"` binds a namespace VALUE (the mental model is `const peano = @import("...")`, not `from peano import *`). You reach members fully-qualified: `peano.mulAddDistribLeft`. There is NO bulk open, no bare re-export. Importing `field` never gives you a bare `mulAddDistribLeft` in scope; only `field.mulAddDistribLeft`. To get a bare local name you must ALIAS (`func add = field.add`) or DECLARE a local theorem.
- **`model` is NOT `import` — it is structure interpretation.** A `model` maps an abstract theory's symbols to YOUR local symbols and discharges its axioms; in return its THEOREMS become true of your symbols and citable via `[using model(NAME) src.thm]`. It does **not** put any name into your scope. The theorem is a fact about your symbols; it has no bare local name until you write one.
- **Consequence — the shim idiom.** When an accelerant (`polynomial(myTheory)`, `arithmetic`) resolves a lemma by BARE name in your file's scope (self-theory), a model-transferred fact won't resolve — it has no bare name. Bridge the two axes with a one-line SHIM theorem: `theorem barelyNamedLemma: <stmt in your symbols> [using model(NAME) src.thm]` (a THEOREM with a proof, not a `fact` — `fact` only re-exports an existing name). Every model-based concrete sort (e.g. ℚ/ℝ/ℂ modeling `field`) pays this shim cost to use bare-name accelerants; the aliased case does not. This is the price of the model system, not a bug.

## Gotchas that bite (memorize)

- **`fix` takes ONE binder.** `fix a, b: Nat {` is a PARSE ERROR — nest them: `fix a: Nat { fix b: Nat { … } }`, discharging with one `generalize` per level (inner discharges `forall b; …`, outer `forall a, b; …`).
- **Literate `.md` fence discipline**: 2b4m code lives in ` ```2b4m … ``` ` blocks; every block must be CLOSED before prose. A missing/misplaced ``` fence makes the checker try to parse prose as 2b4m ("expected a declaration, got 'The'"). When inserting a new theorem in an `.md`, keep it inside one fenced block (or open+close its own).
- **Gates don't pin counts**: `tests/test_*.zig` uses `ctx.okSilent(&.{"check", FILE})` (asserts "checks OK, exit 0") — NOT a `"OK: N declarations, …"` golden. So an edit that changes decl/theorem counts needs NO gate update; just make sure the file still checks. (A few `--fast`/accelerated gates keep a full banner golden with counts — leave those.) Run `2b4m fmt <file>` before `fmt --check` gates.
- `[by hole]` is INVALID — `hole` is a top-level declaration, not a justification. Every obligation must really be proved (or the theorem itself is a `hole`).
- **When `hole` is OK**: for RESEARCH / EXPLORATION (spiking a new construction, sketching a skeleton before filling details) `hole` is a legitimate "assume for now, come back" placeholder. For WELL-KNOWN proofs — the AATA transliterations, std lemmas, anything where the proof is known and the job is to transcribe it — do NOT use `hole`: a hole there is unfinished work dressed up as done. Finish the proof.
- **`tautology` sees ATOMS, not their content.** An equation and a disequation are two
  unrelated atoms: `power(g,m) = g` + `g != E` does NOT give `power(g,m) != E` (it prints a
  countermodel setting all three independently). A `forall` is one atom, so it yields no
  instance. Fix: do the non-propositional step yourself (assume the negation, `chain` to
  the contradiction, `discharge`), then let `tautology` close it. If the countermodel
  names atoms you believe are linked, that link is the step you still owe.
- `common_conclusion` is BINARY. 3-way → `case`.
- Cite a theorem/axiom as a `[by cite X]` STEP before a later `apply_at` refs that step.
- No `<->`; use `iff`. No `<->`-style iff intro/elim beyond `make_equivalence`/`equiv_forward`/`equiv_converse`.
- A `func` cannot return `Prop` and cannot take a `-> Prop` parameter; predicates are opaque (no body).
- No variable shadowing (checker-enforced). When generalizing a statement binder, reuse the statement's binder name.
- A declarations-only file (no `theorem`s) checks with an informational note + exit 0 — that's fine, it's a dependency. A file that declares theorems but a proof fails is a hard error.
