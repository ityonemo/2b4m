# bpa

A proof checker written in Zig. It consumes `.bpa` files containing
declarations and proofs, verifies every step, and reports either a summary
line or precise `file:line:col` diagnostics.

The language design optimizes for clarity under constrained (human and llm)
context: proofs are explicit named steps, every name is greppable, diagnostics are
copy-pasteable surface syntax, and checking is fully deterministic.

## Design

**Explicit.** A proof is a sequence of named steps; every step states its
formula in full and names the rule and references that justify it. There is
no proof search, no hidden state, and no implicit context: what you read is
exactly what the checker checks. Where automation exists, it is a rule you
invoke explicitly, and its work is either replayed as ordinary checked
steps or disclosed.

**Optimized for LLMs and humans alike.** Both audiences read the same
surface: names are greppable (`bpa query uses` lists every fact a proof cites),
diagnostics re-parse verbatim as source, connectives are words rather than
symbol soup, and libraries of schematic statements cost nothing until used
— so context stays small and feedback stays precise. Layout is generous on
purpose; the tokens are thinking room.

**Inspired by Zig.** Beyond being the implementation language, the core
idea is borrowed from Zig's `comptime`:

```
axiom induction(prop: Nat -> Prop):
  prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)
```

behaves like `fn List(comptime T: type)`: in the case of bpa it is a **stored
form**, not a theorem. It does nothing until instantiated with a concrete,
written-out argument, at which point it is monomorphized into plain
first-order logic.  A theorem schema's proof is re-checked at each
instance, just as Zig re-analyzes a generic function per instantiation.

**Why schematics instead of higher-order logic.** Quantifying over
predicates is what makes proof assistants heavy: higher-order unification,
undecidable matching, large trusted cores. But almost every practical use
of that power is *instantiating* a general rule with a predicate you
supply. bpa keeps exactly that half: schemas are instantiated only with
formulas you have actually written down, so instantiation is decidable
substitution rather than search, no quantifier over predicates ever exists
in the object logic, and the trusted kernel stays a small body of concrete
first-order checking.

**Mistakes fail loud, never silent.** You can still write a *bad proof* —
an awkward detour, a cited step that doesn't apply, a tactic pointed at the
wrong goal. What you cannot do is have such a mistake yield a false theorem.
The worst case for a usage footgun is a located `file:line:col` error, not a
wrongly-accepted result. This is a structural property, not a promise of
care: the kernel re-derives every rule application itself and trusts nothing
the elaborator, parser, or a tactic asserts. There are exactly two claims
the kernel accepts without re-deriving — a schema *instance* (and it still
checks the premise-matching) and a named *accelerated* verdict — and both are
made visible rather than hidden: an accelerated step marks its theorem accelerated, the summary
line discloses it, and by default `bpa check` rejects it outright (only the
opt-in `--fast` accepts an accelerated verdict). Ambiguity is
squeezed out of the surface for the same reason: `:` is only ever sort
ascription, `|` only ever a step label, connectives are words not symbols,
and no-shadowing is enforced — so a proof reads one way, and the way it
reads is the way it is checked.

## Quick start

```
zig build
./zig-out/bin/bpa check examples/peano.bpa
```

```
OK: 18 declarations, 6 theorems proven (1 accelerated: arithmetic)
```

A proof is a sequence of labeled steps, each justified by a rule:

```
sort Nat
const ZERO: Nat
func succ(n: Nat): Nat
func add(a: Nat, b: Nat): Nat
axiom addZeroLeft: forall b: Nat; add(ZERO, b) = b
axiom addSuccLeft: forall a, b: Nat; add(succ(a), b) = succ(add(a, b))

define TWO = succ(succ(ZERO))
define FOUR = succ(succ(TWO))

theorem twoPlusTwo: add(TWO, TWO) = FOUR
proof
  @conclusion |
    add(TWO, TWO) = FOUR
    [using arithmetic]
qed
```

Failures are located and exact:

```
$ ./zig-out/bin/bpa check examples/incorrect.bpa
examples/incorrect.bpa:39:41: error: modus_ponens: expected antecedent 'raining', got 'wet'
```

## Commands

```
bpa check [--fast | --fast-only W… | --fast-except W…] [--axioms] [--library] <file.bpa | file.md | dir> [theorem]
bpa fmt [--check] <file.bpa>
bpa lint <file.bpa | file.md>
bpa debug accelerant <file> <line | theorem step-label>
bpa query outline  <file> [theorem]
bpa query theorem  <file> <name> [--sig]
bpa query whereis  <file> <identifier>
bpa query search   <file|dir> <query>
```

`check` verifies a file and everything it imports. By default it verifies
everything; `--fast` defers per-`using`-word verification during development
and says so loudly (`--fast` trusts all `using` words, `--fast-only W…` only
the listed words, `--fast-except W…` all but the listed). Re-run plain
`bpa check` to finalize. `fmt` normalizes whitespace and indentation in place
(`--check` reports instead of rewriting). `lint` reports convention violations `check`
ignores because they don't affect validity — currently canonical binder order
(a leading `forall` must bind in first-appearance order); see `CONVENTIONS.md`.

### Literate proofs (`.md`)

`check` also runs on **Markdown**: give it a `.md` file and it verifies the
proofs inside ` ```bpa ` fenced code blocks, ignoring the prose. All the code
blocks in a document share one scope (a later block may cite a theorem from an
earlier one), and errors report the line number **in the `.md` itself** — so a
literate proof document is a first-class, checkable artifact. See
`examples/literate.md`.

```
$ bpa check examples/literate.md
OK: 6 declarations, 1 theorems proven
```

The `bpa query` commands (below) also understand `.md` — they extract the same
`bpa` blocks — so you can outline, look up, or search proofs written literately.

### Query (read-only inspection)

For most simple searches (label audits, tactic-usage sites, counts), using `grep`
or similar is encouraged!

`bpa query` navigates a proof corpus without checking it — for the cases plain
text searching, especially `grep`, handles poorly: a proof's *structure*, a
theorem's *exact statement* (which may wrap across lines), *following an alias
across files*, or *finding a lemma by concept* when the name is fuzzy.

- `query outline <file> [theorem]` — the proof **skeleton** (one line per step,
  with headers on `fix`/`assume`/`unpack`/`case`).
- `query theorem <file> <name> [--sig]` — a declaration's full source, aliases
  followed to the origin; `--sig` prints just the one-line statement (handy for
  reading binder order before a `forall_elim`).
- `query whereis <file> <identifier>` — trace an identifier through every
  alias/import hop to its **origin**.
- `query search <file|dir> <query>` — fuzzy-search theorem/axiom names +
  statements (a directory searches the whole corpus; a file searches its
  transitive-import scope).
- `query uses <file> [theorem]` — the **dependency audit**: per proof, the
  rules/tactics it invokes (with counts) and the axioms/theorems/schemas it
  cites (its own step labels excluded). Answers "which proofs use `assoc`?" and
  "what does theorem X depend on?" — semantic and alias-aware, where a
  multi-line `[by …]` defeats `grep`.

(The **acceleration audit** — where trust enters a proof — is `bpa debug taint`,
below, not a query.)

Query may support semantic searching in the future.

### Debug (see what an accelerant proved)

An accelerated tactic like `[using simplify …]` or `[using arithmetic]` stands in for a
chunk of proof the tactic generates and the kernel checks. In default (strict)
mode that generated proof is a real, suppressed **synthetic theorem** — nothing is
trusted, everything is kernel-checked. `bpa debug accelerant` reprints it, as the
bpa a person would have written:

```
$ bpa debug accelerant tests/cases/farkas.bpa belowBothWaysIsAbsurd conclusion
theorem arithmetic: forall a: Nat; forall b: Nat; less_than(a, b) -> less_than(b, a) -> less_than(a, a)
proof
  @b2 |
    fix a: Nat {
    ...
      @s8 |
        less_than(a, a)
        [by modus_ponens s7 s2]
    ...
qed
```

Point it at a step by line number (`… <file> 23`) or by enclosing theorem + step
label (`… <file> <theorem> <label>`). The output is valid bpa — fed back through
`bpa check` it re-verifies from scratch. Useful for reviewing exactly what a
tactic discharged, and (as the underlying named-theorem chain) the export IR for a
future Lean/Isabelle/Rocq backend.

`bpa debug taint <file> [theorem]` is the companion audit: per proof, every step
whose rule can fall back to an accelerated verdict (`arithmetic`, `tautology`,
`polynomial`, `assoc_commut`, `assoc`, `extensionality`, and their quantified variants),
flagged at its `file:line:col` — *where trust enters the proof*. A clean report
means every step is kernel-checked.

## How it works

- A **tiny trusted kernel** checks concrete first-order logic: every proof
  step names a rule and the steps it depends on, and the kernel verifies
  each one. Everything outside the kernel — parsing, name resolution,
  tactics — is untrusted machinery that can only ever *prepare* work for
  it.
- **Schematic statements** are stored forms, monomorphized per
  instantiation (see Design above); the kernel only ever sees the concrete
  first-order instances.
- **Automation is certificate-first.** The `simplify`, `tautology`, and
  `arithmetic` rules discharge goals in one step. Whenever possible they
  emit ordinary kernel steps (a *certificate*), so the result is exactly as
  trustworthy as a hand proof. When a decidable goal falls outside the
  certificate fragment, checking fails with a located error by default; the
  opt-in `--fast` flag instead lets a built-in decision procedure (an
  *accelerated tactic*) accept the goal, marks the theorem, and discloses it on the
  summary line. In other words, the default is certificate-or-error; accelerated
  verdicts are never accepted unless you ask for `--fast`.
- **Imports** (`import peano <<< "std/peano.bpa"`) bring in namespaced
  declarations. A cross-file citation is an `import` `using` step; under
  `--fast` (or `--fast-only import`) that step is *admitted* — accepted by
  matching the cited statement rather than re-deriving it — and the summary
  announces it. (A demanded imported theorem is still re-checked in its own
  file: trust admits the citation, not the imported proof's content.)

## Compared to other proof assistants

bpa is young and deliberately narrow; the mature systems below are vastly
more capable and have decades of libraries. These sections are about
*design differences*, not a claim that bpa competes on power. The recurring
theme: bpa trades expressive foundations for a tiny kernel, decidable
elaboration, and an explicit surface — a trade that suits a proof *checker*
whose proofs are written to be read (by humans and LLMs) and grepped.

bpa is designed to rule these footguns out by construction. Each is a genuine
trade-off the mature systems made knowingly, for good reasons — but we think
it's better not to have them at all.

One footgun is shared by all three, so it goes here: **division (and other
partial functions) is made *total* by fiat.** Lean, Isabelle/HOL, and Rocq
all define `n / 0 = 0` (and `head []`, etc.) so the term is well-typed —
which means `n / 0` silently denotes a meaningless value and a proof can pass
through it without anyone noticing the degenerate case. bpa instead guards
such functions (`func div(a, b) requires b != ZERO`), turning every use into
a proof obligation: you must *prove* the divisor is nonzero, or the check
fails with a located error. The cost is that you carry the obligation; the
benefit is that the `n / 0` case cannot silently slip into a proof.

In general, bpa inverts the usual relationship with accelerated tactics:

- **Certificate-by-default.** `by arithmetic` *produces a full kernel-checked
  proof* whenever it can, and the default mode is certificate-or-error — a
  goal it cannot certify is a located error, never a silently trusted step.
  The linear fragment is certificated, including a **Farkas certificate** for
  linear infeasibility (a fixed no-search recipe), so the bulk of arithmetic
  goals check with every step kernel-checked and no accelerated step at all.
- **A loud, opt-in fast mode for development.** The `--fast` flag *skips*
  certificate generation and takes the accelerated verdict, for quick iteration
  while a proof is still being worked out.

Anything that bpa trusts beyond the kernel is **named, transitively propagated,
printed on every summary line, and rejected by default**.

### Lean vs bpa

Lean is a dependently-typed proof assistant and a full programming language
(the Calculus of Inductive Constructions; proofs *are* programs). It is vastly
more expressive than bpa's many-sorted first-order logic. For example, in Lean
you can index a type by a value, which bpa cannot, at the cost of a kernel that
implements definitional equality, universe checking, and inductive families. That
Lean is a full programming language makes it harder to reason about without deeper
knowledge of the underlying language; bpa is on the surface easier to reason about
at the expense of having longer proofs. This tradeoff is taken for two reasons:

- modulo context windows, LLMs seem to have more patience walking through steppy
  problems

- simplifying human review to a less specialized (more general-math) audience is
  desirable.

*The footgun:* `native_decide` expands the trust surface silently, to include
the compiler and FFI, both places where bugs have been found that enable deriving
`False`.  These are only visible via `#print axioms`, versus bpa, which always
discloses accelerated-tactic use.

### Isabelle/HOL vs bpa

Isabelle/HOL is higher-order logic under the **LCF architecture**: theorems are
an abstract type only the small kernel can mint, so even `sledgehammer` and the
classical reasoner factor through kernel inferences. bpa shares the tiny-trusted-core
instinct — its certificate-first tactics replay as kernel steps the same way —
but is first-order (the schema mechanism covers only *instantiation*, not real
quantification over predicates).

*The footgun:* the `eval` method / `value` prove by emitting ML, compiling, and
running it — expanding the trust surface to the code generator, the ML compiler,
and the runtime, outside the LCF kernel. bpa's accelerated tactic is the same shape, but
rejected in the default mode and disclosed under `--fast` rather than trusted silently.

### Rocq (Coq) vs bpa

Rocq, like Lean, is founded on the Calculus of Inductive Constructions with
dependent types and proofs-as-programs (and pioneered much of that tradition —
`Ltac`, extraction, CompCert). Its `Ltac` is a Turing-complete *untrusted*
metaprogramming layer emitting proof terms the kernel re-checks; bpa's tactics
fill the same role but are fixed built-ins, not a metalanguage.

*The footgun:* `native_compute` (to OCaml) and `vm_compute` (a bytecode VM)
close goals by computation, folding the compiler or VM into the trusted base —
discoverable only via `Print Assumptions`. bpa's accelerated tactics are the analogue, but
disclosed and `--fast`-gated, so the trusted surface is always disclosed.

## Layout

| Path | Contents |
|---|---|
| `examples/peano.bpa` | the living demo: automation-assisted Peano arithmetic |
| `examples/peano-pure.bpa` | the same theory proved entirely by hand |
| `examples/gauss.bpa` | Gauss's summation formula (with the `assoc_commut` tactic) |
| `examples/euclid.bpa` | Euclid's gcd, consuming the verified `std/peano-divides` library |
| `examples/euclid-compute.bpa` | gcd *run* on concrete numbers: `gcd(9, 6) = 3`, unfolded step by step |
| `examples/incorrect.bpa` | three classic wrong proofs and their diagnostics |
| `examples/sqrt2.bpa` | **√2 is irrational** (stated over ℕ), proven |
| `examples/literate.md` | a **literate** proof: prose + checkable ` ```bpa ` blocks |
| `std/` | the standard library: arithmetic (`peano`), order + strong induction (`peano-order`), subtraction, the verified divisibility/division/gcd unit (`peano-divides`), even/odd + the parity crux (`peano-parity`), abstract group theory (`group`), set algebra over a universe (`set`), and the theory of mappings (`function`) |
| `aata/` | **literate transliterations of an abstract-algebra textbook** (Judson's AATA, GFDL) verified in bpa — the book's prose reproduced in order, each stated result followed by a checked proof; see `aata/README` |
| `agents/` | agent-facing assets, symlinked into `.claude/`: `bpa-query-skill/` (a Skill teaching when to reach for `bpa query` over `grep`) and `style-guide.md` (a path-scoped `.claude/rules/` file surfacing the drift-prone proof-label conventions freshly when a `.bpa`/proof `.md` is edited — the on-demand companion to `CONVENTIONS.md`) |
| `tests/` | the integration suite: `zig build test` spawns the built `bpa` on each corpus file and asserts its exact stdout/stderr/exit. Gates live in subject-grouped `tests/test_*.zig` (cli, tactics, std, aata, examples, query, imports), each a one-line `ctx.ok`/`ctx.fail` (see `tests/Ctx.zig`); `build.zig` stays build configuration |
| `GUIDE.md` | every keyword, the kernel design, the built-in accelerated tactics |
| `CONVENTIONS.md` | naming and proof-writing style |
| `ACCELERATION.md` | the accelerated-tactic registry and trust disclosure |
