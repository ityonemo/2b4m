# 2b4m proof-writing conventions

These conventions optimize for the two audiences of a `.b4m` file: an LLM
writing it and a human reviewing it. Most are style (normalized by the planned
`2b4m fmt`); a few are checker-enforced where noted. `examples/pa.b4m` is the
living exemplar.

## File layout

Order: header comment → imports → aliases → sorts → constants → functions →
predicates → axioms → theorems. Separate the groups with blank lines; in
larger files, use section comments (`// -- axioms ----`).

**A theory and its sub-theories.** A theory that grows past one file becomes a
parent `std/X.b4m` beside a directory `std/X/` holding its sub-theories
(`std/integer.b4m` + `std/integer/order.b4m`, `std/integer/divides.b4m`, …). The
parent ends with a commented `// THEORY OF X` section that FORWARDS its
sub-theories' results by alias (`theorem gcdGreatest = divides_theory.gcdGreatest`),
grouped with the `intheory` block: `intheory` promises a fact proved later in this
file, a forward is that promise kept in another. A consumer then writes `import
integer` and reaches the order, the division algorithm and gcd without knowing
which file proved which.

Forward the **takeaway results** — what someone reasoning about the theory reaches
for. A lemma does not belong in the forwarding section any more than it belongs in
`intheory`; a consumer that genuinely wants one keeps the honest
`import integer/order`.

**Name an import after its PATH, with `/` written `_`**: `std/function/invertible.b4m`
is imported as `function_invertible`, `std/integer/divides.b4m` as
`integer_divides`, `std/peano.b4m` as `peano`. The name is then mechanical — you
can write it without opening the file, and a reader recovers the path from the
name.

The reason is not tidiness. An import binds a **namespace** in the same
declaration space as every sort, constant, function and predicate, so a theory
named after its subject collides with the subject itself: `import invertible <<<
"std/function/invertible.b4m"` beside the natural alias `pred invertible =
function.invertible` is a hard `duplicate declaration` error — and, because the
name then resolves to the namespace, it is followed by unrelated-looking errors
at every *use* of the predicate (`'invertible' is not callable`). Deriving the
name from the path sidesteps the whole class: a path-shaped name is never the
name of a symbol the theory declares.

A `-` in a path becomes `_` as well (`std/integer/mod-n.b4m` →
`integer_mod_n`), since a hyphen is not an identifier character. Where a name
would be intolerably long, shorten from the FRONT — drop leading path segments
the context makes obvious (`function_invertible`, not `std_function_invertible`)
— never from the back, which is the part that identifies the theory.

A **parenthesized parameter list makes a statement schematic** (a comptime
form, instantiated per concrete argument): `axiom induction(prop: Nat -> Prop):
...` is an assumption family; `theorem contrapositive(p: Prop, q: Prop): ...
proof ... qed` is a proven family whose proof is re-checked at every
instantiation. The keyword carries the epistemic status either way — an axiom
never has a proof, a theorem always does. Libraries exporting schematic
theorems should ship a smoke file instantiating each one (schemas are never
checked at declaration, only at use).

**A library demonstrates its own axioms.** The same reasoning generalizes past
schemas: an axiom no derivation ever rests on is one whose binders, guards and
direction have never been checked, and "a caller will exercise it" is not the
library's to assume. So each theory that states axioms nothing else in the
library consumes ships a `std/<namespace>/examples.b4m` — one file per
top-level namespace (`std/integer/examples.b4m` covers `integer/divides`,
`integer/mod-n` and `integer/product`), each theorem the smallest derivation
that genuinely needs the axiom it names. `2b4m check <dir> --library` enforces
this: it fails on any axiom declared in the directory that no theorem there
rests on. Prefer arguments that give every clause content — an existence axiom
exercised only at zero leaves its index arithmetic untested.

The header comment states what the file is and what it proves.

## Literate `.md` structure — introduce components as the prose reaches them

The front-loaded layout above is for `.b4m` files. A literate `.md`
transliteration (`aata/*.md`) does **not** ape it. Prose is the spine; the
```2b4m fence blocks are woven into it, and each component is introduced **where
it belongs in the exposition** — imports, aliases, and declarations sit at the
top of the fence block that *first needs* them, not hoisted into one preamble
block at the top of the file. The reader should never meet a name before the
text has introduced it.

This is sound because the literate checker concatenates every ```2b4m block into
one logical file **in document order, sharing one scope** (`src/literate.zig`) —
so document order = declaration order (declare-before-use, reading downward), and
an import in one section's block is visible to every later block. There is no
per-block preamble tax.

In practice: the *core vocabulary the whole chapter is about* (the underlying sort +
its operations — `Int`/`add`/`mul`, `Grp`/`op`, `Set`/`member`) is introduced
once, with the opening prose that first names the object (the book opens the same
way). *Concept-specific machinery* enters in the section that first discusses that
concept — the reader meets `does_divide` when the text reaches divisibility, `gcd`
when it reaches the Euclidean algorithm, the subgroup predicate when subgroups are
defined. A single-theory chapter (one import used throughout) naturally satisfies
this by introducing its one import with the opening prose; a multi-concept chapter
scatters its imports across the sections that motivate them. The test is "does
this read most naturally as exposition" — not a mechanical rule. (This overrides
nothing in `agents/style-guide.md`'s transcription exception, which still governs
*naming* inside a literate file — alias to the book's notation.)

## The forward manifest

An optional block of `forward <name>` lines after the axioms declares, up
front, which theorems the file will prove — a table of contents the checker
verifies (each name must be defined in this file as a theorem, plain or
schematic; nothing else is checked).  This exists for organizational purposes,
because theorem bodies can get quite large, and can signal that a particular
theorem is expected to be imported, however, note that this is not a promise.

```
// -- forwarded theorems ----
intheory addZeroRight
intheory addIsCommutative
```

## Comments carry the "why"

These comments are not required, they are just a helpful guide for humans
and LLMs to understand the context of what is followed.  Expect an LLM to
be able to be prompted with a preceding comment block and be able to scan
the theorem to assess if it's correct.

- Every theorem is preceded by a **strategy comment**: the proof idea in one or
  two lines (e.g. `// Strategy: induction on b with prop(k) := forall a. ...`).
  A reviewer — or a future session with a cold context — should never have to
  reverse-engineer intent from the steps.
- Inside proofs, **phase comments** mark the structure: `// base case: ...`,
  `// inductive step: ...`.
- Comments explain *why*; steps state *what*. Don't paraphrase a step in its
  comment.
- Statement-level quirks get a comment (e.g. why a quantifier order was chosen).

## Naming

Every category has a distinct look:

| Category                | Style           | Example                        |
|-------------------------|-----------------|--------------------------------|
| Sorts                   | ProudCamelCase  | `Nat`, `Prop`, `Word32`        |
| Constants               | ALLCAPS         | `ZERO`, `ONE`, `E` (identity)  |
| Functions / predicates  | snake_case word | `succ`, `add`, `even`          |
| Axioms/theorems         | camelCase       | `addZeroLeft`, `induction`     |
| Labels                  | kebab-case      | `induction-step`, `given-inductive-hypothesis`   |
| Variables               | snake_case      | `a`, `k`, `high_word`          |

- Functions and predicates should not be **one letter**: `succ` not `S`. The same
  applies to schema parameters (`prop: Nat -> Prop`, not `P`) — they are
  function-shaped.
- **Named mathematical constants keep their conventional lowercase spelling**:
  the circle constant `pi`, Euler's number `e`, and the imaginary unit `i` are
  written **lowercase**, not `PI`/`E`/`I` — their standard notation *is*
  lowercase, and forcing ALLCAPS reads wrong (`i*i = neg(one)` is `i·i = −1`).
  This is the same "notation is the point" exception the literate files invoke.
  (The group-identity `E` is a different constant — an abstract unit, ALLCAPS by
  the default rule — and stays uppercase; the exception is only for π, e, i.)
- Statement names are **spelled out**: `addZeroLeft`, not `addZ`; properties in
  full: `addIsCommutative`, not `addComm`.
  - Equation-shaped facts encode which argument position they describe:
    axiom `addZeroLeft` is `add(ZERO, b) = b`; theorem `addZeroRight` is
    `add(n, ZERO) = n`; likewise `addSuccLeft` / `addSuccRight`. This prevents
    near-collisions between an axiom and its mirror-image theorem.
- Kebab labels work because `-` joins identifier characters (`x->y` still
  lexes as an arrow). A deliberate consequence: there is **no infix minus,
  ever** — subtraction is `sub(a, b)`.  Note that this convention may be
  changed in the future.
- Variables may be one letter, but this is slightly discouraged — reserve it
  for conventional mathematical scalars in their home domain: `a, b, m, n`
  ranging over `Nat`; `x, y, z, w` over the reals; `i, j, k` as indices
  (including induction variables). Anything else gets a snake_case word.
- **Element-domain sorts — prefer `Element`.** When a theory is built over an
  ambient domain of *underlying individuals* it quantifies over — sets over their
  members, functions over their points, relations over their relata — name that
  element-domain sort **`Element`** (as `std/element.b4m` does). Reserve it for the
  underlying individuals, NOT the structure's own sort: a group is `Grp`, ℤ is
  `Int`, a set is `Set` — those *are* the objects the theory is about, not a domain
  beneath them. A shared canonical name lets element-domains compose (and `model`
  onto each other) without an aliasing layer. This is a *recommendation*: the older
  `set.b4m`/`function.b4m` spell the same concept `Universe` and are reconciled to
  `element.Element` by alias — a working split, not a bug; **do not retrofit them**.
  The guideline is for new theories, where the name is free.

## Binder order — canonical, first-appearance (lint-enforced)

A statement's leading `forall` block binds its variables in **first-appearance
order**: the order they first occur, left to right, in the body. `add` is
associative as `forall a, b, c: Nat; add(add(a, b), c) = add(a, add(b, c))` —
`a`, then `b`, then `c` as you read the left-hand side — **never** `forall c, b,
a` even if the proof fixes them in that order.

The rule exists because a statement's signature is a property of *what it says*,
not *how it is proved*. Two logically identical facts whose binders are permuted
are NOT alpha-equal, so a proof-convenience ordering silently breaks any
mechanism that matches on syntactic shape — most sharply `model`, whose axiom
discharge needs a local fact to alpha-match the (remapped) abstract axiom. Keep
every statement canonical and a local fact discharges the abstract axiom
directly, with no binder-reordering adapter theorem in between.

`2b4m lint <file>` flags every violation (`'forall c, b, a' should be 'forall a,
b, c'`). Run it on new `.b4m`; it also reads `.md` (only source-agnostic rules
like this one apply to a literate transliteration — its naming mirrors the book).

## Left-axiomatic — pick the LEFT law as the primitive

When a two-sided/symmetric operation has a **Left/Right pair** of laws and one
side is **derivable from the other**, make the **LEFT** law the axiom and prove
the RIGHT law as a theorem. This is the convention across `std`:

- **Identity / inverse** (`op(E, a) = a` vs `op(a, E) = a`): `group.b4m`,
  `subgroup.b4m`, `ring.b4m` axiomatize `opIdentityLeft` / `addZeroLeft` /
  `addNegLeft` and *prove* the `…Right` versions (via associativity +
  commutativity). Matches conventional algebra: `ea = a`, `a⁻¹a = e`.
- **Recursion** (which argument a recursive `func` recurses on): `peano.b4m` and
  `integer.b4m` recurse on the **first** argument — `add(ZERO, b) = b`,
  `add(succ(a), b) = succ(add(a, b))` are the axioms; `addZeroRight` /
  `addSuccRight` are theorems proved by induction. For a recursive definition,
  "left-axiomatic" means the recursion equations themselves are left-recursive:
  ZERO/`succ`/`prev` sit in the first slot, and the RIGHT-recursion mirrors are
  bootstrapped from them. (For `mul`, note the extra summand flips with the
  side: left `mul(succ(a), b) = add(mul(a, b), b)` adds the *second* factor,
  where the right mirror `mul(a, succ(b)) = add(mul(a, b), a)` adds the first.)

Why LEFT: it is the foundational choice (`peano.b4m` sets it, everything above
inherits), it matches the textbook statements, and one primitive side keeps the
axiom set minimal — a `model` that discharges the theory then supplies only the
LEFT laws and the RIGHT laws materialize for free (see `ring.b4m`'s
`AdditiveGroup`, which maps `opIdentityLeft`/`opInverseLeft` only).

**Exception — genuinely independent sides.** The rule applies only when one side
is *derivable*. When the Left and Right laws are **independent facts**, both stay
axioms: `function.b4m`'s `inverseLeft`/`inverseRight` (a map can have a
one-sided inverse without the other) and `peano-subtraction.b4m`'s
`subZeroLeft`/`subZeroRight` (`sub(ZERO, a) = ZERO` vs `sub(a, ZERO) = a`, not
mirror images since truncated subtraction is not commutative) are correctly
two-axiom pairs. Don't collapse a pair you cannot actually derive.

## Labels

**The dump test.** The label column IS the proof outline: stripping every
assertion and justification line must leave a skeleton from which a reader can
reconstruct the argument. Every label is judged by what it contributes to that
skeleton.

- **Every label is a mini-assertion of the fact it establishes**:
  `@six-is-nonzero`, `@three-is-below-six`, `@quotients-are-equal`. Never bare
  counters (`eq2`, `s3`), never abbreviations (`gen-a`, `mi-b`, `qcbl` — write
  the words out), never pure operation names when a content name exists.
- **A specialized fact folds its instance into the name**:
  `@remainder-is-unique-nine-six`. Long names are fine — noise is
  meaninglessness, not length.
- **Provenance is not content.** The justification line already says
  `[by cite modIntro]`; the label says what the step *asserts*
  (`@remainder-is-unique`), not what was cited. Exception that proves the
  rule: when a lemma's own name is already an assertion
  (`addIsCommutative`), its kebab form is a fine content name
  (`@add-is-commutative`).
- **Name the move, not the proposition.** The formula line is right there — a
  label that just re-narrates its syntax earns nothing. On a line reading
  `forall b, d: Nat; ...`, `@for-all-b-d` is dead weight; the step's real
  contribution is *discharging the `fix`* (`@discharge-b`). Likewise a
  `forall_elim` step's content is the *specialization* it performs
  (`@specialized-to-this-a-b`), not that the result is now quantifier-free.
  Ask "what did this step DO to the argument?" — that is the name.
- **Steps that assert nothing should not exist.** Specialization towers
  collapse with multi-argument `forall_elim(A, B, C)`; modus-ponens discharge
  ladders collapse with `tautology` (see the apply-a-lemma idiom below). Only
  name what survives.

**Stock names for structural roles** (one standard spelling per role, full
words — the role IS the content for these):

| role | name |
|---|---|
| final step of every proof | `@conclusion` |
| step establishing `P(ZERO)` (the base premise) | `@base-case` |
| block proving the base when it needs its own subproof | `@base-case-proof` (its export step is then `@base-case`) |
| fix-block deriving the successor case | `@induction-step` |
| assume-block introducing `P(k)` | `@given-inductive-hypothesis` |
| restatement of `P(k)` inside it | `@inductive-hypothesis` |
| the implication at fixed `k` | `@induction-step-at-k` |
| the generalized step premise | `@induction-step-for-all-k` |
| fix-block generalizing a statement binder | `@generalize-<var>` |
| forall_intro closing such a block | `@discharge-<var>` (it discharges the `fix`; do NOT name it `@for-all-<var>`, which merely echoes the formula) |
| forall_elim specializing a lemma | `@specialized-<to-what>` / `@<fact>-at-<args>` (name the specialization, not that it is now quantifier-free) |
| assume-block (hypothesis intro) | `@given-<content>` (`@given-b-nonzero`) |
| implies_intro export | `@<cond>-implies-<result>` |
| the existential feeding an unpack | `@<thing>-exists` (`@gap-exists`) |
| unpack-block naming a witness | `@with-<role>-<var>` (`@with-gap-d`, `@with-quotient-j`); fallback `@with-witness-<var>` |
| case arms (`case`/`or_elim` branches) | `@when-<condition>` (`@when-zero`, `@when-successor`) |
| a flipped equation (`[by symmetry x]`) | `@<content>-flipped` |

The induction payoff line reads
`[using instantiation induction((fun ...)) base-case induction-step-for-all-k]`.

**The apply-a-lemma idiom** — cite, specialize, discharge; three nameable
steps, no filler:

  ```
  @remainder-is-unique |
    forall a, b, q, r: Nat; b != ZERO -> less_than(r, b) -> add(mul(b, q), r) = a -> mod(a, b) = r
    [by cite modIntro]
  @remainder-is-determined-nine-six |
    SIX != ZERO -> less_than(THREE, SIX) -> add(mul(SIX, ONE), THREE) = NINE -> mod(NINE, SIX) = THREE
    [by forall_elim(NINE, SIX, ONE, THREE) remainder-is-unique]
  @conclusion |
    mod(NINE, SIX) = THREE
    [using tautology remainder-is-determined-nine-six six-is-nonzero three-is-below-six sum-is-nine]
  ```

  (`tautology` replays as a kernel-checked certificate here — a Horn-shaped discharge
  never approaches its atom cap or step budget. If a discharge ever exceeds
  the 16-atom cap, fall back to named `modus_ponens` steps.)

## Proof variables

- **No shadowing — checker-enforced.** No introduced name (quantifier binder,
  lambda binder, parameter, fix/unpack variable) may reuse any visible name: a
  variable in scope, a schema parameter, or any declared symbol.
- When generalizing a statement variable with `fix`, reuse the statement's own
  binder name (`theorem t: forall b, ... proof @g | fix b: Nat { ... }`). Binder
  hints and fix-variables don't collide — hints carry no identity.
- Induction variables are named `k` (matching the schema's conventional
  parameter).
- Variable names must be fresh per proof (checker-enforced). When a conceptual
  variable must be re-fixed in a disjoint subproof, append an index: `a`, then
  `a2`, `a3`.
- When restating a fact whose binder names would shadow variables in scope,
  rename the binders freely (`forall c: Nat; ...`) — alpha-equivalence ignores
  hints.

## Imports

- `import peano <<< "peano.b4m"` binds a namespace to a file (path relative to
  the importing file). Imports come first in the file.
- Everything imported is referenced **qualified** (`peano.Nat`,
  `[by cite peano.addIsCommutative]`) or via an **explicit alias**:
  `sort Nat = peano.Nat`, `const ZERO = peano.ZERO`, `func succ = peano.succ`.
  Aliases are kind-checked views of the same entity — both spellings denote
  the same thing, and there is no wildcard `open`.
- **Alias only when it earns its place: alias a name used more than once,
  qualify inline (`peano.mulSuccLeft`) for a single use.** An alias line at
  the top pays for itself when the name recurs; for a lone reference it just
  adds a line to scan past, so write the qualified name at its one call site
  instead. (This keeps alias headers to the vocabulary a file actually
  leans on.)
- **Naming the arithmetic theory**: `by arithmetic` resolves its vocabulary
  and certificate lemmas in **local scope**; `by arithmetic(<module>)`
  resolves them against an imported theory module (e.g.
  `by arithmetic(ordering)` after `import ordering <<< "std/peano-ordering.b4m"`).
  Prefer the named form in a file that is layers above the primitives or is a
  subdomain still building its own vocabulary: it certifies against the solid
  theory beneath it without aliasing `add`/`less_than`/the order lemmas into
  the local namespace. `std/peano-ordering.b4m` is the canonical theory module
  (it carries the full order + Farkas lemma set). A named theory must supply
  every symbol the goal uses, or the check hard-errors naming the gap.
- **Trust model**: `2b4m check` verifies everything by default — every `using`
  step (accelerant / model / import) produces a kernel-checked certificate.
  `--fast` defers that per `using` WORD for iteration, admitting the trusted
  words (`--fast` = all, `--fast-only W…` = allowlist, `--fast-except W…` =
  denylist), always with a loud accelerated banner. `instantiation` is never
  trustable (the per-instance proof is the only soundness gate). Re-run plain
  `2b4m check` before finalizing.

## Layout of steps

- Each step is three lines: the `@`-sigiled label alone, then the formula, then
  the bracketed justification — the formula and justification aligned two spaces
  under the label:

  ```
  @conclusion |
    forall n: Nat; add(n, ZERO) = n
    [using instantiation induction((fun k: Nat => add(k, ZERO) = k)) base step]
  ```

  The `@` marks a definition and sits at the left margin, so labels form a
  scannable gutter column; citations of a label stay bare. (The brackets are
  syntax — the justification is a delimited unit — but the line breaks are
  convention; the checker is whitespace-insensitive. `2b4m fmt` produces this
  shape.)
- Two-space indent per block depth.
- Blank line between proof phases; none within a phase.
- Soft limit ~100 columns.
- Layout tokens are not "overhead": structure gives both the reviewer and a
  generating LLM room to think. Do not compress for token frugality.
- `2b4m fmt <file>` normalizes all of this mechanically (in place;
  `--check` reports instead of rewriting). It is strictly a whitespace and
  indentation tool: it preserves comments, blank-line placement (collapsed to
  one), and the author's line breaks within statements (re-indenting
  continuations to +2) — and it never checks or rewrites names.
