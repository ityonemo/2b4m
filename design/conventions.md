# 2b4m proof-writing conventions

These optimize for the two audiences of a `.b4m` file: an LLM writing it and a human
reviewing it. Most are style, normalized by `2b4m fmt`; a few are checker-enforced where
noted. `examples/peano.b4m` is the living exemplar. For the language itself — every keyword,
every tactic's surface and errors — see `../GUIDE.md`.

## File layout

Order: header comment → imports → aliases → sorts → constants → functions → predicates →
axioms → theorems. Blank lines between the groups; in larger files, section comments
(`// -- axioms ----`). The header comment states what the file is and what it proves.

**A theory and its sub-theories.** A theory that grows past one file becomes a parent
`std/X.b4m` beside a directory `std/X/` holding its sub-theories (`std/integer.b4m` +
`std/integer/order.b4m`, `std/integer/divides.b4m`, …). The parent ends with a
`// THEORY OF X` section forwarding its sub-theories' results by alias
(`theorem gcdGreatest = divides_theory.gcdGreatest`). A consumer then writes
`import integer` and reaches the order, the division algorithm and gcd without knowing
which file proved which.

Forward the **takeaway results** — what someone reasoning about the theory reaches for. A
lemma belongs in the forwarding section no more than it belongs in an `intheory` block; a
consumer that genuinely wants one keeps the honest `import integer/order`.

**Name an import after its PATH, with `/` written `_`**: `std/function/invertible.b4m` is
`function_invertible`, `std/integer/divides.b4m` is `integer_divides`, `std/peano.b4m` is
`peano`. The name is then mechanical — writable without opening the file, and a reader
recovers the path from it. An import binds a namespace in the same declaration space as
every sort and symbol, so a theory named after its subject collides with the subject itself;
a path-shaped name never does.

A `-` becomes `_` too (`std/integer/mod-n.b4m` → `integer_mod_n`). Where a name would be
intolerably long, shorten from the FRONT — drop leading segments the context makes obvious
(`function_invertible`, not `std_function_invertible`) — never from the back, which is the
part that identifies the theory.

## Writing `std`

Three rules make `std` `std`.

**1. Well-known constants and operations take the name of the domain of discourse**, which
is usually the subdirectory — but some domains are rooted differently (a polynomial file is
about `R[x]` parameterized over its coefficients, so the directory records WHICH
coefficients, not the subject).

In `std/<theory>/*` or `std/<theory>.b4m`, that theory owns the unmodified names. A
**visiting** theory takes a full-word prefix — `nat_`/`NAT_`, `int_`/`INT_`, `real_`/`REAL_`
— never a bare letter:

```2b4m
// in std/integer/embedding.b4m — ℤ is the theory, ℕ is visiting
const ZERO      = integer.ZERO        oper add     = integer.add
const NAT_ZERO  = peano.ZERO          oper nat_add = peano.add
```

**Never prefix a name nothing competes for.** `nat_less_than` in a permutation file guards
against a `less_than` that does not exist and reads as a collision where there is none. If
no local declaration claims the bare name, take it.

**2. No totalizing functions** — unless the standard mathematical convention *is* total
(`gcd(0,0) = 0`, `0! = 1`). A function that is undefined somewhere gets a `requires` guard;
inventing a value at the gap makes every downstream theorem quietly weaker than it reads.

**3. Alias what exists; declare bare only what is new.** A file that re-declares a symbol
its import already provides creates a second entity that merely looks like the first.

## Literate `.md` structure

In a literate transliteration, introduce each component where the prose reaches it, rather
than hoisting every declaration to the top. The file reads as exposition, so a sort appears
where the text introduces the concept and an axiom where the text states it. The test is
whether it reads naturally as prose, not a mechanical rule.

Imports still come first — they are not exposition.

## Comments carry the "why"

Not required, but expect an LLM to be prompted with a comment block and asked whether the
theorem below it is correct.

- Every theorem gets a **strategy comment**: the proof idea in a line or two
  (`// Strategy: induction on b with prop(k) := forall a. ...`). A reviewer, or a future
  session with cold context, should never reverse-engineer intent from the steps.
- Inside proofs, **phase comments** mark structure: `// base case: ...`.
- Comments explain *why*; steps state *what*. Don't paraphrase a step in its comment.
- Statement-level quirks get a comment (why a quantifier order was chosen, say).

## Naming

| Category | Style | Example |
|---|---|---|
| Sorts | ProudCamelCase | `Nat`, `Prop`, `Word32` |
| Constants | ALLCAPS | `ZERO`, `ONE`, `E` (identity) |
| Functions / predicates | snake_case word | `succ`, `add`, `even` |
| Axioms / theorems | camelCase | `addZeroLeft`, `induction` |
| Labels | kebab-case | `induction-step`, `given-inductive-hypothesis` |
| Variables | snake_case | `a`, `k`, `high_word` |

- Functions and predicates are never **one letter**: `succ`, not `S`. Same for schema
  parameters (`prop(Nat)`, not `P`) — they are function-shaped.
- **Named mathematical constants keep their conventional lowercase spelling**: `pi`, `e`,
  `i` — their standard notation *is* lowercase, and `i*i = neg(one)` reads as `i·i = −1`.
  (The group identity `E` is a different constant and stays ALLCAPS.)
- Statement names are **spelled out**: `addZeroLeft`, not `addZ`; `addIsCommutative`, not
  `addComm`. Equation-shaped facts encode the argument position: `addZeroLeft` is
  `add(ZERO, b) = b`, `addZeroRight` is `add(n, ZERO) = n`. This keeps an axiom and its
  mirror-image theorem from near-colliding.
- Kebab labels work because `-` joins identifier characters (`x->y` still lexes as an
  arrow). Consequence: there is **no infix minus** — subtraction is `sub(a, b)`.
- Variables may be one letter, but prefer it only for conventional scalars in their home
  domain: `a, b, m, n` over `Nat`; `x, y, z, w` over the reals; `i, j, k` as indices.
  Anything else gets a snake_case word.
- **Element-domain sorts — prefer `Element`.** When a theory is built over an ambient domain
  of underlying individuals it quantifies over — sets over members, functions over points,
  relations over relata — name that sort `Element` (as `std/element.b4m` does). Reserve it
  for the individuals, NOT the structure's own sort: a group is `Grp`, ℤ is `Int`, a set is
  `Set`. A shared canonical name lets element-domains compose, and `model` onto each other,
  without an aliasing layer.

## Binder order — canonical, first-appearance (lint-enforced)

A leading `forall` binds in **first-appearance order**: the order the variables first occur,
left to right, in the body. `add` is associative as
`forall a, b, c: Nat; add(add(a, b), c) = add(a, add(b, c))` — never `forall c, b, a`, even
if the proof fixes them in that order.

A statement's signature is a property of what it *says*, not how it is proved. Permuted
binders are not alpha-equal, so a proof-convenience ordering breaks anything matching on
syntactic shape — most sharply `model`, whose axiom discharge needs a local fact to
alpha-match the remapped abstract axiom.

## Left-axiomatic — pick the LEFT law as the primitive

When a symmetric operation has a Left/Right pair of laws and one side is **derivable from
the other**, axiomatize the LEFT and prove the RIGHT. It is the foundational choice
(`peano.b4m` sets it, everything above inherits), it matches the textbook statements, and
one primitive side keeps the axiom set minimal — a `model` then supplies only the LEFT laws
and the RIGHT ones materialize for free.

For a recursive `oper` this means the recursion equations are left-recursive: `ZERO`/`succ`/
`prev` sit in the first slot. (For `mul`, note the extra summand flips with the side: left
`mul(succ(a), b) = add(mul(a, b), b)` adds the *second* factor, where the right mirror adds
the first.)

**Exception — genuinely independent sides stay axioms.** `function.b4m`'s
`inverseLeft`/`inverseRight` (a map can have one one-sided inverse without the other) and
`peano/subtraction.b4m`'s `subZeroLeft`/`subZeroRight` (`sub(ZERO, a) = ZERO` vs
`sub(a, ZERO) = a` — not mirror images, since truncated subtraction is not commutative) are
correctly two-axiom pairs. Don't collapse a pair you cannot derive.

## Labels

**The dump test.** The label column IS the proof outline: stripping every assertion and
justification line must leave a skeleton a reader can reconstruct the argument from.

- **Every label is a mini-assertion of the fact it establishes** — `@six-is-nonzero`,
  `@quotients-are-equal`. Never bare counters (`eq2`, `s3`), never abbreviations (`qcbl` —
  write the words out). Long names are fine; noise is meaninglessness, not length. A
  specialized fact folds its instance in: `@remainder-is-unique-nine-six`.
- **Provenance is not content.** The justification line already says `[by cite modIntro]`;
  the label says what the step *asserts*. (When a lemma's own name is already an assertion,
  its kebab form is a fine content name: `@add-is-commutative`.)
- **Name the move, not the formula.** On a line reading `forall b, d: Nat; ...`,
  `@for-all-b-d` is dead weight — the step's contribution is discharging the `fix`
  (`@discharge-b`). Ask what the step DID to the argument.
- **Steps that assert nothing should not exist.** Specialization towers collapse with
  multi-argument `apply_at(A, B, C)`; modus-ponens ladders collapse with `tautology`.

Stock spellings for structural roles, where the role IS the content: `@conclusion`,
`@base-case`, `@induction-step`, `@inductive-hypothesis`, `@generalize-<var>` /
`@discharge-<var>` for a fix block and its closer, `@given-<content>` for an assume block
(`@given-b-nonzero`), `@specialized-<to-what>` for an `apply_at`.

## Proof variables

- **No shadowing — checker-enforced.** No introduced name (quantifier or lambda binder,
  parameter, fix/unpack variable) may reuse a visible one.
- When generalizing a statement variable with `fix`, reuse the statement's own binder name.
  Binder hints and fix-variables don't collide — hints carry no identity.
- Induction variables are named `k`, matching the schema's conventional parameter.
- Names must be fresh per proof (checker-enforced). When a conceptual variable is re-fixed
  in a disjoint subproof, index it: `a`, then `a2`.
- When restating a fact whose binders would shadow, rename them freely — alpha-equivalence
  ignores hints.

## Imports

- Imports come first. Everything imported is referenced **qualified** (`peano.Nat`) or via
  an explicit alias (`sort Nat = peano.Nat`). There is no wildcard `open`.
- **Alias only when it earns its place: alias a name used more than once, qualify inline
  for a single use.** An alias pays for itself when the name recurs; for one reference it is
  a line to scan past.

## Layout of steps

Each step is three lines — the `@`-sigiled label alone, then the formula, then the bracketed
justification, the latter two aligned two spaces under the label:

```
@conclusion |
  forall n: Nat; add(n, ZERO) = n
  [using instantiation induction((fun k: Nat => add(k, ZERO) = k)) base step]
```

The `@` marks a definition and sits at the left margin, so labels form a scannable gutter
column; citations of a label stay bare.

- Two-space indent per block depth; blank line between proof phases, none within a phase.
- Soft limit ~100 columns.
- **Layout tokens are not overhead**: structure gives both the reviewer and a generating LLM
  room to think. Do not compress for token frugality.

`2b4m fmt` produces all of this mechanically.
