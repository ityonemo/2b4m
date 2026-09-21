---
paths:
  - "**/*.bpa"
  - "aata/**/*.md"
  - "examples/**/*.md"
---

# Writing bpa proofs — the drift-prone conventions

`CONVENTIONS.md` is canonical. This rule surfaces the parts that erode over a
long generation session — chiefly **proof labels**. When writing or reviewing a
`.bpa` proof (or a ```bpa block in a literate `.md`), hold these in mind.

**Transcription exception.** When transcribing material from an external source
(e.g. an AATA textbook chapter into `aata/`), use discretion to match the
source's own formatting where it conflicts with a convention — the book's
notation is the point. This overrides the *naming* rules in particular: alias
to the source's symbols (`sort G = group.Grp`, `func inv = group.inverse`,
`const e = group.E`), keep its one-letter variables, and mirror its theorem
names. It does NOT excuse bad **labels** — the dump test still holds; a
transcribed proof's own `@labels` are yours to write well regardless of the
source. Note the deviation where it isn't obvious.

## Labels — the thing that drifts (get this right)

**The dump test.** The label column IS the proof outline: strip every formula
and justification line, and the remaining `@labels` must let a reader
reconstruct the argument. Every label is judged by what it contributes to that
skeleton. If the skeleton reads like noise, the labels are wrong.

`bpa query outline <file> <theorem>` prints exactly this skeleton — the labels
plus block headers, nothing else. **Read the outline as the acceptance test:**
it should be *narrative* — reading it top to bottom should convey the shape and
flow of the proof (what is assumed, what is derived, how it concludes) to
someone who has not read the steps. A well-labeled proof outlines into prose;
a poorly-labeled one outlines into a list of opaque tokens. Run it on what you
write and check that it reads.

- **Every label is a mini-assertion of the fact it establishes** —
  `@six-is-nonzero`, `@quotients-are-equal`, `@inverse-cancels-on-the-left`.
  - NEVER bare counters (`eq2`, `s3`, `step1`).
  - NEVER abbreviations (`gen-a`, `mi-b`, `fwd`, `bwd`, `ca`, `ext`, `imp`,
    `concl`, `hyp` — write the words out).
  - NEVER a pure operation/provenance name (`mem-union`, `ax-union`,
    `forall-elim-1`) — the justification line already says what was cited; the
    label says what the step *asserts*.
- **Name the MOVE, not the proposition.** The formula line is right there — a
  label that re-narrates its syntax earns nothing. `@for-all-b-d` on a
  `forall b, d; …` line is dead weight; the step's real contribution is
  *discharging the `fix`* → `@discharge-b`. A `forall_elim` step's content is
  the *specialization* → `@specialized-to-a-b` / `@lemma-at-a-b`, not that it is
  now quantifier-free. Ask: "what did this step DO?"
- **A specialized fact folds its instance into the name**:
  `@remainder-is-unique-nine-six`. Long names are fine — noise is
  meaninglessness, not length.
- **Steps that assert nothing should not exist.** Collapse specialization towers
  with multi-arg `forall_elim(A, B, C)`; collapse modus-ponens ladders with
  `tautology` (the apply-a-lemma idiom). Only name what survives.

### Stock names for structural roles (use these exact spellings)

| role | name |
|---|---|
| final step of every proof | `@conclusion` (NOT `@done`, `@result`, `@qed`) |
| concluding step of a NESTED subproof block | `@conclusion-<what-it-concludes>` (`@conclusion-add-left-swaps`, `@conclusion-two-divides-p`) — the `@conclusion-` prefix marks a subproof's final step; the suffix says what it proved (NOT the bare `@conclusion-inner`) |
| `P(ZERO)` base premise | `@base-case` |
| base needing its own subproof | `@base-case-proof` (export → `@base-case`) |
| fix-block deriving the successor case | `@induction-step` |
| assume-block introducing `P(k)` | `@given-inductive-hypothesis` |
| restatement of `P(k)` inside it | `@inductive-hypothesis` |
| implication at fixed `k` | `@induction-step-at-k` |
| generalized step premise | `@induction-step-for-all-k` |
| fix-block generalizing a statement binder | `@generalize-<var>` (NOT `@gen-a`) |
| forall_intro closing such a block | `@discharge-<var>` (NOT `@close-a`, and NOT `@for-all-<var>` which just echoes the formula) |
| forall_elim specializing a lemma | `@specialized-<to-what>` / `@<fact>-at-<args>` |
| assume-block (hypothesis intro) | `@given-<content>` (`@given-b-nonzero`) |
| implies_intro export | `@<cond>-implies-<result>` |
| existential feeding an unpack | `@<thing>-exists` (`@gap-exists`) |
| unpack-block naming a witness | `@with-<role>-<var>` (`@with-quotient-j`); fallback `@with-witness-<var>` |
| case / or_elim arms | `@when-<condition>` (`@when-zero`, `@when-successor`) |
| a flipped equation (`[by symmetry x]`) | `@<content>-flipped` |

(When a lemma's own name is already an assertion — `addIsCommutative` — its kebab
form is a fine content label: `@add-is-commutative`.)

## The other conventions — quick reminders (CONVENTIONS.md has the detail)

- **Strategy comment** before every theorem (one or two lines: the proof idea).
  In a literate `.md`, the prose paragraph above the block serves this role.
  **Phase comments** inside proofs mark structure (`// base case:`,
  `// inductive step:`). Comments say *why*; steps say *what* — don't paraphrase
  a step in its comment.
- **Naming**: Sorts `ProudCamelCase`; consts `ALLCAPS` — EXCEPT the named
  mathematical constants `pi`, `e`, `i` (circle constant, Euler's number,
  imaginary unit), written **lowercase** because their conventional notation is
  lowercase (`i*i = neg(one)`); the abstract group-identity `E` is a different
  constant and stays uppercase; funcs/preds `snake_case`
  words never one letter (`succ` not `S`); axioms/theorems `camelCase` spelled
  out (`addZeroLeft`, not `addZ`; `addIsCommutative`, not `addComm`);
  equation-shaped names encode the argument position (`addZeroLeft` =
  `add(ZERO,b)=b`, `addZeroRight` = `add(n,ZERO)=n`); variables `snake_case`,
  one letter only for conventional scalars (`a,b,m,n` Nat; `i,j,k` indices). A
  theory's element-domain sort (the underlying individuals it quantifies over —
  set members, function points, relation relata) is preferably **`Element`**, not
  the structure's own sort (`Set`/`Grp`/`Int` stay themselves); older
  `Universe` spellings are reconciled, don't retrofit.
- **Proof variables**: no shadowing (checker-enforced); when generalizing a
  statement binder, reuse the statement's own binder name; induction variable is
  `k`; re-fixing a conceptual var in a disjoint subproof appends an index
  (`a`, `a2`). No infix minus — ever (`sub(a, b)`).
- **Imports**: name an import after its PATH with `/` written `_`
  (`std/function/invertible.bpa` → `function_invertible`) — a namespace shares a
  declaration space with every symbol, so naming a theory after its subject
  collides with the subject (`import invertible` beside `pred invertible = …` is
  a hard duplicate-declaration error, plus confusing follow-on errors at each
  *use*). Then alias a name used more than once, qualify inline
  (`peano.mulSuccLeft`) for a single use. Prefer `by arithmetic(<module>)` in
  files layered above the primitives.
- **Layout**: three lines per step — `@label |`, then the formula, then
  `[by …]`, formula/justification indented two spaces under the label; two-space
  indent per block depth; blank line between phases; `bpa fmt` normalizes
  whitespace only (never names).
