# `model` — structure reuse ("X is-a Y")

A `model` declaration says *this concrete thing satisfies that abstract theory*, and in
exchange the theory's whole derived corpus becomes citable at the concrete thing. It is
how `std/integer.b4m` gets the ring corpus without re-deriving it, and how one proof
over an abstract `Grp` serves ℚ-under-addition, ℚ∖{0}-under-multiplication, and every
subgroup.

## How `model` works, in general

A `model` declaration **creates a universe of discourse** — an interpretation in which the
source theory's vocabulary means something else — and **names it**, so the universe can be
referred to. The body is a bag of overloads saying what each source symbol means in that
universe, and which local facts pay off the source theory's axioms:

```2b4m
// std/integer/mod-n.b4m — ℤ_n is a group
model ZnGroup {
  group.Grp: Zn                           // `:`  interprets a sort
  group.E: ZERO                           // `:`  interprets a const
  group.op: add                           // `:`  interprets an oper
  group.inverse: neg
  group.opAssoc <- addAssoc               // `<-` discharges an axiom obligation
  group.opIdentityLeft <- addIdentityLeft
  group.opInverseLeft <- addInverseLeft
}
```

A sort mapping is not a privileged "carrier header" — it is one more overload. The name is
mandatory because the universe is the thing being named: two models over the same source
coexist on one carrier (ℚ under addition and ℚ∖{0} under multiplication are both groups)
and are told apart only by it.

**Two kinds of line, and they take DIFFERENT arrows:**

| arrow | left side | right side | reads as |
|---|---|---|---|
| `:` | a sort, const, oper or pred | the symbol it means here | "is interpreted as" |
| `<-` | an axiom of the source theory | a fact that establishes it | "is discharged by" |

An axiom obligation names a *fact* — an existing axiom or theorem whose formula already
has the remapped shape — never a proof block. Using the wrong arrow is a hard error in
both directions, each with its own gate: `:` on an axiom
(`tests/cases/model/model_axiom_colon_bad.b4m`) and `<-` on a symbol
(`tests/cases/model/model_symbol_arrow_bad.b4m`). Keeping them distinct means the block
says which lines are *definitions of meaning* and which are *debts being paid*.

### `definition` — a definition block discharges a definition block, arm for arm

A multi-clause `oper f(…) => U: f(…) = …; f(…) = …` publishes one obligation per clause,
and those clauses have **no user-facing names** — so there is nothing to put on the right
of a `<-` per arm. Instead the SYMBOL stands for the whole obligation set, and clause 0
discharges clause 0, clause 1 clause 1:

```2b4m
oper madd(a: M, b: M) => M:
  madd(MZ, b) = b;
  madd(msucc(k), b) = msucc(madd(k, b))

model Mod {
  base.N: M
  base.NZ: MZ
  base.nsucc: msucc
  base.nadd: madd        // `:`  interprets the symbol
  base.nadd <- madd      // `<-` discharges its definitional obligations, arm for arm
}
```

The symbol appears on **both** arrows, and that is not redundant: one line says what
`nadd` means here, the other says this definition pays off that definition's clauses.

Two rules make the pairing meaningful:

- **A definitional axiom is overloadable ONLY by another definition.** You cannot discharge
  a definition's clause with an unrelated theorem that happens to match.
- **The pairing is NOT shape-checked at the model.** A mismatched pair is caught at the
  first citation, where the diagnostic can show both formulas
  (`tests/cases/model/definition/model_definition_bad.b4m`).

To cite one clause of a transferred definition, index it — zero-based:

```2b4m
[using model(Mod) definition(0) base.nadd]     // the madd(MZ, b) = b arm
[using model(Mod) definition(1) base.nadd]     // the successor arm
```

Outside a model the same form cites a definition's clause directly — `[by definition(N) f]`
for an operation clause (165 uses in the corpus), `[by definition p]` with no index for a
single-clause predicate. A definition clause is a **ground fact**, so `definition` is a
`by` rule, never `[using …]`.

### A model's universe is referable from anywhere

The named universe is not private to the file that declares it. A model is referred to
like any other declaration — bare when it is in scope, qualified through an import when it
is not:

```2b4m
import rational <<< "std/rational.b4m"
…
[using model(rational.RationalOrderedField) field_order.zeroLessThanOne]
```

That is `std/rational/integer-order.b4m` citing a universe declared in
`std/rational.b4m`. The corpus does this 36 times across six models;
`rational.RationalOrderedField` alone is cited 25 times from four other files. So a theory
can establish *once* that its carrier satisfies some abstract theory, and every file
downstream cites that universe rather than re-declaring an identical model of its own.

### The overlay chain, and the universe fixpoint

Mechanically a model is an **overlay with a parent**, and resolving a name in a model
namespace means: resolve it to its source `Index` in the source file's universe namespace,
then walk the chain (`InternPool.applyModel`) for a mapping. **An un-overloaded entity
returns UNCHANGED** — the universe fixpoint, and the load-bearing line: it is what makes
citing an undischarged abstract axiom fail (see below).

`.universe` is the empty overlay, hence the identity, which is why an ordinary proof and a
transferred proof run the same code path with `model = .universe` in the ordinary case.

### Citing a transferred theorem

```2b4m
theorem unitsCancelLeft: forall a, b, c: QStar; mul(a, b) = mul(a, c) -> b = c
proof
  @conclusion |
    forall a, b, c: QStar; mul(a, b) = mul(a, c) -> b = c
    [using model(RationalUnitsGroup) group.cancelLeft]
qed
```

The cite names **both** the universe (which interpretation) and the source theorem (what
to transfer), because a sort has several models. The universe may be bare or
import-qualified, per the section above. Spelling follows the parameterized-tactic
convention — instance in parens as the mode selector, source theorem as a bare ref, no
`with` particle. `model` is an **engine word** (`Verify.Word.engine()` is exactly
`{model, import}`), so it is `[using …]`, never `[by …]`.

### What strict mode actually does

A `[using model(M) src.thm]` step **demands a transferred ProveTask** keyed by
`(M, src_file)` — `Prove.demandTransfer` — and suspends until it proves. The source
theorem's proof is genuinely re-elaborated and kernel-checked in target space; the
obligation discharge *is* that checking, so nothing is taken on faith.

Two consequences worth knowing:

- a transferred SCHEMA additionally demands the discharging schema's instance at this
  proof's own arguments (`demandSchemaTransfer`);
- a proof running under a transfer keeps its formulas in **both** spaces — `goal` in
  target space and `goal_source` in source space — because an accelerant builds in
  SOURCE space and the mapping applies afterwards. `Prove.underModel()` is the test.

Under `--fast`, `model` is trustable: the transfer is admitted without re-proving the
source. The decision still runs, so a goal the mapping does not actually yield is still
refused — see `acceleration.md` for where that boundary falls per word.

### Relativization — the guarded case

When a source sort maps onto a **predicated** (refined) target sort, the model is
relativized by that sort's qualifier: every source binder over the mapped sort picks up a
`guard(bound) ->` antecedent. Guarding is *inferred from a mapping*, never declared:

```2b4m
// std/rational/units.b4m — ℚ∖{0} is a group under multiplication
sort QStar = Rat where nonzero
model RationalUnitsGroup {
  group.Grp: QStar                                  // predicated ⇒ relativized by `nonzero`
  group.E: ONE(oneIsNonzero)                        // a const names its BASE fact
  group.op: mul -| productOfNonzeroIsNonzero        // an oper names its CLOSURE fact
  group.inverse: recip -| recipOfNonzeroIsNonzero
  group.opAssoc <- unitsAssoc                       // already guarded by nonzero
  group.opIdentityLeft <- unitsIdentityLeft
  group.opInverseLeft <- unitsInverseLeft
}
```

Applied uniformly in both directions. OUT: `group.cancelLeft`'s
`forall a,b,c: Grp; op(a,b)=op(a,c) -> b=c` comes back relativized over the carrier, with
a `nonzero(_)` antecedent per binder. IN: the discharging fact must ALREADY carry the
guards — the checker does not synthesize or strip them, which is why `unitsAssoc` is a
`QStar` theorem rather than a bare `Rat` one.

So a guarded model nominates **guard dischargers** right on the `:` lines — a const's base
fact in parens, an oper's closure fact after `-|` — because a refined target makes every
mapped symbol owe its guard. They are looked up by `InternPool.modelDischargers` and
discharged at the call site by `Prove.withGuardPremises`.

## Why you can't cite an un-overloaded axiom over an abstract sort

This is the soundness question the mechanism turns on.

**The rule.** When a transfer's re-elaboration reaches a cited fact, there are four cases:

| the cited fact | what happens |
|---|---|
| overloaded by the model | cite the target it maps to, kind-matched (an obligation discharged by a *theorem* becomes a theorem ref; by an *axiom*, an axiom ref) |
| not overloaded, and **unaffected** by the interpretation | cite as-is. The remap is the identity on it, so it is a genuinely shared fact |
| not overloaded, affected, a THEOREM | re-prove it under the model too |
| not overloaded, affected, an AXIOM | **must fail.** Its meaning shifts under the interpretation and nothing discharges it |

The last row is the important one. An abstract theory's axiom is a *constraint you promised
to honour*; citing it un-overloaded inside a transfer would assume the very thing the model
exists to establish. The obligation set is therefore **not** the source theory's declared
axiom list (unbounded and cross-file — a group-powers proof may lean on an arithmetic axiom
three files away). It is *whatever the proof actually cited*.

**How it is enforced: the universe fixpoint, not a separate check.** An un-overloaded
entity maps to *itself*. So a transfer reaching an undischarged abstract axiom re-derives
that axiom's SOURCE-space statement while the step's goal is in TARGET space, and the two
do not match. The citation fails **by statement mismatch**.

Worth knowing when reading a failure: the error names a formula, not a missing obligation.
That is also why an incomplete discharge can surface far from its cause — see
`../NESTED-MODEL-COMPOSITION-ISSUE.md`, where an unmapped F-level algebra fact reports
itself as a sort mismatch inside the source theory's own proof.

**The corollary for authors:** a fixed const/pred + axioms section IS a model source, and
is indistinguishable from dead code — or from a restriction — until some fixture
demonstrates the model. `std/group/order.b4m`'s `A`/`N` section and `coset.b4m`'s
`inSubgroup` are both of this shape: each looks like one fixed subject and transfers to
any.

## Partial models are legal — at the prover's risk

A model **need not map every source axiom**. A partial mapping is an interpretation with
an undischarged obligation, and the MODE decides the consequence:

- **`--fast`** never inspects which source axioms the transferred theorem's proof reached,
  so a transfer resting on an unmapped axiom **passes**. Disclosed as accelerated-by-model
  in the summary, invisible otherwise.
- **strict** re-elaborates, hits the unmapped axiom, and **rejects**.

> **THE WARNING.** A `--fast` green build over a partial model may FAIL strict. Treat it
> as provisional until plain `check` agrees.

### Partial models as a reverse-mathematics probe

The asymmetry is also a feature: comment out one obligation line, re-run strict, and the
checker names exactly the transferred theorems that genuinely used that axiom — "does
`cancelLeft` need inverses, or only associativity and identity?" It is sound as a probe
because a strict rejection means the proof really did cite the missing axiom.

## The design invariant

**Stay comptime-shaped: explicit at the cite, structural not nominal, resolved-to-concrete
and done, no dictionary, no search.** Test any proposed extension by asking whether it is a
comptime transform or needs a resolution mechanism.

- the cite always NAMES its universe — no instance search, no action at a distance;
- a carrier never *declares conformance*; you assert a mapping and the checker verifies the
  shape, failing at the use site;
- the remap emits the concrete statement and is done — no dictionary passing, no residual
  machinery at checking time;
- the kernel never learns what a "structure" is.

Three things would break this and are NON-GOALS: automatic model discovery, transitive
chains resolved by search, and coherence machinery to reconcile two paths to one theorem
(there are no paths — there is one named cite).

## See also

- `acceleration.md` — the trust boundary per word, and where `model` sits among the
  accelerated tactics.
- `namespaces.md` — the `{model, theory}` namespace concept built on this.
- `../GUIDE.md` — the language reference.
