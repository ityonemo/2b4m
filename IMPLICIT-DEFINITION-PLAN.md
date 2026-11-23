# `definition … where` — implicit definition by characterizing property

A symbol can be *defined* in two ways, and 2b4m only supports one of them.

**Explicitly**, by a rewrite: the symbol stands alone on the left, and the right mentions it
only structurally. This is the existing definition block, and it is what makes the symbol
ELIMINABLE — rewrite left-to-right and it disappears.

```2b4m
pred nonzero(a: Field):
  nonzero(a) iff (not (a = ZERO)).           // nonzero(a) ≡ a formula without nonzero

oper f(n: N) => N:
  f(Z) = Z;                                   // f(Z) → Z
  f(s(n)) = s(f(n)).
```

**Implicitly**, by a property the value uniquely satisfies. The symbol appears INSIDE the
condition, so there is no rewrite direction — and 2b4m has no form for this at all. Today it
must be written as an axiom:

```2b4m
oper recip(a: Field) => Field requires nonzero(a)
axiom fieldInverse: forall a: Field; nonzero(a) -> mul(a, recip(a)) = ONE
```

## Why that axiom is the wrong shape

`fieldInverse` reads as an assumption and is counted as one, and in the strict sense that is
right — it is not eliminable, so it is not an explicit definition. But it is not an assumption
of the same kind as `mulIsAssociative` either. The three relationships a symbol can have to
the facts about it:

| | example | what the fact does | eliminable |
|---|---|---|---|
| **A. primitive, constrained** | `oper mul` + `mulIsAssociative`, `mulAddDistribLeft`, … | constrains; many axioms, none determines a value | no |
| **B. implicitly defined** | `oper recip` + `fieldInverse` | characterizes a value that EXISTS and is UNIQUE | no — but determined |
| **C. explicitly defined** | `pred nonzero(a): … iff …` | gives the value | **yes** |

A and C have forms. **B does not**, so it borrows A's, and the report cannot tell them apart.

The difference between A and B is not stylistic. `mul` means *whatever satisfies* the ring
axioms — many functions do, and that is the point of an abstract theory. `recip` means *the*
inverse: in a field the inverse exists and is unique, so `fieldInverse` pins the symbol down
completely. That uniqueness is a THEOREM, not something the axiom states, which is exactly why
the current form cannot claim definitional status honestly.

## The proposed form

```2b4m
oper recip(a: Field) => Field requires nonzero(a)

definition recip(a) where mul(a, recip(a)) = ONE.
  existence: everyNonzeroHasAnInverse,
  uniqueness: inversesAreUnique
```

Read: *`recip(a)` is the value satisfying `mul(a, recip(a)) = ONE`; here is the proof it
exists, and the proof it is unique.*

**Punctuation follows the existing definition block**: the characterizing property ends with
`.`, then the obligations as a `name: theorem` list, comma-separated — the same shape as
`consistency:` after a clause list. `consistency` is already a plain identifier rather than
reserved vocabulary (`parser.zig:1064`), and `existence` / `uniqueness` should be too.

**The obligations are the whole point, and both are REQUIRED.** They are what make this a
definition rather than an assumption:

- **existence** — without it the symbol may denote nothing, and the "definition" is vacuous
  or inconsistent.
- **uniqueness** — without it the property picks out a SET of candidate values, so the symbol
  is underdetermined. That is case A, not case B, and should be written as an axiom.

A `definition … where` whose obligations are absent or unproved is an ERROR, not a downgrade.
This is the same discipline `consistency:` applies to multi-clause blocks, and the same reason:
the status is only honest if the thing was checked.

## What it buys

1. **`--axioms` stops miscounting.** `fieldInverse` is currently an assumption in every
   dependency report that reaches a field. Under this form it is a definition, and the two
   obligations are theorems — so the assumption count drops by one and gains nothing, which is
   the correct accounting.

2. **The status is CHECKED, not asserted.** This is the substantive difference from
   `DEFINITION-KEYWORD-STATUS-PLAN.md`, which proposes a `definition` keyword whose tier is
   self-asserted and unverifiable. Here the claim "this is a definition" has content: existence
   and uniqueness are discharged. **If both plans land, this is the better one** — and it may
   make the other unnecessary, see below.

3. **It says what the author means.** A reader at `oper recip` currently sees a bare
   declaration and must hunt for `fieldInverse` to learn what `recip` is. The form keeps the
   characterization adjacent to the symbol, as the explicit block does.

4. **Guards compose.** `requires nonzero(a)` already restricts where `recip` can be written;
   the existence obligation is naturally proved under the same guard. Nothing new is needed —
   but see the open questions.

## Is there a parallel construction for `pred`? No — and the reason is instructive

**No**, and not because preds are simpler: because an implicit definition's two obligations
are both FREE for a predicate.

- **Existence** is free. A predicate is total — `p(x)` is true or false at every `x`, with
  nothing to construct. An `oper` must exhibit an inhabitant of its result sort; a `pred`
  denotes into Prop, which is two-valued and always inhabited.
- **Uniqueness** is automatic. A condition on the proposition `p(x)` determines it pointwise.

So any condition that pins a predicate down can be SOLVED for `p(x)` and written as an `iff` —
which is the explicit block. A condition that cannot be so solved (`p(x) -> Q(x)` with no
converse) leaves `p` underdetermined, which is case A and belongs as an axiom. There is no
middle case for the new form to occupy.

`std/real.b4m`'s `less_than` is the case-A example: six axioms (irreflexive, transitive,
trichotomy, add-right, add-cancel, …) constrain it and none determines it — many relations
satisfy them, which is the point of an ordered-field axiomatization.

**Caveat worth recording:** this argument uses classical logic with total predicates, which is
what 2b4m has. Were predicates partial, or the logic intuitionistic, case B would open up for
preds too and this section would need revisiting.

### But preds DO hit a wall — a different one

Predicates fail to use the block form regularly, and existentials are the trigger:

```2b4m
pred divides(d: T, n: T):
  divides(d, n) iff (exists k: K; n = mul(d, k)).
  // error: cannot infer the sort of 'k'
```

That is why `std/divisibility.b4m:23` uses a `define` macro instead. But this is NOT the
implicit case — the body IS `iff`-shaped and IS eliminable, so it is a perfectly explicit
definition the checker merely cannot type. **It is PAINPOINTS 16**, and the binder is even
annotated (`k: K`); the inferencer just does not use the annotation.

This matters for sequencing: fixing 16 dissolves BOTH the pred cases and the 16e cases
(`DEFINITION-KEYWORD-STATUS-PLAN.md`). What remains genuinely unaddressable by any existing
form is only the `oper` implicit case — which is what this plan is for.

## Relationship to the other two plans

- **`DEFINITION-KEYWORD-STATUS-PLAN.md`** (PAINPOINTS 16e) proposes a bare `definition
  <name>: <formula>` for content that IS explicit but cannot use the block form, because a
  clause cannot infer a bound variable's sort under a quantifier (PAINPOINTS 16). That is a
  different case from this one and the two do not overlap. **But if PAINPOINTS 16 is fixed,
  that plan dissolves and only this one is needed** — which argues for doing 16 and this,
  rather than 16e.
- **`DEFINITION-SOUNDNESS-PLAN.md`** owns clause-overlap consistency and structural-decrease
  termination for EXPLICIT blocks. This plan's existence/uniqueness pair is the implicit-case
  analogue of that file's `consistency:`, and should follow its build order and its ruling that
  a failed check is an error rather than a downgrade.

## Open questions — settle before building

1. **Does the characterizing property still generate a citable fact, and under what name?**
   Today proofs cite `fieldInverse` directly (`std/field.b4m:74`, and widely downstream). The
   form must either keep that name available or the migration breaks every consumer. Proposal:
   the property IS the fact, named as the definition names it — i.e. `definition recip … `
   publishes under a derived name the way a block clause does (`definition-recip-0`), with the
   old name kept as a `fact` alias during migration. **Needs a decision before any std edit.**

2. **Is `uniqueness` provable before the symbol exists?** `inversesAreUnique` would be stated
   about the PROPERTY (`mul(a,y) = ONE and mul(a,z) = ONE -> y = z`), not about `recip` — it
   must be, or it is circular. The form should probably REQUIRE that shape rather than accept
   any theorem the author names, which is a stronger check than `consistency:` applies.

3. **What exactly does existence have to say?** `exists y: Field; mul(a, y) = ONE`, under the
   guard, universally quantified over `a`. Mechanically derivable from the `where` clause, so
   the checker can state the obligation itself and verify the named theorem matches — the way
   `--library` already checks a `consistency:` theorem states its pair's obligation
   (`root.zig:collectConsistencyGaps`).

4. **Should this subsume `requires`?** An implicit definition and a guard are closely related
   — `recip` is defined exactly where `nonzero(a)` holds. Keeping them separate is simpler and
   matches the current declaration, but it means the guard is stated twice (once on the `oper`,
   once in the existence theorem's antecedent).

5. **Does the explicit block form stay?** Yes — it is the eliminable case and it is what
   `simplify` and `definition(N)` citations rewrite with. This adds a second form; it replaces
   nothing.

## Not in scope

- Deciding whether an implicit definition is CONSERVATIVE (that adding it proves no new
  theorems in the old vocabulary). It is, given existence and uniqueness — that is the standard
  result — but 2b4m does not currently reason about its own conservativity and should not start
  here.
- Migrating `std`. The form must exist, be gated, and have the naming question settled first.
  `fieldInverse` is the obvious first case, and **15 files under `std/` cite it**, so it is the
  wrong thing to convert on day one.
