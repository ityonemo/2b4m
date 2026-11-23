# Guarding implicit definitions — the form already exists and is unchecked

**Scope correction, up front.** An earlier draft of this plan described adding an implicit
definition form. That was wrong: the form is already in the language, already accepted by the
parser, and already used 30 times in `std/`. `stageDefinitionAxiom` (`parser.zig:1107`) stages
a clause "exactly as written" without inspecting its left-hand side, so a clause whose defined
symbol sits inside the condition is staged as an axiom with no further question asked.

This plan therefore adds no syntax. It adds the **obligations that form should have carried
from the start**, and it is a migration of 30 existing clauses rather than a new feature.

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
condition, so there is no rewrite direction.

**2b4m already accepts this — unguarded.** `stageDefinitionAxiom` (`parser.zig:1107`) stages
"the axiom is the clause exactly as written": it collects the clause's free variables,
quantifies them, and stages the formula verbatim. It never inspects the left-hand side. So an
implicit definition parses today and is used 30 times in `std/`.

**This plan therefore CONSTRAINS an existing form rather than adding one.** The hard part —
expressing an implicit definition — is built and in production. What is missing is the guard.

The alternative today is to write it as a plain axiom:

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

All three are writable today. The problem is that **B and C share one syntax with one set of
checks** — the block form accepts either and demands only `consistency:`, which is the wrong
obligation for B — so an implicit definition is accepted with no existence check and reported
as carrying no assumption.

The difference between A and B is not stylistic. `mul` means *whatever satisfies* the ring
axioms — many functions do, and that is the point of an abstract theory. `recip` means *the*
inverse: in a field the inverse exists and is unique, so `fieldInverse` pins the symbol down
completely. That uniqueness is a THEOREM, not something the axiom states, which is exactly why
the current form cannot claim definitional status honestly.

## The rule: dispatch on whether the LHS is an l-value

**No new keyword.** The existing definition block carries both cases, and which one it is
follows from the clause's shape:

| the clause's LHS | kind | eliminable | obligations |
|---|---|---|---|
| `f(args)` **alone** — an l-value | explicit | yes, rewrite left-to-right | `consistency:`, one per clause pair |
| anything else, with `f` inside the condition — **not an l-value** | implicit | no | **`existence:` + `uniqueness:`** |

`f(Z) = Z` has `f(Z)` as an l-value: rewrite and `f` is gone. `mul(a, recip(a)) = ONE` has
`mul(…)` on the left with `recip` buried inside — there is no position to rewrite from.

The test is purely syntactic (is the LHS an application of the symbol being defined, to
distinct binders), so it is decidable at parse time. That is the same kind of structural read
the clause already performs for arity and arm count — not a naming coupling, since it inspects
the shape of what was written rather than how it was spelled.

```2b4m
oper recip(a: Field) => Field requires nonzero(a):
  mul(a, recip(a)) = ONE.
  existence: everyNonzeroHasAnInverse,
  uniqueness: inversesAreUnique
```

Punctuation follows the explicit block exactly: the clause ends with `.`, then a
comma-separated obligation list. `existence` and `uniqueness` are plain identifiers, as
`consistency` already is (`parser.zig:1064`).

**Both obligations are REQUIRED**, and they are what make this a definition rather than an
assumption:

- **existence** — without it the symbol may denote nothing. Not hypothetical: see
  PAINPOINTS 16f, where the absence of this check lets a user derive `ZERO = ONE`.
- **uniqueness** — without it the property picks out a SET of candidates, so the symbol is
  underdetermined. That is an axiom's job, not a definition's.

### A BARE `oper` plus axioms is untouched — this is the load-bearing invariant

**Nothing here applies to a declaration with no definition block.** The dispatch happens
INSIDE a block (`oper f(…):` followed by clauses); an `oper` declared bare and constrained by
separately-named axioms is case A, is correct as it stands, and must keep working unchanged:

```2b4m
oper add(a: Ring, b: Ring) => Ring          // no block — nothing to dispatch on
oper mul(a: Ring, b: Ring) => Ring

axiom mulIsAssociative:  forall a, b, c: Ring; mul(mul(a, b), c) = mul(a, mul(b, c))
axiom mulAddDistribLeft: forall a, b, c: Ring; mul(a, add(b, c)) = add(mul(a, b), mul(a, c))
```

`mul` here is a PRIMITIVE. It means whatever satisfies the ring axioms — many functions do,
and that is the entire point of an abstract theory. There is no existence obligation to
discharge (the theory asserts such an operation, that is what an axiomatization IS) and no
uniqueness claim to make (there had better not be one; `Ring` has many models).

So the rule must not be read as "an `oper` with facts about it owes obligations". It is: **a
DEFINITION BLOCK whose clause is not an l-value owes obligations.** An axiom stated about a
bare declaration is not a definition block and never becomes one.

This is also why the existing `--axioms` behaviour for case A is RIGHT rather than a
companion bug to 16f: `mulIsAssociative` genuinely is an assumption, and reporting it as one
is the honest answer.

### Why mandatory obligations also fix typos

Dispatching on shape raises the worry that a typo could silently move a clause between
regimes. It cannot, *because the obligations are mandatory*: fat-finger an explicit clause into
a non-l-value shape and the error is "this needs existence and uniqueness", which names the
real problem — what was written is not the definition that was meant. The requirement is the
typo detector.

## What it buys

1. **`--axioms` stops miscounting.** `fieldInverse` is currently an assumption in every
   dependency report that reaches a field. Under this form it is a definition, and the two
   obligations are theorems — so the assumption count drops by one and gains nothing, which is
   the correct accounting.

2. **The status is CHECKED, not asserted.** The claim "this is a definition" has content,
   because existence and uniqueness are discharged. A `definition` keyword was considered and
   REJECTED for exactly this reason: its tier would have been self-asserted and unverifiable,
   so it would have added a way to say "do not count this" without a way to earn it.

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

This matters for sequencing: fixing 16 dissolves BOTH the pred cases and the 16e cases. What
remains is the `oper` implicit case — which is writable today and merely unguarded, and is
what this plan is for.

## Relationship to the other plans, and to PAINPOINTS 16

**There is no `definition` keyword, and 16e does not need one.** The two axioms that motivated
16e (`shared/vocabulary.b4m:118`) are l-value shaped —
`noZerosRightOfTheCriticalLine() iff …` — so they are EXPLICIT definitions that merely could
not use the block form, because a clause cannot infer `r`'s sort under the `forall`
(PAINPOINTS 16). Fix 16 and they become blocks, reported `— DEFINITION` automatically.

So the work splits cleanly:

| | fixes | how |
|---|---|---|
| **PAINPOINTS 16** (sort inference under a quantifier) | 16e, and the `pred` cases that fall back to `define` | elaboration change |
| **this plan** | 16f — the implicit form is writable today but unguarded | parse-time validation + obligation check |

`DEFINITION-SOUNDNESS-PLAN.md` owns clause-overlap consistency and structural-decrease
termination for the explicit case. This plan's existence/uniqueness pair is the implicit-case
analogue of its `consistency:`, and should follow its build order and its ruling that a failed
check is an error rather than a downgrade.

## The obligations' shapes, worked out

### Single clause — mechanical

```2b4m
oper recip(a: Field) => Field requires nonzero(a):
  mul(a, recip(a)) = ONE.
```

Replace the defining application `recip(a)` by a fresh variable, then quantify: params to the
outer `forall`, guard to the antecedent, result sort to the fresh variable.

```2b4m
existence:  forall a: Field; nonzero(a) -> exists y: Field; mul(a, y) = ONE
uniqueness: forall a: Field; forall y, z: Field;
              nonzero(a) -> mul(a, y) = ONE -> mul(a, z) = ONE -> y = z
```

### Multi-clause — the clauses CONJOIN, and the binders are two-tiered

`rmonomial`'s two clauses are ONE definition split by a case on the index, so they must be
conjoined under a single `exists`:

```2b4m
existence:  forall a: Real; forall k: Nat;
              exists y: RPoly; rcoeff(y, k) = a
                and (forall i: Nat; (not (i = k)) -> rcoeff(y, i) = ZERO)

uniqueness: forall a: Real; forall k: Nat; forall y, z: RPoly;
              <y satisfies both clauses> -> <z satisfies both clauses> -> y = z
```

**Note where `i` binds.** In the clause it is a free variable, implicitly universal over that
clause. In the obligation it must bind INSIDE the `exists y`, because `y` must satisfy the
condition for every `i`. Bind it outside and the obligation is weaker and wrong — it would
only ask for a polynomial that works at one index.

So the synthesis needs **two binder tiers**: declared params outside the `exists`,
clause-local variables inside.

### What is reusable, and what is not

`parser.zig`'s `consistency:` synthesizer already has three of the four pieces:

| | | |
|---|---|---|
| `collectClauseVars` (`:510`) | finds clause-local variables | reusable — it would find `i` |
| the param-override loop (`:511-518`) | gives a declared param its DECLARED sort, not `inferred` | reusable, and necessary: the comment records that an inferred param with no defining application to pin it fails with "cannot infer the sort of 'u'" |
| `antecedentOf(c.body)` (`:520`) | extracts an implication guard | reusable — it is exactly `rmonomial`'s second clause |
| `conditionOf`'s FLAT binder list | one outer `forall` for everything | **not reusable** — the implicit case needs the two tiers above |

And the obligation structure differs: `consistency:` is PAIRWISE (one per unordered clause
pair, `synthesizeObligations:437-447`), while the implicit case conjoins ALL clauses into one
existence and one uniqueness. So this needs its own synthesizer rather than a parameter on the
existing one.

A consequence worth noting: `uniqueness` repeats the whole conjoined condition twice, once per
candidate. For `rmonomial` that is already unwieldy to write by hand, which argues for the
checker stating the obligation and verifying the author's named theorem matches — the
`collectConsistencyGaps` pattern — rather than expecting it typed out.

## How the corpus handles this today — and what it tells the design

`std/real/polynomial.b4m` has five implicit definitions and handles them like this:

```2b4m
oper rmonomial(a: Real, k: Nat) => RPoly:
  rcoeff(rmonomial(a, k), k) = a;
  (not (i = k)) -> rcoeff(rmonomial(a, k), i) = ZERO.

axiom rPolyExtensionality: forall p, q: RPoly;                      // line 45
  (forall i: Nat; rcoeff(p, i) = rcoeff(q, i)) -> p = q
```

| | how it is handled today |
|---|---|
| the definition | block form, implicit (symbol inside the condition) |
| **uniqueness** | `rPolyExtensionality` — **generic, one axiom serving all five definitions** |
| **existence** | **absent** — probed: no `exists … Poly` claim in either polynomial layer |

Two consequences, both of which make the plan cheaper and better shaped than drafted above.

**1. Uniqueness is already corpus practice, just unlinked.** `rPolyExtensionality` is not about
`rmonomial`; it says any two polynomials with equal coefficients are equal, which supplies
uniqueness for `raddP`, `rnegP`, `rmulP`, `rmonomial` and `RZEROP` at once. So requiring
`uniqueness:` largely FORMALIZES AN EXISTING CONVENTION rather than demanding new proofs.

**2. Existence is the genuinely missing obligation**, and it is where the 16f exposure sits in
real code. `rcoeff(rmonomial(a,k), k) = a` is ASSERTED by the clause, not derived from "a
polynomial with these coefficients exists". That is structurally identical to the `natRecip`
repro — the same unguarded construction, with a true conclusion instead of a false one.

### Design consequence: the obligations must accept a GENERIC fact

If `existence:` / `uniqueness:` had to name a theorem about THIS definition, the polynomial
family would need five near-identical pairs. `rPolyExtensionality` shows the natural unit is
**per-sort, not per-definition**.

So the obligation should accept a generic fact and have the checker verify it IMPLIES the
specific instance, rather than demanding a bespoke theorem per definition:

```2b4m
oper rmonomial(a: Real, k: Nat) => RPoly:
  rcoeff(rmonomial(a, k), k) = a;
  (not (i = k)) -> rcoeff(rmonomial(a, k), i) = ZERO.
  existence: aMonomialExists,
  uniqueness: rPolyExtensionality        // the SAME fact all five cite
```

That makes the migration: one new existence fact per implicit definition (genuinely new
mathematics, and genuinely missing today), plus one shared uniqueness citation per sort. Not
30 pairs.

**Open:** whether "implies the specific instance" is checked by α-equivalence after
instantiation (as `collectConsistencyGaps` does) or needs real inference. Extensionality
instantiated at `y` and `z` gives uniqueness directly, so α-match may suffice — verify on
`rmonomial` before committing to it.

## Settled by probing

1. **How the clause publishes.** As the explicit case does: `InternPool.definitionClauseName`
   mangles `definition{symbol}{arm}` (`InternPool.zig:938`), which is unreachable from source,
   so it is cited positionally with `[by definition(0) recip]` rather than by name. The
   implicit form needs no new publication mechanism — same mangling, same citation syntax.

   **Migration consequence, and it is the blocking one:** 15 files under `std/` cite
   `fieldInverse` by name. Converting it means either keeping `fact fieldInverse = …` as an
   alias, or editing 15 files. Settle before touching `std`.

2. **The obligations' required shapes.** Both are mechanically derivable from the clause, so
   the checker states them and verifies the named theorem matches — exactly as `--library`
   already checks a `consistency:` theorem states its pair's obligation
   (`root.zig:collectConsistencyGaps`). Accepting any theorem the author names would make the
   obligation decorative.

   - existence: `forall <params>; <guard> -> exists y: <result>; <clause with f(params) := y>`
   - uniqueness: `forall <params>; forall y, z: <result>; <guard> -> <clause[y]> -> <clause[z]> -> y = z`

   Note both are stated about the PROPERTY, not about `f` — they must be, or they are circular.

3. **Guards are not subsumed.** `requires nonzero(a)` stays on the declaration and appears as
   the antecedent of both obligations. Stating it twice is the honest cost: the guard governs
   where `f` may be WRITTEN, the obligations govern whether it DENOTES, and those are different
   claims that happen to coincide here.

4. **The explicit form is unchanged.** It is the eliminable case, and it is what `simplify` and
   `definition(N)` citations rewrite with. This adds a second regime to the same syntax; it
   replaces nothing.

## Still open

- **What the clause-shape test accepts exactly.** "LHS is an application of the defined symbol
  to distinct binders" is the intent. Edge cases to pin down, each present in the corpus or
  trivially reachable:
  - **structural recursion**: `f(s(n)) = s(f(n))` has the symbol on both sides but the LHS IS
    an l-value, so it must stay EXPLICIT. The test is about the left side only.
  - **`rmonomial` — the hardest real case** (`std/real/polynomial.b4m:35`): TWO implicit
    clauses, the second guarded by an implication rather than `when`, and no `consistency:`
    declared.

        oper rmonomial(a: Real, k: Nat) => RPoly:
          rcoeff(rmonomial(a, k), k) = a;
          (not (i = k)) -> rcoeff(rmonomial(a, k), i) = ZERO.

    This is a single implicit definition SPLIT ACROSS TWO CLAUSES by a case on the index, so
    existence and uniqueness are owed once for the pair, not once per clause — and the
    existing pairwise `consistency:` shape does not fit. **Design against this case**; a rule
    that handles only one implicit clause per symbol would fail the corpus on day one.
  - whether a block may MIX l-value and non-l-value clauses (nothing in the corpus does).
- **Whether `--library` should reject an implicit definition whose obligations are unproved**,
  or whether plain `check` should. The `consistency:` precedent puts the STATEMENT check in
  `--library` but discharges the obligation in the normal proof flow, which suggests the same
  split here.

## The corpus already does this, 30 times

Not greenfield. A scan for non-l-value clauses finds **30 in `std/`**, concentrated in the
polynomial layers:

    oper raddP(p: RPoly, q: RPoly) => RPoly:
      rcoeff(raddP(p, q), i) = real.add(rcoeff(p, i), rcoeff(q, i)).

`raddP(p,q)` is characterized by its coefficients, not given by a rewrite — a textbook
implicit definition. They are sound, and for the right reason: each needs a polynomial to be
determined by its coefficient sequence, which IS the uniqueness obligation, and the corpus
states it as `polyExtensionality` (`std/ring/polynomial.b4m:84`). Existence holds because every
coefficient sequence of the right shape has a polynomial.

So the practice is already correct — but by CONVENTION, not enforcement. Nothing links a
clause to the axiom that licenses it, and nothing would complain if one were written without.

**Two consequences for this plan.** First, these are not evidence the form is WANTED — they
are existing USERS of it, since the parser already accepts any clause. Requiring obligations
breaks all 30 until each names them, so this is a migration, not an addition. Second, the cost
is well under 30 proofs: the polynomial family shares one `polyExtensionality`-shaped
uniqueness fact per sort, so what is genuinely new is the existence fact per definition.

## Candidates: `oper`s that ARE implicit definitions but are written as axioms

Scanned `std/` for the shape "a bare `oper` plus an axiom that pins it down". The clean family
is **inverse-of-a-binary-op-gives-the-unit**, which is unambiguous: the axiom determines the
symbol (inverses are unique where they exist), the symbol appears once, and the equation is
exactly the characterizing property.

| symbol | sites | axiom shape |
|---|---|---|
| `recip` | 5 — `field`, `field/order`, `real`, `rational`, `complex` | `nonzero(a) -> mul(a, recip(a)) = ONE` |
| `neg` | 6 — `ring`, `field`, `field/order`, `real`, `rational`, `complex` | `add(neg(a), a) = ZERO` |
| `inverse` | 4 — `function` (×2, guarded), `group`, `group/size` | `op(inverse(a), a) = E` |
| `invG`/`invH`/`invK`/`invHH` | 9 — the group chapter's per-letter copies | `opG(invG(a), a) = EG` |
| `negS`/`negA`/`negB`/`negC` | 4 — the ring-isomorphism chapter's copies | `addS(negS(a), a) = zeroS` |
| `unitInverse` | 1 — `integer/mod-n` | `mul(unitInverse(x), x) = ONE` |
| `phi`/`psi`/`chi`/`chiInv`/`phiInv` | 8 — isomorphism inverse pairs | `psi(phi(a)) = a` |

**~37 sites, but far fewer distinct facts** — most are per-letter restatements of the same
theorem in chapter files, which the no-parameterized-sorts constraint forces
([[order-family-inherited]] is the worked precedent for that shape).

### Three caveats on this list

1. **ABSTRACT theories convert too — existence may be an AXIOM.** An earlier draft of this
   plan claimed `neg` on a `Ring` was not a candidate, on the reasoning that `addNegLeft` IS
   the existence postulate so there is nothing to prove it from. **That was wrong**, and the
   error was conflating two different things:

   - *is `neg` determined by `add(neg(a), a) = ZERO`?* — **yes**, and provably: the group
     uniqueness argument needs only associativity and identity. It is already a theorem,
     `group.inverseUnique` (`std/group.b4m:198`): `op(a, b) = E -> b = inverse(a)`.
   - *does an inverse exist?* — that is the postulate.

   Nothing in this design requires existence to be a THEOREM. The obligations demand both
   facts be STATED and discharged; an abstract theory discharges existence with an axiom of
   its own:

   ```2b4m
   axiom additiveInversesExist: forall a: Ring; exists y: Ring; add(y, a) = ZERO
   ```

   **And the conversion is an improvement, not a formality.** `addNegLeft` currently FUSES two
   claims: "inverses exist" and "`neg` is one of them". Splitting them means `--axioms` reports
   the existence postulate — which genuinely is an assumption a reader should weigh — while
   `neg`'s characterization becomes a definition. Today both hide inside one axiom labelled as
   a single assumption.

   So the concrete/abstract distinction governs WHERE existence comes from (a construction vs.
   a postulate), not whether the conversion is available.

2. **`succ`/`prev` are false positives.** `prevSucc: prev(succ(n)) = n` matched the pattern,
   but these are CONSTRUCTORS — `succ` is primitive and `prevSucc` constrains `prev` against
   it. Neither is implicitly defined.

3. **The isomorphism pairs are mutual.** `psiAfterPhi` and `phiAfterPsi` together say `psi` is
   `phi`'s two-sided inverse. Converting either alone would be wrong; the pair defines `psi`
   FROM `phi` (or vice versa), so the direction has to be chosen, and the other axiom then
   becomes a theorem.

### The realistic first conversion

**`recip` on a CONCRETE field — ℝ, ℚ, or ℂ — is the right first case.** And the uniqueness
half is already done: `recipIsUnique` (`std/field/units.b4m:307`) proves
`mul(a, b) = ONE -> b = recip(a)`, via `group.inverseUnique` through the `UnitsGroup` model.
So a conversion would cite an existing theorem rather than needing a new one — which is the
same shape as `rPolyExtensionality` serving all five polynomial definitions.

What is genuinely missing is EXISTENCE, as with the polynomial family. For a concrete field
that is provable from the construction; for an abstract one it is the postulate itself.

**`std/field.b4m` converts too**, contrary to an earlier draft here: its `fieldInverse` is an
abstract postulate, but per caveat 1 that only means existence is discharged by an axiom
rather than a construction. The conversion still separates "inverses exist" from "`recip` is
the inverse", which is the gain.

And note the migration cost measured earlier: 15 files under `std/` cite `fieldInverse` by
name, so even the concrete conversions need the naming question settled first.

## Not in scope

- Deciding whether an implicit definition is CONSERVATIVE (that adding it proves no new
  theorems in the old vocabulary). It is, given existence and uniqueness — that is the standard
  result — but 2b4m does not currently reason about its own conservativity and should not start
  here.
- Migrating `std`. The form must exist, be gated, and have the naming question settled first.
  `fieldInverse` is the obvious first case, and **15 files under `std/` cite it**, so it is the
  wrong thing to convert on day one.
