# Definition well-formedness — the `consistency:` obligation

**Status: DESIGNED 2026-11-18, not built.** Supersedes the "OPEN: a SOUNDNESS CHECK on
definitions" section of `DEFINITION-KEYWORD-PLAN`, which was written against a wrong model of
the corpus (it assumed guards needing decision procedures) and conflated two independent
properties.

## THE FRAMING (user ruling 2026-11-18)

**An unsound definition is a USER ERROR, not a kernel soundness issue.** The kernel did
nothing wrong: it faithfully derived consequences from assumptions the author asserted. An
inconsistent definition block is the same category as writing `axiom everythingIsEqual`.

So the goal is not a proof-theoretic guarantee — it is making the error EASY TO NOTICE, and
making the choice of form carry semantic weight: a definition block gets CHECKED, a
hand-written axiom pair does not.

Disclosure already works today and is not the gap: `--axioms` names both offending clauses
with file and line, labelled `— DEFINITION`. Probed with a proof of `Z = s(Z)`.

## TWO INDEPENDENT PROPERTIES (do not conflate — this plan covers only the first)

| property | about | clause count |
|---|---|---|
| **consistency** | the RELATIONSHIP between clauses: do two that both apply agree? | one clause ⇒ free |
| **well-foundedness** | ONE clause in isolation: does its recursive call decrease? | irrelevant |

All four combinations occur. Both hazards were demonstrated against the live checker:

- pure overlap, no recursion: `f(n) = Z when n = Z` beside unguarded `f(n) = s(Z)` proves
  `Z = s(Z)` in 8 kernel-checked steps, exit 0.
- pure non-well-foundedness, one clause: `g(n) = s(g(n))` plus only `sNoFixedPoint` proves
  `Z = s(Z)`.

A single clause therefore needs NO consistency check but STILL needs well-foundedness.

## THE OBLIGATION

For a block with clauses `0..n`, one obligation per unordered pair, in lexicographic index
order — `(0,1), (0,2), … (1,2), (1,3), … (2,3) …`. Each is its OWN theorem:

    (cond_i and cond_j) -> rhs_i = rhs_j

**PER-PAIR, not one conjunction** (user ruling 2026-11-19, superseding the earlier
"conjunction of all pairs"). Two reasons, and the second is the one that matters:

1. The statement stays short — n(n-1)/2 conjuncts become n(n-1)/2 separate statements, each
   quantifying only the variables ITS pair mentions rather than the union over all pairs.
2. **It makes PARTIAL application possible.** A conjunctive theorem forces the author to prove
   every pair in one proof, so a single hard pair drags the trivial ones into hand-written
   scaffolding — the opposite of what the tactic is for.

**Conditions conjoined with `and`, one flat clause** (user ruling): not nested implications.
That is the shape the author reads and the tactics handle.

**NO syntactic exemption.** "Constructor-disjoint" is not a license to skip the obligation —
only the usual REASON it discharges easily. This is what closes the model-collapse hole the
user raised: `f(FOO) = FOO; f(BAR) = BAR` looks disjoint, but a model may map both `FOO` and
`BAR` onto one target constant. Carrying the obligation makes that sound automatically — the
obligation becomes `ONLY = ONLY` under the mapping, and a transfer re-proves the body, so
there is no gap between "checked in the source" and "true in the target".

### The obligations rest on ONE disequality axiom, and REUSE collapses them

**Corrected 2026-11-18 by probe.** An earlier draft of this plan claimed the obligations rest
on NO axioms. That was measured on a bad probe whose consequent (`Z = s(m)`) was itself
derivable from the hypothesis by rewriting. REAL obligations have unrelated right-hand sides,
so the contradiction in the hypothesis must actually be USED:

    forall a: Complex; forall k, n: Nat;
      (k = ZERO and k = succ(n)) -> ONE = mul(a, cpower(a, n))

`ONE` and `mul(a, cpower(a, n))` are unrelated, so rewriting cannot close this and `tautology`
declines with a countermodel. All 66 recursion obligations rest on `succNotZero` — which IS
reachable everywhere (every ZERO/succ-splitting block imports peano; verified, 0 exceptions).

**The collapse: ONE shared schema per constructor pair.** Verified end to end — three
theorems, one axiom:

```2b4m
// (1) the theory-specific core. The ONLY place succNotZero appears.
theorem noNatIsZeroAndSucc: forall k, n: Nat; not (k = ZERO and k = succ(n))

// (2) the reusable schema: turn that into ANY consequent, via ex_falso.
theorem splitVacuous(prop(Nat, Nat)): forall k, n: Nat;
  (k = ZERO and k = succ(n)) -> prop(k, n)

// (3) each of the 66 obligations: ONE step.
[using instantiation splitVacuous((fun kk, nn: Nat => <rhs_i> = <rhs_j>))]
```

So the cost is ~75 lines written ONCE plus one short theorem per block, not ~2,900 lines of
duplicated scaffolding. (The 2,900 estimate — 72 blocks, 2-6 binders, mean 4.3, at
`14 + 6 x binders` — is what hand-proving would cost, and is the reason a tactic is not
optional.)

**`prop` MUST take both variables.** With a single argument the instantiation fails
(`reference not found: 'n'`), because every one of the 66 consequents mentions the recursion
variable — inevitably, since that is what recursion IS. Measured: 66 of 66.

### ARM ORDER IS IMMATERIAL (so the canonical order is free to choose)

Pair `(i,j)` and `(j,i)` differ only in which RHS lands on which side of the equation.
Verified: the flipped obligation discharges by the SAME shared schema, with the equation
flipped inside `prop`, in one step. So the generator emits each unordered pair ONCE, in
lexicographic index order, and nothing is lost.

### THE TACTIC IS THIN, AND THE THEOREM STAYS NAMED

`consistency:` still names a REAL theorem (user ruling) — what the tactic buys is that in the
trivial cases its proof is ONE LINE:

```2b4m
oper cpower(a: Complex, n: Nat) => Complex:
  cpower(a, ZERO) = ONE;
  cpower(a, succ(n)) = mul(a, cpower(a, n)).
  consistency: cpowerConsistent

theorem cpowerConsistent: forall a: Complex; forall k, n: Nat;
  (k = ZERO and k = succ(n)) -> ONE = mul(a, cpower(a, n))
proof
  @conclusion |
    forall a: Complex; forall k, n: Nat;
      (k = ZERO and k = succ(n)) -> ONE = mul(a, cpower(a, n))
    [using definition_consistency]
qed
```

The STATEMENT is written out — it is the synthesized obligation and must match exactly — and
the PROOF is one accelerant step, like any `[using model(…) thm]` transfer.

**The word must open the outer binders itself.** A bare `[using instantiation splitVacuous(…)]`
CANNOT close the goal: the non-matched param `a` is bound by the goal's own `forall`, so it is
not in scope at the step (`reference not found: 'a'`), and the hand proof needed a `fix a` /
`generalize` wrapper around the instantiation. The precedent is exact: `simplify_quantified`
closes `forall p, q: Pair; fst(prodOp(p, q)) = opG(fst(p), fst(q))` in ONE step
(`std/group/product.b4m:101`), doing the binder-opening internally and emitting the whole
relativized proof as its certificate. The consistency word is the same shape.

The certificate is a kernel step, always producible (a schema lookup, not a search), so the
word never declines and `--fast` trust buys nothing.

## SYNTAX

The clause list is terminated by `.`, which SEPARATES the clauses (and their `when` guards)
from the well-formedness declarations that follow:

```2b4m
oper gcd(a: Nat, b: Nat) => Nat:
  gcd(a, b) = a                  when b = ZERO;
  gcd(a, b) = gcd(b, mod(a, b))  when b != ZERO.
  consistency: gcdClausesAgree
```

- **Required on multi-clause blocks** (user ruling), absent on single-clause ones.
- **`consistency:` takes a LIST, one entry per pair in canonical order.** A NAME points that
  pair at a theorem the author wrote; `_` says "discharge it with the tactic". So application
  is PARTIAL per pair, and the pairs that need a real argument are pointed at specific
  theorems (user requirement 2026-11-19):

      consistency: swapOverlapAgrees, _, _

  Every position is written out even when automatic, so a reader sees how many pairs exist
  and a miscount is an error rather than a silent default.
- The period also makes room for the second property without re-opening the syntax
  (`termination: <name>`), and improves the dropped-`;` diagnostic: today a missing semicolon
  reports "expected a declaration, got 'f'" at the orphaned clause instead of naming the
  real mistake.
- **Breaking change to all 112 existing blocks** — accepted by the user; mechanical, and
  `2b4m fmt` can apply it.

### The named theorem must MATCH a checker-synthesized statement

User ruling: same contract as a `model`'s `<-`. The checker states the obligation; the named
theorem must match it; a mismatch is an error that MUST print both sides, because the author
never wrote the synthesized conditions.

### The generated condition must be DETERMINISTIC from the source text

User ruling — no unification, no generated names, no choice. The rule:

1. **Binders**: the declaration's non-matched params in DECLARED order, THEN the
   matched-position binder and the clause variables, grouped by sort. The tail order is not
   free: it must match the shared schema's (`forall k, n: Nat`) or one `instantiation` cannot
   close the obligation and the proof falls back to manual `fix`/`generalize`. Verified both
   ways.
2. **Conditions**: for argument position `p`, if a clause head writes a PATTERN there, emit
   `<freshBinder_p> = <pattern>`; if it writes the parameter itself, emit nothing. A `when`
   guard is conjoined VERBATIM. An arrow-guard antecedent likewise.

   **The fresh binder is POSITIONAL (`arg2`), never the declared param name.** `cpower(a, n:
   Nat)` has clause `cpower(a, succ(n))` — the clause variable SHADOWS the param, so
   "`param_p = pattern`" would generate the nonsense `n = succ(n)`. Positional names are a
   function of the declaration alone, so they stay deterministic under any clause's variable
   choices.
3. **Right-hand sides**: each clause's RHS exactly as written, in lexicographic pair order
   (arm order is immaterial — see above).

Worked example — `oper f(j: Nat, k: Nat)` with clauses `f(j, ZERO) = base(j)` and
`f(j, succ(m)) = succ(f(succ(j), m))` (whose emitted axioms have DIFFERENT binder lists,
clause 0 having no `m`) generates:

    forall j, k: Nat; forall m: Nat;
      (k = ZERO and k = succ(m)) -> base(j) = succ(f(succ(j), m))

**Consequence to document:** because conditions come from argument POSITIONS, renaming or
reordering a declaration's params changes the generated statement and breaks the
`consistency:` theorem. Same fragility a `model`'s `<-` has when a source theory renames an
axiom — acceptable, but it is why the mismatch error must show both statements.

## THE CORPUS (measured 2026-11-18, all 112 definition blocks)

| shape | count | obligation |
|---|---|---|
| single clause | 40 | none — free by the rule |
| `ZERO`/`succ(m)` primitive recursion | 66 | the standard pair; discharges by boilerplate |
| arrow-guarded (the `monomial` family) | 5 | condition is the antecedent; pairs are VACUOUS |
| `when`-guarded, 3 clauses (`swap`) | 1 | one real pair + two vacuous |

`swap` is the only block in `std` whose clauses GENUINELY overlap, and it is the witness for
why the obligation is "overlaps AGREE", never "overlaps do not exist":

    apply(swap(u, v), x) = v when x = u;
    apply(swap(u, v), x) = u when x = v;
    apply(swap(u, v), x) = x when x != u and x != v

(0,1) overlaps exactly when `u = v`, and there both arms agree. (0,2) and (1,2) have
self-contradictory conditions and are vacuous. A checker that REJECTED overlap rather than
requiring agreement would wrongly reject `swap`.

**It is also the worked example of PARTIAL application** — the reason `consistency:` is a list:

    consistency: swapOverlapAgrees, _, _

`swapOverlapAgrees` is `forall x, u, v: E; (x = u and x = v) -> v = u`, proved standalone and
resting on NO axioms (the two hypotheses rewrite into the conclusion). It quantifies only
`x, u, v` — its own variables — where a conjunctive form would quantify the union over all
three pairs. The other two positions are `_`: the complementary-(in)equality route, also
axiom-free.

Note `size(a: Set) => Nat: hasSize(a, size(a)) when isFinite(a)` — a `when` on a SINGLE
clause is a DOMAIN RESTRICTION, not a case split, and carries no obligation.

## BUILD ORDER

1. **DONE — the shared schemas (`2a305e0`) and the `definition_consistency` tactic.** The
   ZERO/succ pair lives in `std/peano.b4m`; the word is a `theory_selector` tactic
   (`[using definition_consistency(peano)]`) whose certificate is `fix` / `instantiation` /
   `generalize`, generated from the GOAL ALONE — no clause structure is passed in, verified
   at 1 and 3 non-matched binders. Gated by `tests/cases/definition/`.

   **Why it cannot be unsound:** the word proves nothing itself. It emits an `instantiation`
   and the KERNEL checks the fit, so a goal whose conditions can both hold fails the statement
   match rather than being discharged (gated by `consistency_satisfiable_bad.b4m`, whose
   consequent is false).

   Still to do here: the 5 arrow-guarded `monomial` blocks and `swap` need their own schemas;
   special-casing them is fine (user ruling).
2. The parser change: `.` terminator + `consistency:` declaration, and the migration of all
   112 blocks.
3. **PARTLY DONE** (`f7b68a0`, `8ab84f3`, and the `--library` consumer). The parser takes the
   `.` terminator and the `consistency:` list, validates the entry count against
   `arms*(arms-1)/2`, and carries the list on the AST decl (`ast.Consistency`, with `pairAt`
   deriving a position's clause pair). 125 blocks migrated across 30 files.

   `--library` enforces the half that can be enforced today: a declaration naming a theorem
   that does not exist. The SIBLING half — a multi-clause block with NO declaration — is
   written but GATED OFF, because turning it on fails `std --library` on all 72 multi-clause
   blocks at once, which is the state this build order exists to avoid. Flipping it on is
   step 5.

4. **PARTLY DONE — the synthesizer.** `Parser.synthesizeObligations` generates one obligation
   per pair onto `ast.Consistency.obligations`, in the same canonical order as `entries`.
   Deterministic from source text: each clause's condition is its guard verbatim, or
   `argN = <pattern>` on a fresh POSITIONAL binder for a pattern-matched slot. Sorts are left
   `inferred`, exactly as a clause variable's are, for the elaborator to settle.

   **All THREE corpus shapes synthesize, so the `monomial` special case is not needed after
   all.** An arrow-guarded clause (`(not (i = k)) -> coeff(…) = zeroR`, the shape all 5 of
   that family use) states its guard as a leading ANTECEDENT rather than with `when` — and the
   parser desugars `when` to exactly that, so the two mean the same thing. Reading both costs
   one `rhsOf` recursion through `.implies` plus an `antecedentOf` helper.

   Worth noting what the `monomial` obligation reveals: it has exactly ONE condition, because
   clause 0's matched slot holds `k`, the declared PARAMETER itself — so that clause applies
   everywhere and constrains nothing. The asymmetry is the definition's actual content (one
   index pinned, every other index zero), and the synthesizer reproduces it rather than
   inventing a condition.

   Still to do: the per-position MATCH check (a named entry's theorem against its synthesized
   obligation) with a both-sides mismatch diagnostic.
5. Flip to required. The corpus must never pass through a state where blocks owe unwritten
   proofs.

## SETTLED (user ruling 2026-11-18, confirming all three)

- **TWO triviality routes, both of which `_` must cover.** Measured 2026-11-19, and they are
  not the same mechanism:

  | route | shape | discharge | axioms |
  |---|---|---|---|
  | constructor-disjoint | `k = ZERO and k = succ(n)` | instantiate the sort's vacuity schema | `succNotZero` |
  | complementary (in)equality | `x = u and (x != u and …)` | `ex_falso` on the pair | **none** |

  The second is `swap`'s two trivial pairs, and `tautology` CANNOT do it — it declines with a
  countermodel, because it sees `x = u` and `x != u` as unrelated atoms. So the tactic needs
  both routes; only the first is built today.

- **Vacuous pairs are still EMITTED, never dropped.** Every pair gets a list position and an
  obligation; the checker never elides one because its conditions look contradictory. Dropping
  would be the wrong instinct anyway, since EVERY ZERO/succ obligation is vacuous in exactly
  that sense. What makes them cheap is the tactic, not elision — which is what `_` spells.

- **The shared schema is PER-SORT, supplied by the theory that declares the constructors.**
  `noNatIsZeroAndSucc` is about ℕ, so it lives in `std/peano.b4m` beside `succNotZero`, the
  axiom it rests on. A sort with its own constructors supplies its own pair — the theory that
  knows its constructors are distinct is the theory that can prove it.

  **This costs nothing today.** Measured: EVERY constructor split in the corpus is ℕ's —
  37 spelled `NAT_ZERO`/`succ` and 29 spelled `ZERO`/`succ`, differing only in local naming
  and both resolving to peano, which all 66 already import. So ONE schema in `std/peano.b4m`
  covers the whole corpus; the per-sort rule only activates when a new sort with constructors
  is declared. (The remaining 5 multi-clause blocks pattern-match on nothing — they are the
  arrow-guarded `monomial` family.)

- **WHEN the obligations are checked (user ruling 2026-11-19).** In NON-LIBRARY mode an
  UNUSED definition does not have its consistency checked: it demands nothing, so nothing
  checks it — the same rule as everything else in a demand-driven engine, and consistent with
  the decl-time schema check having been REMOVED (#93: "uncited code isn't checked"). The
  obligation is demanded when a clause of that block is.

  **In `--library` mode every definition's obligations are checked**, because a library's
  whole surface must be sound and a definition is as much of that surface as an axiom.

  Note the two interact usefully: `--library` ALREADY rejects an unused definition (per
  clause, by name and line — verified), so in library mode the consistency check only ever
  applies to definitions that ARE used. An inconsistent dead definition is caught either way,
  just by the earlier rule.

  `--library` is DIRECTORY-scoped ("a library is its whole file set"), so the check belongs
  with the other whole-set rules, not in the per-file path.

- **`--draft` suspends the requirement**, like every other author-hygiene check (`intheory`
  required, lemmas cited, the `--library` header rule). `verify.draft` is the single coarse
  work-in-progress bit these consult.

## STILL OPEN

- **Well-foundedness** is NOT designed — the second, independent property. `g(n) = s(g(n))`
  is detectable syntactically (same argument on both sides) and `rconvolution`'s decrease is
  syntactic too, but the criterion and its syntax (`termination: <name>`, in the
  well-formedness section the `.` opens) are unspecified. The arrow-guarded `monomial` family
  and `swap` also still need their own shared schemas for CONSISTENCY; special-casing them is
  approved.
