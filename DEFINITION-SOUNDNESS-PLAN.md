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

   **DONE — the per-position MATCH check.** `statementMatches` elaborates BOTH sides into one
   scratch pool — the named theorem's own stated AST and the synthesized obligation — and
   compares up to alpha-equivalence, the same test the kernel's claim-match uses. Both sides
   come from AST, so one elaborator settles both and there is no reify/unreify asymmetry.

   The diagnostic shows BOTH statements, because the author never wrote the obligation:

       - nrep (…:17) — 'wrongStatement' does not state the obligation for clauses 0 and 1
             it states:  ZERO = ZERO
             wanted:     forall a: Nat; forall arg2: Nat; forall n: Nat;
                           (arg2 = ZERO and arg2 = succ(n)) -> a = succ(nrep(a, n))

   The `wanted` line is PASTEABLE — `tests/cases/definition/library-ok/` was built from it,
   and that fixture is the whole pipeline passing `--library`: synthesize → match → discharge
   by one `definition_consistency(peano)` step.

   A statement that matches but whose SORT has no vacuity schema fails at the tactic
   (`expected sort 'Nat', got 'N'`), which is the per-sort rule behaving correctly rather than
   a gap: that sort's own theory would supply its schema.
5. **BLOCKED on three gaps, measured 2026-11-20.** Staging works — a `_` entry now mints a
   real theorem (`definition-<sym>-{i,j}`, exported, manifest-exempt, proved by the one tactic
   step) and `ParseTask` racks a ProveTask for it, so the obligation is DISCHARGED rather than
   merely declared. The theory selector is read off the clause pattern's token QUALIFIER
   (`peano.succ` ⇒ `peano`), which is syntactic and needs no sorts — it must come from the
   matched ARGUMENTS, never the RHS, or `cpower(a, NAT_ZERO) = complex.ONE` yields `complex`.

   Declaring all 72 and running `--library`: **50 discharge with a bare `_`.** The other 22
   are three real gaps, not switch-flipping:

   | n | gap |
   |---|---|
   | 9 | **a clause matching in MORE THAN ONE slot.** `csegmentOf(p, q, succ(j), c, succ(n))` matches slots 3 AND 5, so the obligation correctly carries three conditions — but the tactic's `peel` expects exactly two conjuncts. The synthesizer is right; the tactic is too narrow. |
   | 11 | **the `when`-variable sort limitation**, already recorded — and WIDER than thought: it hits the `monomial` family too, not only `swap`. |
   | 2 | **the selector is unresolvable** — not a missing import: `std/ring/polynomial.b4m` and `std/field/polynomial.b4m` DO import peano, but spell their constructors UNQUALIFIED (`theCofactorIndex(i, j, ZERO)`), so there is no token qualifier to read and the step goes bare. |

   **ACCEPTED FOR NOW (user, 2026-11-20): requiring a `peano` import is OK.** But it is a
   NAMING COUPLING of exactly the kind `[[accelerator-naming-couplings]]` forbids, and the
   canonical example in that memory is nearly identical — `ext` looked up its element sort by
   the literal name `"Universe"`, broke when the sort was renamed, and was fixed by deriving
   the sort STRUCTURALLY. Qualifier-sniffing works only when the author happens to write
   `peano.succ`; an author who writes `ZERO`/`succ` bare, or imports peano under another name,
   silently gets a bare step and an unresolvable schema.

   **FOLLOW-UP, immediately after the emergency project (user ruling): require the bindings
   for the "relevant number system" to be DECLARED EXPLICITLY** rather than sniffed. That
   replaces the coupling with a stated binding, in the spirit of the rule — the override is the
   language's own remapping, not a heuristic in the checker.

6. **NEW — a QUERY that prints a block's `_` obligations** (user, 2026-11-20). The checker
   knows each obligation's exact statement; an author has no way to see it except by
   deliberately mis-declaring and reading the `wanted:` line. A `2b4m query consistency
   <file> [symbol]` printing them, pasteable, is what makes the hard pairs writable — the
   same role `debug model` plays for a model's obligations.

7. Flip to required. The corpus must never pass through a state where blocks owe unwritten
   proofs.

## SETTLED (user ruling 2026-11-18, confirming all three)

- **TWO triviality routes, both of which `_` must cover.** Measured 2026-11-19, and they are
  not the same mechanism:

  | route | shape | discharge | axioms |
  |---|---|---|---|
  | constructor-disjoint | `k = ZERO and k = succ(n)` | instantiate the sort's vacuity schema | `succNotZero` |
  | complementary (in)equality | `x = u and (x != u and …)` | `ex_falso` on the pair | **none** |

  The second is `swap`'s two trivial pairs, and `tautology` CANNOT do it — it declines with a
  countermodel, because it sees `x = u` and `x != u` as unrelated atoms.

  **BOTH ROUTES BUILT.** `peel` classifies, trying the complementary route FIRST because it
  needs no particular binders: `findComplementary` flattens the `and` tree (association is not
  canonical in the corpus) and looks for a conjunct whose negation is also a conjunct. Its
  certificate assumes the conditions, walks the nested conjunction with `and_lhs`/`and_rhs`
  (the path is searched, not assumed), and finishes with `ex_falso` — no schema, no selector,
  and verified to rest on NO axioms. Both of `swap`'s trivial pairs discharge, so
  `consistency: swapOverlapAgrees, _, _` is now serviceable.

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

## KNOWN LIMITATION — a `when`-clause variable's sort

A clause variable appearing ONLY in the guard and the dropped defining application has no sort
the elaborator can infer: its rule is argument-position only, so `x = u` does not pin `x` from
`u: E` even though equality determines it. `swap` is the one such block in `std`, and its
obligation elaborates only when a named entry is compared — so nothing fails today, and the
statement can be written with sorts spelled out.

Two fixes, neither taken: teach the elaborator to infer across equality (a separate change,
corpus-wide risk), or anchor the clause's own left-hand side as an extra conjunct — which
works, and WAS tried, but changes the agreed `(conditions) -> rhs_i = rhs_j` shape and breaks
the tactic's two-conjunct recognition. Not the right trade.

## WELL-FOUNDEDNESS — the remaining criterion

The second, independent property: does a recursive clause have a fixpoint at all? Still live
against the current checker, re-probed 2026-11-23:

```2b4m
oper g(n: N) => N:
  g(n) = s(g(n)).

theorem contradiction: Z = s(Z)        // checks, exit 0
proof
  @def    | forall n: N; g(n) = s(g(n))   [by definition(0) g]
  @at-z   | g(Z) = s(g(Z))                [by apply_at(Z) def]
  @nofix  | forall n: N; not (n = s(n))   [by cite sNoFixedPoint]
  @nofix-at | not (g(Z) = s(g(Z)))        [by apply_at(g(Z)) nofix]
  @conclusion | Z = s(Z)                  [by ex_falso at-z nofix-at]
qed
```

Same class as PAINPOINTS 16f: the kernel does as it is told, and the user has built an
inconsistent system with nothing warning them.

### The criterion: a MEASURE that strictly decreases at every recursive call

**A syntactic check is not acceptable here** (user ruling 2026-11-23). "The argument looks
smaller" can pass a looping definition: `f(g(x)) = f(x)` decreases structurally while `g` is
free to be the identity. A soundness check cannot rest on a shape that admits a counterexample.

So the obligation is a PROOF, in the user's framing:

> Gather the arms that TERMINATE (no recursive content). Each RECURSING arm must then prove:
> for all inputs, the inner call satisfies one of the terminating arms' patterns after
> finitely many steps.

In practice that is discharged as a **strictly decreasing measure on a well-ordered sort** —
which is the same claim, and the form that is actually provable. The recursion reaches a base
arm because the measure cannot descend forever.

```2b4m
// rconvolution: the base arm's pattern is arg4 = NAT_ZERO; the recursive arm calls at
// arg4 = m from arg4 = succ(m). The measure is arg4.
theorem rconvolutionDecreases: forall m: Nat; less_than(m, succ(m))   // lessThanSelf
```

Verified provable against the three corpus shapes:

| | measure | obligation | proved from |
|---|---|---|---|
| `rconvolution` | arg 4 | `less_than(m, succ(m))` | `peano_order.lessThanSelf` |
| `rsegmentOf` | arg 5 | `less_than(n, succ(n))` | same |
| `fib` | arg 1 | TWO, see below | `lessThanSelf` + `lessThanSuccRight` |

`rsegmentOf` is why the measure must be NAMED rather than inferred from "the arguments": its
arg 3 decreases, arg 4 **increases**, arg 5 decreases. Only arg 5 is the measure, and a check
that tried every position or demanded none increase would get it wrong.

### MULTIPLE RECURSIVE CALLS — one obligation per CALL, not per clause

Measured: **no clause in `std` has more than one self-call**, and exactly one in the wider
corpus does — `fib` (`aata/2.3-primes-exercises.md:106`):

```2b4m
oper fib(n: Nat) => Nat:
  fib(NAT_ZERO) = NAT_ZERO;                                   // terminating arm
  fib(nat_succ(NAT_ZERO)) = NAT_ONE;                          // terminating arm
  fib(nat_succ(nat_succ(k))) = nat_add(fib(nat_succ(k)), fib(k)).   // TWO calls
```

The two calls are at `succ(k)` and at `k`, from the pattern `succ(succ(k))`. Both decrease,
**by different amounts and from different facts**:

```2b4m
theorem fibCallOneDecreases: forall k: Nat; less_than(succ(k), succ(succ(k)))
  // lessThanSelf at succ(k)
theorem fibCallTwoDecreases: forall k: Nat; less_than(k, succ(succ(k)))
  // lessThanSelf at k, then lessThanSuccRight
```

Both verified to check. So the obligation structure is **per call site**, and that is forced
rather than chosen: a single clause-level obligation could not have been discharged by one
theorem here, since the two calls need different lemmas.

Consequences for the syntax, all following from "per call":

- **Entries are positional over the call sites of each recursive arm**, in source order — the
  same discipline `consistency:` uses for clause pairs, and for the same reason: a miscount
  should be an error rather than a silent default.
- **A terminating arm declares nothing.** It is identified by having no self-call, and its
  PATTERN is what the recursive arms must reach.
- **A clause with two calls needs two entries.** `fib` would write
  `termination: fibCallOneDecreases, fibCallTwoDecreases`.

### SYNTAX: `termination:` with `_` for the terminating arms

```2b4m
termination: _, _, proof1, proof2, …
```

**Positional over the whole block**: one entry per terminating arm (written `_`), then one per
recursive CALL, in source order. The declaration therefore shows the arm structure rather than
making a reader reconstruct it.

**A `_` MUST correspond to a terminating arm** (user ruling 2026-11-23) — it is not a
"discharge this automatically" marker as it is in `consistency:`. Writing `_` where an arm
recurses, or a name where an arm terminates, is an error. That makes the declaration a
checkable claim about which arms are base cases, not just a list of proofs.

Against the corpus:

```2b4m
oper rconvolution(p: RPoly, q: RPoly, j: Nat, m: Nat) => Real:
  rconvolution(p, q, j, NAT_ZERO) = …;                       // arm 0: terminating
  rconvolution(p, q, j, succ(m)) = … rconvolution(p, q, succ(j), m).   // arm 1: one call
  termination: _, rconvolutionDecreases

oper fib(n: Nat) => Nat:
  fib(NAT_ZERO) = NAT_ZERO;                                  // arm 0: terminating
  fib(succ(NAT_ZERO)) = NAT_ONE;                             // arm 1: terminating
  fib(succ(succ(k))) = add(fib(succ(k)), fib(k)).            // arm 2: TWO calls
  termination: _, _, fibCallOneDecreases, fibCallTwoDecreases
```

Note `fib`'s **4 entries for 3 arms**. The count is driven by call sites, not arms, which is
forced by the per-call obligation: its two calls need different lemmas (`lessThanSelf` at
`succ(k)`; `lessThanSelf` then `lessThanSuccRight` for `k`), so no single entry could
discharge both.

The arity rule, stated once: `entries = (number of terminating arms) + (total recursive calls
across all arms)`. A miscount is an error naming both numbers, as `consistency:` does.

**At least one `_` is required.** A block whose every arm recurses has no base case at all,
so no measure argument can save it — `g(n) = s(g(n))` is exactly that, and the arity rule
rejects it before any proof is considered. That is the cheapest possible diagnosis of the
original exploit.

### Why this is NOT symmetric with `consistency:` after all

An earlier draft of this section argued well-foundedness should take no author-written
theorem, because "argument 5 decreases" is a property of the source text. **That reasoning
only holds for the syntactic check, which is rejected.** A measure decrease on a well-ordered
sort IS a proposition about the mathematics — `less_than(m, succ(m))` is a theorem of
`peano/order.b4m`, not a fact about parsing — so it wants a named theorem exactly as
`consistency:` does.

The `termination: <name>` slot the `.` terminator was reserving is therefore wanted after all.

### What the check must NOT reject

Three shapes the corpus relies on, each a potential false positive:

- **A clause whose LHS nests the symbol in an accessor**: `coeff(monomial(a, k), i) = zeroR`
  mentions `monomial` on the left inside `coeff` and not on the right at all. **19 such
  clauses** in `std/`; the naive "symbol appears twice" test flags every one. (They are also
  IMPLICIT definitions, handled separately.) The test must look at the RIGHT side only.
- **Recursion to a different symbol**: `rtheCofactorIndex` calls `rtheGapTo`. Per-symbol, so
  invisible here — and mutual recursion does not occur in the corpus, which is what lets the
  check stay per-symbol.
- **A non-recursive clause**: 113 of the 161 clauses in `std/`.

### Build order

1. `recursiveCalls(clause, sym)` — every self-application on the RHS, in source order. Reuses
   `findApplication`'s recursion but collects all hits rather than the first.
2. `termination:` parsing, positional over the recursive arms' call sites, mirroring
   `parseWellformedness`'s `consistency:` loop.
3. Synthesize each call's obligation so the checker can verify the named theorem states it —
   the `collectConsistencyGaps` pattern. **This is the open piece**: the obligation mentions a
   MEASURE (which argument position), and the checker cannot know which position the author
   intends. Options below.
4. Error when a recursive arm's call has no `termination:` entry.
5. Gates: `std --library`, `aata`, theorem counts unchanged — all 48 recursive clauses need
   entries, so this is a real migration, not a no-op.

### Open: how the measure is named

The obligation's statement depends on which argument is the measure, and the checker cannot
infer it — `rsegmentOf` has one decreasing, one increasing, one decreasing, and only the
author knows arg 5 is the intended measure.

Three options:

- **Infer by trying every position**, accepting the first for which the named theorem matches
  a synthesized decrease. Fragile, and silently picks a position the author did not mean.
- **Name the position in the declaration**: `termination: 5 by rsegmentOfDecreases`. Explicit,
  verifiable, and the checker can synthesize the exact statement to match against.
- **Let the theorem speak for itself** — accept any theorem whose statement is a strict
  ordering between the call's argument and the pattern's at SOME position, and report which
  position it matched. No new syntax; the checker discovers the measure from the proof.

The third is the most appealing and needs a decision before step 3. It also raises the
question of what ordering counts: `less_than` on `Nat` here, but the criterion should not
hardcode a predicate name — [[accelerator-naming-couplings]] again. A well-founded-ordering
notion per sort is the honest version, and `std/peano/order.b4m` already supplies the facts
for ℕ.
own trust boundary.
