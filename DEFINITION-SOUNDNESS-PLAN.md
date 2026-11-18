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
order — `(0,1), (0,2), … (1,2), (1,3), … (2,3) …` — conjoined into ONE theorem:

    (cond_i and cond_j) -> rhs_i = rhs_j

**Conditions conjoined with `and`, one flat clause** (user ruling): not nested implications.
That is the shape the author reads and the tactics handle.

**NO syntactic exemption.** "Constructor-disjoint" is not a license to skip the obligation —
only the usual REASON it discharges easily. This is what closes the model-collapse hole the
user raised: `f(FOO) = FOO; f(BAR) = BAR` looks disjoint, but a model may map both `FOO` and
`BAR` onto one target constant. Carrying the obligation makes that sound automatically — the
obligation becomes `ONLY = ONLY` under the mapping, and a transfer re-proves the body, so
there is no gap between "checked in the source" and "true in the target".

### The obligations are provable WITH NO AXIOMS

Measured, and it corrects the plan this supersedes. The obligation is NOT "prove the guards
cannot both hold" (which would need a disequality); it is `conditions -> rhs_i = rhs_j`. For a
constructor split the conditions ARE the two equations whose combination gives the conclusion
by pure rewriting:

    forall x, m: N; (x = Z and x = s(m)) -> Z = s(m)      -- rests on NO axioms

`succNotZero` is neither used nor needed, so the "is the disequality reachable?" question is
void. The proof is theory-independent boilerplate: introduce the conjunction, `and_lhs` /
`and_rhs`, `rewrite`. 32 lines, of which ~30 are identical across every block.

**THEREFORE A DISCHARGE TACTIC MUST SHIP WITH THIS.** No existing word does it — `simplify`
wants equations, `tautology` sees atoms and declines with a countermodel, `specialize` does
not fit. Required-without-the-tactic would add ~2,200 lines of mechanical proof to `std`.

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

1. **Binders**: the declaration's params in DECLARED order, then each clause's extra free
   variables in first-appearance order, clause `i`'s before clause `j`'s. (The parser already
   uses first-appearance order for single clauses — `parser.zig:stageDefinitionAxiom`.)
2. **Conditions**: for argument position `p`, if a clause head writes a PATTERN there, emit
   `<paramName_p> = <pattern>`; if it writes the parameter itself, emit nothing. A `when`
   guard is conjoined VERBATIM. An arrow-guard antecedent likewise.
3. **Right-hand sides**: each clause's RHS exactly as written.

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

(0,1) overlaps exactly when `u = v`, and there both arms agree — obligation `v = u`, proved
in 4 steps. (0,2) and (1,2) have self-contradictory conditions and are vacuous. A checker
that REJECTED overlap rather than requiring agreement would wrongly reject `swap`.

Note `size(a: Set) => Nat: hasSize(a, size(a)) when isFinite(a)` — a `when` on a SINGLE
clause is a DOMAIN RESTRICTION, not a case split, and carries no obligation.

## BUILD ORDER

1. **The discharge tactic first**, verified by hand against one of each corpus shape. Nothing
   else can land before this without obligating 72 blocks with no way to pay.
2. The parser change: `.` terminator + `consistency:` declaration, and the migration of all
   112 blocks.
3. The synthesizer + the match check, with a both-sides mismatch diagnostic.
4. Flip to required. The corpus must never pass through a state where blocks owe unwritten
   proofs.

## STILL OPEN

- **Vacuous pairs**: does the single named theorem carry them as conjuncts (so the author
  proves all three for `swap`), or does the checker drop pairs whose conditions it can see are
  contradictory? "Conjunction of all pairs" argues the former — simpler and deterministic.
- **Does `--draft` suspend the requirement?** Every other author-hygiene check does.
- **Well-foundedness** is NOT designed. `g(n) = s(g(n))` is detectable syntactically (same
  argument on both sides), and `rconvolution`'s decrease is syntactic too, but the criterion
  and its syntax (`termination: <name>`?) are unspecified.
