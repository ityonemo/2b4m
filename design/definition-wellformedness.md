# Definition well-formedness — the four obligations

A `pred`/`oper` DEFINITION BLOCK claims to pin down its symbol. Four obligations check that it
does, each guarding a distinct way the claim can fail:

| obligation | asks | failure it prevents |
|---|---|---|
| `consistency:` | do the arms AGREE where they overlap? | a block proving `ZERO = ONE` |
| `existence:` / `uniqueness:` | does the characterized value EXIST, uniquely? | a symbol denoting nothing, or a set |
| `termination:` | does the recursion REACH A BASE? | `g(n) = s(g(n))`, which has no fixed point |
| `totality:` | do the arms COVER the domain? | a symbol left UNDETERMINED somewhere |

`GUIDE.md` documents the syntax and semantics. This file records the parts that are not
derivable from the surface — why these four, why not the alternatives, and what the
implementation measured.

## `consistency:` and `totality:` are duals, and only one used to exist

Consistency guards against arms CONTRADICTING; totality against arms NOT REACHING. A block can
satisfy the first and fail the second — arms that never overlap make every consistency pair
vacuous while some input matches no arm at all.

**The motivating instance was real, not hypothetical.** `std/ring/polynomial.b4m`'s `monus` is
truncated subtraction, and it was written with two arms: `monus(i, ZERO) = i` and a `succ`/`succ`
step. `monus(ZERO, succ(j))` matched NEITHER — the flooring case, which is the entire reason the
symbol exists. The declaration's own comment claimed a floor clause that was never written, and
everything above inherited it: `theCofactorIndex(i, j, k)` was unconstrained whenever
`j + k > i`, routine for a triple-product coefficient. Consistency could not see it; only a
coverage check can.

## Totality is AUTODETECTED where the arms are propositionally exhaustive

The obligation is demanded only when the disjunction of the arms' conditions is not a
propositional tautology (truth table over their distinct atoms, opaque non-propositional
subformulas, the 16-atom cap `tautology` uses). Measured on the corpus, which is what settled
the design — of 72 multi-arm blocks: **56** are one pattern arm plus its exact negation, 10 are
implicit definitions owing existence/uniqueness instead, 5 are `ZERO`/`succ(k)` splits, 1 is
`swap`. So a per-block theorem would have been noise on 56 of 62 applicable blocks.

That 56 is not luck: `prev`-descent needs a guard and the natural guard is the base pattern
negated, so the form the recursion migration produced is total BY CONSTRUCTION.

Three shapes it recognizes: two-way complementarity (`n = ZERO` / `n != ZERO`), a PREDICATE
split (`p(x)` / `not p(x)`), and `swap`'s three-way (`x = u` / `x = v` /
`x != u and x != v`). The last is why this is a general propositional test rather than a
pairwise complementarity check — `swap`'s third arm is the conjunction of the others'
negations, which no pairwise test sees.

**A disequation is its equation NEGATED, not a separate atom.** Without that normalization the
truth table admits "both false" and the commonest shape goes undetected.

**It is deliberately conservative.** It refuses `n = ZERO` beside `less_than(ONE, n)`, which
leaves a real gap at `ONE`. Deciding that pair needs arithmetic, and a detector that reasons is
a prover that can be wrong. A refusal means the author names a theorem — which is precisely
where someone should be made to look.

## Termination: five framings were rejected before the sixth worked

| framing | why it fails |
|---|---|
| syntactic decrease | `f(g(x)) = f(x)` passes while `g` is the identity |
| a decreasing MEASURE | "decrease" needs a well-founded relation 2b4m lacks — and some legitimate recursions INCREASE (a ladder operator maps level `n` to `n+1`) |
| reachability with an explicit `N` | faithful but unstatable: iterating a multi-call step is not function application |
| generated AXIOMS giving the predicate meaning | a soundness check that emits assumptions returns exactly what it was meant to remove |
| base cases as DISJUNCTS of the predicate | instantiating at `ZERO` requires WRITING `sub(ZERO, TWO)`, whose guard is false; guard discharge is per-term, not flow-sensitive |

**The sixth, which works:** the checker GENERATES a predicate transcribing the recursive arm's
call sites — one conjunct per call, each a disjunction of that call grounded with its argument
hitting a terminating arm's pattern — and the author proves the arm's own guard implies it. The
base alternatives are what make the recursion bottom out; an earlier form conjoined the bare
grounded calls, had a step and no base, and was unprovable.

**The obligation names no ordering and no induction principle.** How to prove it is the
author's choice, which is the design's one load-bearing insight.

**Only the CONTROLLING slots are transcribed** — those the arm's guard names. A riding slot
carrying a guarded operation made the predicate uninstantiable where that guard fails: 
`segmentGrounded(j, c, n)` with `prev(j)` on a riding exponent needed `ZERO != ZERO` at `j = 0`.
Measured both ways — the identical shape with total `monus(j, ONE)` instantiates fine.

## An `oper` block cannot be unsound; a `pred` block can

An `oper`'s clause is an EQUATION, so it has no propositional structure to negate. The nearest
analogue to negative self-reference is `f(n) = succ(f(n))`, which `termination:` rejects. The
three remaining failure modes are each covered (no fixed point → `termination:`; overlapping
arms with different values → `consistency:`, which refuses the trivial discharge so the author
would have to prove `ZERO = ONE`; a nonexistent characterized value → `existence:`).

A `pred` block is different: `pred q(n): q(n) iff (not q(n)).` is accepted and proves
`q(c) and not q(c)`. That is NEGATIVE SELF-REFERENCE, orthogonal to all four obligations — a
block can satisfy every one of them and still be inconsistent this way. Tracked in PAINPOINTS.
So "definition blocks are well-formed" holds; "definition blocks cannot be unsound" does not.

The separate standing caveat: a bare `oper` plus a hand-written axiom is just an axiom, and
nothing stops a false one. That is the `axiom`-vs-`hole` discipline, not a well-formedness gap.

## RECURSION AND CASE-SPLITTING BOTH NEED AN INDUCTIVELY GENERATED SORT

Found twice, independently, by the termination and totality migrations. On a bare abstract sort
(`sort N` with `Z`/`s` declared and no induction schema) a recursive definition's obligation is
GENUINELY unprovable — nothing forbids an element whose predecessor chain never reaches `Z` —
and a `Z`/`s(n)` coverage split is equally unprovable. Four test fixtures were in exactly this
state, so the gates caught unsoundness in the test suite itself. The honest fix is to state the
induction schema, which is the assumption such a definition always rested on.

## What a definition is NOT

`peano.add` and `peano.mul` are PRIMITIVES constrained by axioms, not definitions.
`addZeroLeft` + `addSuccLeft` characterize a symbol that has no prior meaning — nothing defines
`add` in terms of something else, so those two axioms ARE its theory. Contrast `monus`, which
gets its meaning from `prev`. Converting a primitive to a definition block would saddle it with
three obligations about something that was never underdetermined.

(A deleted `DEFINITION-MIGRATION-CANDIDATES` proposed exactly that conversion, having stated
the right test and then misapplied it. Its plausible candidates were elsewhere —
`invertibleDef`, `conj`, and the membership style where the clause head is
`member(x, union(a, b))` rather than `union(a, b)`.)

## A recurring hazard: the parser cannot classify a NAME

Three separate bugs came from trying to tell a clause variable from a lower-case constant by
SPELLING. `collectClauseVars` reads the lower-case convention, but `aata` declares
`const intZero` and the style guide prescribes lower-case for `pi`/`e`/`i`.

- A binder rename made a generated predicate's base branch reflexive (`j = j`), so the
  termination obligation fell to `[by reflexivity]` with no induction — a VACUOUS DISCHARGE.
- Quantifying a bare-name coverage argument produced `exists intZero_at1; n = intZero_at1`,
  destroying complementarity so a covering block appeared to owe an obligation.
- The l-value rule for recursive blocks remains STAGED for the same reason.

**The lesson: read STRUCTURE, not names.** Every fix that classified by spelling misfired;
every fix that read the argument's shape worked. And verify a synthesized statement by reading
it back off the checker — three of these were caught that way and no other.
