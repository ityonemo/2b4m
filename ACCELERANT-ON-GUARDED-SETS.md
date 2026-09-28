# ACCELERANT-ON-GUARDED-SETS.md — accelerants that meet a relativized axiom

Status: **OPEN, pinned 2026-09-28.** A recorded observation with candidate
diagnoses, NOT a plan. The root cause is **not yet established** — three readings fit
the evidence and they call for different fixes. Nothing in the engine has
been changed. The code has not been read; everything below the "What is established"
section is inference from one failure and from the architecture notes, and is flagged
as such.

Related: `MODEL-DESIGN.md` (the guarded-model machinery), `ACCELERATION.md`,
memory notes `accelerants-not-model-aware`, `required-on-model-primitive`.

## The trigger

AATA §3.2 Exercise 14 — ℝ\* × ℤ is a group under the componentwise operation.
Both halves exist:

- `std/group/product.b4m` — the direct product of two groups, abstractly: a pair sort
  with the componentwise operation, group laws proved, exposed as a `model` of
  `std/group.b4m` so its corpus transfers.
- `std/real/units.b4m` — ℝ\*, as the PREDICATED CUT `RStar = Real where nonzero`,
  with its group laws stated over that cut.

The product instantiates cleanly at UNGUARDED factors: `std/integer/mod-n-product.b4m`
is ℤ_n × ℤ_n and is green. Instantiating it with ℝ\* as the first factor fails.

## What is established

`std/group/product.b4m` proves its three group laws with an accelerant over the
factor axioms:

```2b4m
theorem prodAssoc: forall p, q, r: Pair; prodOp(prodOp(p, q), r) = prodOp(p, prodOp(q, r))
proof
  @conclusion |
    forall p, q, r: Pair; prodOp(prodOp(p, q), r) = prodOp(p, prodOp(q, r))
    [using simplify_quantified prodOpDef fstPair sndPair opGAssoc opHAssoc]
qed
```

Under a model whose `product.G` target is a predicated cut, the cited factor axioms
transfer RELATIVIZED. The generated proof then claims the bare equation while the
citation derives the implication, and the kernel rejects it. Verbatim, from the
attempt (a since-deleted `std/real/units-times-integers.b4m`):

```
std/group/product.b4m:82:12: error: UnitIntProduct@simplify{…}: step claims
  'mul(ONE, unitPart(p)) = unitPart(p)'
  but forall_elim derives 'nonzero(unitPart(p)) -> mul(ONE, unitPart(p)) = unitPart(p)'
```

Three such errors, one per law. The guard facts needed are all available at that
point: `unitPartIsNonzero` is a theorem of the instance, and for a composite term the
model's own `-|` closure nominations (`opG: rmul -| productOfNonzeroIsNonzero`) give
it from the guards of the parts.

So: the kernel caught a generated proof that drops a premise and asserts the
consequent. The trust boundary is intact and the diagnostic fires in the right place.

## What is NOT established — the readings

**Reading A — the emitter is lazy.** The accelerant CAN thread the guards and simply
does not. A collected rule arriving as `guard -> eq` should have its premise
discharged (cite the guard as its own step, modus ponens, then rewrite) instead of
being used as though it were `eq`. The witness construction is deterministic from the
goal AST and the model's `-|` map: a leaf term's guard is a theorem cite, a composite
term's guard is a closure lemma applied to its parts' guards, recursively. If so, the
fix is in proof generation and changes no contract — an accelerant remains a
deterministic (goal AST, selector) → proof AST map.

**Reading B — the procedure has no guard-respecting derivation to emit.** The
accelerants normalize to a canonical form (`simplify` to a shared normal form,
`polynomial` to a canonical sum of monomials), and those procedures assume their rules
are UNCONDITIONAL equations. Under a conditional rule, every intermediate term of the
normalization chain carries a side condition — and the guard of a term the
normalization BUILDS need not follow from the guards of the inputs. Normalization can
pass through terms outside the cut even when both endpoints are inside it (a regrouped
product whose factors are not individually in the cut has no closure lemma to appeal
to). If so, there is no proof for the emitter to emit, and no amount of emitter work
helps.

**All readings produce the same error text.** Distinguishing them requires reading
the rule-collection path, not more examples. (Reading C, below, is more general than
either and is where the generality test points.)

## What to read first (in this order)

1. `demandUsing` in `src/Engine/ProveTask/Prove.zig` — how an accelerant's synthetic
   schema instance is built, and what the cited facts look like when they arrive.
2. The `simplify` rule intake (`src/Engine/ProveTask/simplify.zig`) — whether a
   collected rule's guard premise is visible at collection time or stripped silently
   on the way in. This settles A vs. B: if the premise never reaches the procedure,
   that is a plumbing gap (A); if it reaches it and is discarded because the rewriter
   has no conditional-rule path, that is B.
3. The `-|` closure nominations in the model overlay — where they are stored and
   whether they are reachable at emission time, which is what makes A's recursive
   witness construction deterministic.
4. For Reading C: whether the overlay records, per axiom, that it was relativized ON
   TRANSFER versus stated only over the cut at the source. That is what decides whether
   a carrier-level form can be handed out soundly.

## The generality test — NO PER-PREDICATE SPECIAL CASING (user, 2026-09-28)

Any candidate fix must be checked against cuts whose predicate has no algebraic
content. Three cases span the space:

| cut | closed under the ops? | closure nomination possible? |
|---|---|---|
| `RStar = Real where nonzero` | yes (a multiplicative subgroup) | yes — `productOfNonzeroIsNonzero` |
| `Real where notSqrtTwo` (ℝ∖{√2}) | **no** | **no** — the closure fact is FALSE |
| ℤ with a range guard `0 ≤ x < 256` (a program's `u8`) | **no** (overflow leaves it) | **no** |

The second is a legitimate thing to work in (a punctured line) and the third is the
bread-and-butter of program verification, where the membership failures are the
INTERESTING CONTENT (overflow checking), not an annoyance to be designed away.

This retires an option that was on this page earlier — "restructure the abstract theory
to state its laws over the carrier with membership as separate CLOSURE theorems." That
works for `RStar` only because ℝ\* happens to be closed. It cannot work for ℝ∖{√2} or
for range-guarded `u8`: there is no closure lemma to state. Any design resting on `-|`
nominations therefore serves exactly one family of cuts and is not a fix.

Note also that a QUOTIENT is a different animal from a cut and already works. ℤ/255 as
`std/integer/mod-n.b4m`'s `Zn` is a sort with its own TOTAL operations (wraparound), and
it models cleanly — which is why ℤ_n × ℤ_n is green in
`std/integer/mod-n-product.b4m`. The two encodings should not be conflated: a quotient
wants its own sort and total ops; a range-guarded `u8` wants CARRIER arithmetic plus
membership obligations per operation.

## Reading C — the transferred axiom arrives in the wrong space

More general than A or B, and the one the generality test points at. The accelerant
does not want a relativized rule at all; it wants the CARRIER-LEVEL equation, where its
rules are honest unconditional equations and its normalization is valid whether or not
the intermediate terms lie in the cut. Membership is a separate obligation, discharged
where the refined sort is actually required — guards riding as FACTS, not as constraints
on rewriting (the `predicated-sorts` design intent).

On this reading the defect is that a guarded model exposes its source axioms ONLY
relativized, with no way for a rule-collecting accelerant to ask for the carrier-level
form. Give it both — relativized for citation, carrier-level for rewriting — and
accelerants never meet a conditional rule, no closure nominations are needed, and the
arbitrary-predicate cases work for free because nothing is asked of the predicate.

Open question this raises, and the reason it is a reading rather than a plan: whether
the carrier-level form is always SOUND to hand out. For ℝ\* the field axioms do hold
unconditionally on `Real`, so `mul(ONE, x) = x` is fine. But an axiom that is TRUE ONLY
ON THE CUT has no carrier-level form to expose, and handing one out would be unsound.
Distinguishing "relativized on transfer but carrier-true" from "genuinely only true on
the cut" is the crux, and it is not obvious that the overlay records enough to tell
them apart.

## If Reading B holds and Reading C does not rescue it

**Accept that guarded theories do not get accelerants** for their axiom-level laws, and
prove those by explicit steps. Not a workaround but an honest statement of the
procedure's domain.

## `--fast` needs no changes (user ruling 2026-09-28)

`--fast` admits a `using` word on an α-match of the statement and never racks a
ProveTask, so the generated proof is never built and there is nothing to discharge.
The admission IS the disclosed trust boundary; a second warning channel underneath it
would report the same decision twice. No new taint channel, no `--fast` work. The
whole of the fix — whichever reading holds — is on the strict path.

Corollary for whoever picks this up: a guarded instance may well pass `--fast` and
fail strict. That is the documented `--fast` contract (an accelerant can pass fast and
fail strict when it cannot produce a kernel certificate), not a new hazard.

## Soundness note

Whatever is built, a guard must be DISCHARGED BY PROOF, never assumed because the
model nominated a closure lemma. A closure nomination
`opG: rmul -| productOfNonzeroIsNonzero` states
`nonzero(a) -> nonzero(b) -> nonzero(mul(a, b))`; using it still requires both
antecedents. Treating a nomination as a licence to skip the side condition would let an
accelerant rewrite with an axiom whose guard does not hold — the one failure mode here
that is unsound rather than merely inconvenient.

## Ledger

`aata/EXERCISES-DEFERRED` carries §3.2 Ex 14 under "a direct product with a GUARDED
factor"; `aata/3.2-groups-exercises.md` marks the exercise Deferred(attempted) with the
cause in prose. The attempted instance file was deleted rather than left broken; it is
recoverable from this document's description (pair sort over `Real × Int` with
projections at the carrier plus a `unitPartIsNonzero` axiom, a `UnitIntProduct` model
with guarded nominations, then the three law transfers) and makes a natural fixture:
it should pass `--fast` and, once fixed, pass strict.
