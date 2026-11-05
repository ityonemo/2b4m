# Functions as sets of pairs — the payoff plan (future work)

The two Chapter-1 ontology walls (collections / sets-of-sets, and choice /
definite description) are both closed: `std/collection.b4m` handles collections,
and `functionFromGraph` (the tame ι) in `std/function.b4m` handles definite
description. What remains is the payoff those unlocks enable.

## The plan

The textbook-faithful move is: a function IS a set of pairs, and that CONCRETE
construction is a `model` OF the abstract opaque `Fn` theory — so the whole `Fn`
corpus (composition-associativity, invertible⇒bijective, …) transfers onto the
pair representation for free. Same shape as group→ring→ℤ, applied to functions.
Direction matters: the model maps the abstract `Fn` theory's sort onto the
concrete pair-set sort, and the abstract corpus flows DOWN onto the concrete
objects.

Build order (each layer additive, no kernel change):
1. **`std/pair.b4m`** — a `Pair` sort, `pair(a, b)`, `fst`/`snd`, projection axioms.
2. **Sets of pairs** — alias `set.Element = pair.Pair`; `std/set.b4m` then gives
   `member(Pair, Set)` for free (the shared-`Element` design paying off exactly as
   intended).
3. **`std/function-pairs.b4m`** — the concrete pair-set layer the model maps onto:
   `isFunction(S)` (single-valued guard), `applyPair(S, a)` = the unique `b` with
   `pair(a, b) ∈ S` (an ι-term — uses `functionFromGraph`), `composePair`,
   `identityPair`. Prove each `Fn` axiom as a LOCAL theorem over pair-sets — notably
   `funcExtensionality` flips from axiom to *theorem*, discharged by set
   extensionality.
4. **The model** — `sort FunctionSubset = Set where isFunction`, then
   `model FunctionAsPairs { function.Fn: FunctionSubset, function.apply: applyPair,
   … }`. Guarded because the sort-mapping targets the predicated `FunctionSubset`:
   the relativization threads `isFunction(bound) ->` through every binder over the
   mapped sort, so transferred theorems come back relativized, and you discharge the
   guards at each cite (needs lemmas like `isFunction(f) ∧ isFunction(g) →
   isFunction(compose)`).

## Risk assessment (honest)

- **The `model` stratum is REVERSIBLE.** The pair theory + the `model` block + the
  transferred cites are an additive layer over untouched foundations. If the
  guard-discharge burden gets ugly or a transfer won't go through, delete the
  `model` block — the pair-set theory still stands on its own, and nothing
  downstream of the opaque `Fn` theory breaks (it is never modified). So concerns
  about guard relativization at scale and "is the transfer worth it" are
  *find-out-by-trying*, not *de-risk-first*: build it, roll back if it doesn't earn
  its keep.

- **The load-bearing foundation (definite description) is already in place.**
  `applyPair` is an ι-term, and `functionFromGraph` provides exactly that — so the
  non-reversible prerequisite that would otherwise need a spike is done. The
  element-extraction form (`theElement(pred)` = the unique `x` with `pred(x)`) is a
  narrow variant of the same schema shape; confirm it states cleanly against the
  current N-ary schema machinery when §3 needs it, but this is no longer a
  gating unknown.

Net: architecturally sound and worth doing; the model layer needs no up-front
proof (roll back if it fails). Pick it up when a chapter makes functions-as-pairs
the natural next step.
