# CONTAINER-THEORY.md — `std/indexed.b4m`, what it delivers, and the one wall it hit

Status: **the container exists and is green** (`std/indexed.b4m` + `std/indexed/examples.b4m`,
landed 2026-10-03). The postulate-sharing half works. The generic-lemma half is **blocked on a
structural property of `model`**, established by repro and recorded below — it is not a
transcription problem and not something to retry by rearranging.

## What it is

The pattern every finite-list sort in std was re-declaring by hand: an index-read list plus the
facts that say such lists can be BUILT. Seven carriers restated some subset of
singleton/prepend/concat/reverse/remove — `Seq` over groups, over permutations, over ℤ, `ZnSeq`,
`SetSeq`, `Points` — 26 postulates between them, each with a comment explaining why it could
not inherit.

`std/indexed.b4m` names it once: `sort Indexed`, `sort Item`, `at`, and the five building
postulates.

## The fold split, which was the actual design question

`std/sequence.b4m` bundles the container with a FOLD (`IDENTITY`/`combine`/`foldUpTo`), and three
of its four existence postulates carry a fold clause. That bundling is precisely what excluded
`Points`: a list of set ELEMENTS has no monoid structure, so there is nothing to fold.

So the container carries NO fold, and a carrier takes whichever layer it needs. Verified by
counting: `std/permutation/cycle.b4m` and `std/set/subsets.b4m` use zero fold clauses in their
postulates; `std/integer/mod-n-listing.b4m` uses five. The pure-container layer has real
customers.

**`Points` models the container.** Tested: `indexed.Indexed: Points`, `Item: Element`,
`at: at`, with cycle.b4m's three postulates discharging. That is the carrier the old design
could not reach.

## What a carrier gains, and what it still owns

The postulates are AXIOMS, so a model DISCHARGES them rather than inheriting them — a model
transfers theorems and discharges assumptions. A concrete list sort is still asserting that its
own lists can be built, and `--axioms` names that assertion at the carrier. Honest, and correct.

What it gains is that the SHAPE is stated once, so a carrier cannot silently ship a THINNER
postulate set than its constructions need. That was a real cost: `Points` had only
singleton+prepend, which made two different induction shapes unavailable, and the failure
presented as "my proof is wrong" rather than "this carrier is missing an axiom" (it took a
detour and a new axiom, `pointsConcat`, to find). A carrier modeling `Indexed` must discharge
all five or the model is incomplete.

## THE WALL: a model cannot deliver a source SCHEMA to a carrier

The other half of the plan was to prove generic lemmas once over `Indexed` and transfer them.
The headline case: "a list whose i-th entry is f(sᵢ) exists", written out by hand FOUR times in
std (`group_sequence.translatedSequenceExists` at 175 lines, `counting.powersAreListed`,
`permutation_sequence.mappedSequenceExists`, plus a failed attempt for `Points`).

It is a SCHEMA over the map, because the first-order kernel cannot quantify over a function
`Item -> Item`. And a schema cannot cross a model in the needed direction. All three routes,
each tried against `std/group/sequence.b4m` and then reduced to a minimal repro:

1. `[using model(M) indexed.mappedListExists]` — "is a schema obligation the model does not
   discharge".
2. Add `indexed.mappedListExists <- containerMappedList` to the model and make the stand-in's
   body that transfer — "cyclic schema instantiation". Correctly: the stand-in is what
   DISCHARGES the source, so its proof cannot be "cite the source through that discharge".
3. Skip the model, `[using instantiation indexed.mappedListExists((fun g: Grp => …))]` —
   **"expected sort 'Item', got 'Grp'"**. This is the root cause stated plainly: instantiation
   wants an `Item`-sorted map and the carrier has `Grp`. Only a model remaps `Item → Grp`, and
   route 1 says a model-cited schema needs a discharge, and route 2 says the discharge cannot be
   the transfer.

A closed loop, reproduced in 20 lines with no container involved
(`scratchpad/loop.b4m`/`loop2.b4m`): **`model` can RECEIVE a carrier's schema as a discharge but
never DELIVER a source schema to a carrier.** For schemas the direction is backwards from what
structure reuse requires.

Note this is the same wall §6.3 hit from the other side (CHAPTER6-PAINPOINTS), and the engine
work of 2026-10-02 — which made `model(M) sch(args)` parse, let a proven schema discharge, and
let a model be cited cross-file — does not move it. Those fixed four real gaps; none is this one.

## What would move it

The missing primitive is a model-aware schema INSTANTIATION: `instantiation` that takes the
model as context, so the map argument is read in the carrier's space (`Grp`) while the schema's
parameter sort (`Item`) remaps through the model. Mechanically close to what
`demandSchemaTransfer` already does with explicit args — it binds against the DISCHARGING
schema; this would bind against the SOURCE schema under the model's remap, with no discharge
required because nothing is being substituted for.

Soundness shape looks the same as today's: the instance is proved per use and the claim is
matched against it, which is what already gates (verified 2026-10-02 — a weak discharge yields
only the weak fact).

## Where this leaves things

**Landed:** the container, its examples (which is where the schema's proof is actually checked),
and `Points` demonstrated as a model.

**Not landed:** retiring any of the four hand-written mapped-list proofs, and therefore the §6.3
path is unchanged — `splittingAListing` still has to be proved per carrier.

**Not attempted:** migrating the other six carriers to model the container. Worth doing for the
shape discipline alone, but it buys no proof reuse until the wall moves, so it is cleanup rather
than leverage. Each carrier also needs weakening lemmas where its own postulates carry fold
clauses (two written for `std/group/sequence.b4m` and then reverted with the schema attempt;
they were one page and straightforward).
