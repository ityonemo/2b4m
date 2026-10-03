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

## What would move it — ATTEMPTED 2026-10-03, two of three layers done

The user identified this as the same shape as the 2026-10-02 fixes: a case rejected by an
early-out when the machinery sat downstream. That reading was right, and three layers turned
out to be involved. Two are now landed; the third is a different kind of problem.

**Layer 1 — route the no-discharge case (DONE).** `demandTransfer` errored with "the model does
not discharge" before ever reaching the instantiation path. With EXPLICIT args that is not an
error: nothing is being substituted FOR the source, so no discharge is wanted. Now routes to
`demandSchemaTransferUnder(c, universe_ix, effective_model)`.

**Layer 2 — remap the parameter sorts under the CITE's model (DONE).** `bindSchemaArgs` set
`se.model = self.model`, the citing proof's AMBIENT model — the universe in the common case,
not the model named at the cite. So the container's `Item` never became the carrier's `Grp`.
Added `bindSchemaArgsUnder` / `demandSchemaTransferUnder` with an optional override, defaulting
to today's behavior at every existing call site. The statement now remaps correctly, and the
instance task proves the body under the cite's model rather than the ambient one.

**Layer 3 — the REMAINING wall, and it is not an early-out.** Two distinct problems, both
visible once layers 1-2 are in:

- **The lambda cannot capture.** `(fun g: Grp => op(t, g))` with `t` from an enclosing `fix`
  gives "unknown identifier 't'". `demandSchemaTransfer` runs in the READ PASS, before
  step-local scope exists — which is exactly why the existing path uses the citing schema's own
  parameters (available without scope) rather than arbitrary expressions. `demandInstance`, the
  plain-`instantiation` path, receives the caller's live `Elab` as an argument; the transfer
  path has none to receive.
- **A proof BODY is not remappable the way a statement is.** With a capture-free lambda the
  error moves inside the schema's proof: `indexed.b4m:104: expected sort 'Grp', got 'Item'`,
  at a step citing `indexedSingleton` — an axiom the model discharges. The statement remaps but
  the body is left half-translated. Note the existing (working) fixtures instantiate a LOCAL
  schema, whose sorts are already the carrier's, so nothing in their bodies needs remapping.
  Transferring a schema means re-proving a source BODY under an interpretation, which is a
  different operation from α-matching a remapped statement.

So the honest state: layers 1-2 are correct and harmless (full suite + `--library` green, all
pre-existing schema fixtures pass), and they move the diagnostic from "the model does not
discharge" to the two real obstacles. But they do NOT deliver the generic-lemma reuse, and I am
not going to claim a third time that it is nearly there. What remains is (a) threading a
scope-bearing `Elab` into a read-pass demand, and (b) deciding what it means to prove a source
schema's body under a model — which may be the same question as "why does a plain theorem
transfer but a schema not", answered properly.

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
