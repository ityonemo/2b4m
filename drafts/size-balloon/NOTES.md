# The size balloon — ONE `size` for sets AND group orders

2026-10-21. Two questions from the user: can one size notion serve sets and group orders
alike? And: if a subgroup becomes a `Set`, do we lose modeling it into the group axioms?

**Both answered yes, with one precise boundary.** `size.b4m`: 512 declarations, 8 theorems.
Check with `2b4m check --draft drafts/size-balloon/size.b4m` — `--draft` is only for the
statability HOLE at the end; every theorem is fully kernel-checked.

## The construction (no language change)

1. **A group ON THE SHARED ELEMENT SORT.** `const E: Element`, `func op`, `func inverse`, the
   three group axioms, and `model ElementGroup { group.Grp: Element … }`. All of `std/group.b4m`
   transfers. Two facts make this legal: a model CAN target an imported sort (precedents
   `std/collection.b4m` → `Set`, `std/integer/mod-n-listing.b4m` → `Zn`), and `opCommutative`
   is OPT-IN, so no abelian requirement.
2. **The carrier as a set: `complement(emptyset)`**, the universe. `std/set.b4m` has no
   comprehension and no universe constant, but the complement of empty IS everything
   (`everyElementIsInTheCarrier`), and every set is a subset of it.
3. **A subgroup as a SET VALUE.** `pred isSubgroup(s: Set)` with the subgroup criterion as an
   axiom. Then `forall h: Set; isSubgroup(h) -> …` QUANTIFIES OVER SUBGROUPS — the thing a
   predicated sort cannot do, and the shape of 13 of the corpus's 26 stated limits.

## The three tests

| test | what it needs from BOTH worlds | result |
|---|---|---|
| `aSubgroupOfAFiniteGroupHasNonzeroOrder` — `hasSize(carrier, n) -> isSubgroup(h) -> size(h) != ZERO` | counting (`subsetOfFiniteIsFinite`, `sizeIsTheSize`, `sizeZeroIsEmpty`) meets group structure (`member(E, h)`) | ✓ |
| `aMemberWithItsInverseGivesTheIdentityInsideTheSubgroup` | a TRANSFERRED group theorem (`opInverseRight` — a theorem, not an axiom) holds of set members: the model landed on the very sort `Set` ranges over | ✓ |
| `cancellationHoldsInsideH` | a NAMED subgroup `const H: Set` is re-entered as a group: carve `sort HSort = Element where inH` with `inH(x) iff member(x, H)`, nominate the closure facts, guarded `model HGroup`, and `group.cancelLeft` transfers inside H | ✓ |

## The answer to "do we lose modeling"

**NO for a named subgroup** — TEST 3 is exactly that, and the Element-level axioms AUTO-WEAKEN
to `HSort` (the same device `std/permutation/symmetric.b4m` relies on for `composeAssoc`).

**YES for a QUANTIFIED one.** `sort X = Element where inH` takes a predicate SYMBOL. You cannot
carve a sort from a bound `h: Set`; that is a DEPENDENT SORT, which the language lacks (the
same ground `zn-via-models-spike` ruled out indexed sorts). So the boundary is precisely:
*"for EVERY subgroup, reason INSIDE it."* Note that is also Sylow I's shape — it inducts over
subgroups it must enter (centralizers), so this is the same wall seen from the other side.

## Statability, and the next wall

`hole lagrangeInSizeVocabulary: hasSize(carrier, n) -> isSubgroup(h) -> divides(size(h), n)`
ELABORATES — Lagrange is statable in size vocabulary. PROVING it needs cosets AS SETS: the
image of `h` under left-multiplication by `g`. That is **SET comprehension, which
`std/set.b4m` lacks**. `functionFromGraph` (`std/function.b4m:90`) is FUNCTION comprehension —
a total single-valued spec yields an `Fn` — not set comprehension. This is a design decision
(one comprehension schema? per-instance axioms?), not a transcription task, and it is the
single thing standing between this balloon and Lagrange.

## Trust surface (`--axioms`)

My 3 group axioms + `subgroupDef`, then only genuine `std` primitives: `set.b4m` ×6,
`function.b4m` ×3 (incl. `functionFromGraph`), `peano.b4m` ×5 + `induction`, `order.b4m` ×2,
`finite.b4m`'s `numeralInjective`/`segmentMember` and its definition clauses. Nothing
degenerate. The hole is uncited, so it is invisible to `--axioms`, as the cheatsheet says.

## Two tooling findings

- **A DEFINITION BLOCK cannot nest a quantifier in a clause.**
  `pred isSubgroup(s: Set): isSubgroup(s) iff (… forall a, b: Element; …)` fails with
  `cannot infer the sort of 'a'`. ZERO definition blocks in `std` nest one, so nobody had hit
  it. Fallback is `pred` + an explicit axiom, which is what `std/subgroup.b4m` does anyway.
- The listing-based `|G| = n` in `std/group/*` and the size-based `|G|` here are two
  encodings of one idea. The bridge theorem `listsTheGroup(v, n) <-> hasSize(carrier, n)` is
  NOT attempted; with it, Lagrange and everything proved in listing vocabulary would translate
  to size vocabulary without re-proof. Worth doing before any re-proof.

## The structural observation

Had `std`'s group theory been built ON `element.Element` from the start, `Set` and `size`
would have been available to it all along. The separate `group.Grp` sort is what kept the two
worlds apart — not any limit of the language.

## Landed (2026-10-22)

- `setFromPredicate` → `std/set.b4m` (+ `std/set/examples.b4m`), commit e173ddd.
- The balloon minus the hole → `std/group/size.b4m` (7 theorems: the two tests plus
  `theCarrierIsASubgroup`, `aSubgroupOfAFiniteGroupIsFinite`,
  `aProperSubgroupOfAFiniteGroupIsSmaller`); test 3 and `reverse.b4m`'s theorem →
  `std/group/size-examples.b4m` (5 theorems). This directory stays as the record of the
  spike; the hole `lagrangeInSizeVocabulary` lives only here.
- The user's ruling on the design questions the balloon raised: NO parameterized sorts —
  sorts over sorts are `model` with restated axioms (std/collection.b4m), sorts over values
  are const + reading predicate + `where`. Recorded in GUIDE.md `### KEYWORD: model`.
