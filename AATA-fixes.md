# AATA transcription audit — WHAT REMAINS

**Status 2026-10-20: the transcription work is COMPLETE.** Zero main-text one-line
re-exports remain, zero chapters prove nothing (bar §4.3, correctly), and Theorem 9.17 is
proved. What is left is one engine question, listed below.

**Earlier status note:** `check aata` is green at **40 files / 422
theorems** (was 331 when the audit opened), `check std --library` strict at 109 files /
1484, `zig build test` exit 0. This file has been pruned to the open items; the
resolved per-chapter defect lists are in the git history (see the commits from
`aata: Stage 0 —` through `std + aata §9.2:`).

## The governing rules, for anyone picking this up

**Which theorems must be written out** (user ruling, 2026-10-18). Only where Judson
signals a proof is expected: he gives a `<proof>`, or says "left as an exercise", or says
"left to the reader". A result he states **flatly** has no proof structure to transcribe
and legitimately keeps a citation. Measured against the XML: 64 `<proof>` + 6 cleanly
attached forwards = ~70 in scope; **16 bare statements are not defects** (Corollary 6.10,
Theorem 6.15, Fermat's Little Theorem, the Third Isomorphism Theorem, $|D_n| = 2n$,
every-permutation-is-a-product-of-transpositions, and others).

**When in doubt, put the full theorem into aata** (user ruling, 2026-10-19). Imports from
`std` stay legal — alias the axioms, objects and helper lemmas a proof needs as *inputs* —
but a theorem itself must not be an alias or a one-line re-export.

**Prose must be Judson's.** The only legitimate uses of "Judson …" are (a) a real language
limit, (b) an infeasible calculation, (c) a deliberate divergence reading "Judson does X,
we are doing Y" — and all three must sit in a markdown blockquote aside. Import-horizon
reasoning ("which Judson has in hand") is a defect. **Attribution headers stay.**
**`Deferred:` / `Skipped` blocks stay exactly as they are**, including the `std` paths
inside them (user ruling, 2026-10-19).

---

# OPEN ITEMS

## 1. The engine question — NEXT, to be done collaboratively

**Should `check` fail on an unresolvable import when no alias from it is cited?** Today it
does not. `aata/6.2` imported a nonexistent `std/group/group_lagrange.b4m` and passed; and
even with the path corrected, `fact lagrange = group_lagrange.noSuchTheorem` *still*
passes, because an uncited `fact` alias is never resolved. That hole is why ten chapters
could prove nothing behind a green gate.

Two candidate fixes:
- resolve every import eagerly; or
- resolve every `fact` alias **at declaration** rather than on first citation.

The second is stronger — it would retire the aliasing loophole entirely, which is the
mechanism the whole Class-1 defect class depended on. Both need a judgement about cost: the
engine is demand-driven by design, and eager resolution cuts against that.

## 2. The duplicate catalog (158 entries) — asides to paste

Regenerate with `python3 drafts/aata-audit/dup.py`. Each entry is an aata theorem whose
statement already exists in `std`, matched modulo variable, sort and theorem names, with
the aside pre-written:

> NB: This theorem exists in std in `file:line:theorem_name`

**Duplication in `std` is encouraged** — this is a cross-reference, not a delete list. The
count rose 84 → 158 over the sweep because writing theorems out *created* matches. Entries
with two `std` rows have the statement in two theories; cite whichever the chapter is
layered on.

**Caveat before pasting**: `std` line numbers drift. Re-run the script rather than trusting
the numbers below if `std/` has changed since 2026-10-20.



### aata/1.2.1-sets-exercises.md — 5

- **`unionAsThreePieces`** (`aata/1.2.1-sets-exercises.md:125`)
  > NB: This theorem exists in std in `std/set.b4m:1268:unionAsThreePieces`

- **`unionMinusRight`** (`aata/1.2.1-sets-exercises.md:138`)
  > NB: This theorem exists in std in `std/set.b4m:1261:unionMinusRight`

- **`differenceOverUnion`** (`aata/1.2.1-sets-exercises.md:149`)
  > NB: This theorem exists in std in `std/set.b4m:1277:differenceOverUnion`

- **`intersectionOverDifference`** (`aata/1.2.1-sets-exercises.md:162`)
  > NB: This theorem exists in std in `std/set.b4m:1286:intersectionOverDifference`

- **`symmetricDifference`** (`aata/1.2.1-sets-exercises.md:176`)
  > NB: This theorem exists in std in `std/set.b4m:1295:symmetricDifference`


### aata/1.2.1-sets.md — 14

- **`unionIdempotent`** (`aata/1.2.1-sets.md:167`)
  > NB: This theorem exists in std in `std/set.b4m:73:unionIdempotent`

- **`intersectionIdempotent`** (`aata/1.2.1-sets.md:232`)
  > NB: This theorem exists in std in `std/set.b4m:132:intersectionIdempotent`

- **`differenceSelf`** (`aata/1.2.1-sets.md:297`)
  > NB: This theorem exists in std in `std/set.b4m:191:differenceSelf`

- **`unionEmpty`** (`aata/1.2.1-sets.md:375`)
  > NB: This theorem exists in std in `std/set.b4m:256:unionEmpty`

- **`intersectionEmpty`** (`aata/1.2.1-sets.md:449`)
  > NB: This theorem exists in std in `std/set.b4m:321:intersectionEmpty`

- **`unionAssociative`** (`aata/1.2.1-sets.md:531`)
  > NB: This theorem exists in std in `std/set.b4m:386:unionAssociative`

- **`intersectionAssociative`** (`aata/1.2.1-sets.md:638`)
  > NB: This theorem exists in std in `std/set.b4m:487:intersectionAssociative`

- **`unionCommutative`** (`aata/1.2.1-sets.md:748`)
  > NB: This theorem exists in std in `std/set.b4m:588:unionCommutative`

- **`intersectionCommutative`** (`aata/1.2.1-sets.md:829`)
  > NB: This theorem exists in std in `std/set.b4m:663:intersectionCommutative`

- **`unionDistributesOverIntersection`** (`aata/1.2.1-sets.md:914`)
  > NB: This theorem exists in std in `std/set.b4m:738:unionDistributesOverIntersection`

- **`intersectionDistributesOverUnion`** (`aata/1.2.1-sets.md:1035`)
  > NB: This theorem exists in std in `std/set.b4m:849:intersectionDistributesOverUnion`

- **`deMorganUnion`** (`aata/1.2.1-sets.md:1178`)
  > NB: This theorem exists in std in `std/set.b4m:960:deMorganUnion`

- **`deMorganIntersection`** (`aata/1.2.1-sets.md:1297`)
  > NB: This theorem exists in std in `std/set.b4m:1065:deMorganIntersection`

- **`disjointDifferences`** (`aata/1.2.1-sets.md:1426`)
  > NB: This theorem exists in std in `std/set.b4m:1170:disjointDifferences`


### aata/1.2.2-functions-exercises.md — 2

- **`composeAssoc`** (`aata/1.2.2-functions-exercises.md:33`)
  > NB: This theorem exists in std in `std/function/invertible.b4m:36:composeAssoc`

- **`composeInvertible`** (`aata/1.2.2-functions-exercises.md:136`)
  > NB: This theorem exists in std in `std/function/invertible.b4m:271:composeInvertible`


### aata/1.2.2-functions.md — 1

- **`composeAssoc`** (`aata/1.2.2-functions.md:178`)
  > NB: This theorem exists in std in `std/function/invertible.b4m:36:composeAssoc`


### aata/10.1-factor-groups-and-normal-subgroups.md — 7

- **`conjugationLandsInTheSubgroupIffCosetsCoincide`** (`aata/10.1-factor-groups-and-normal-subgroups.md:102`)
  > NB: This theorem exists in std in `std/group/normal.b4m:46:conjugationLandsInTheSubgroupIffCosetsCoincide`

- **`theFactorOperationIsWellDefined`** (`aata/10.1-factor-groups-and-normal-subgroups.md:384`)
  > NB: This theorem exists in std in `std/group/normal.b4m:313:theFactorOperationIsWellDefined`

- **`theFactorGroupIsAssociative`** (`aata/10.1-factor-groups-and-normal-subgroups.md:505`)
  > NB: This theorem exists in std in `std/group/factor.b4m:143:opQAssoc`

- **`theFactorGroupHasAnIdentity`** (`aata/10.1-factor-groups-and-normal-subgroups.md:581`)
  > NB: This theorem exists in std in `std/group/factor.b4m:220:opQIdentityLeft`

- **`theFactorGroupHasInverses`** (`aata/10.1-factor-groups-and-normal-subgroups.md:615`)
  > NB: This theorem exists in std in `std/group/factor.b4m:255:opQInverseLeft`

- **`theCanonicalMapIsAHomomorphism`** (`aata/10.1-factor-groups-and-normal-subgroups.md:657`)
  > NB: This theorem exists in std in `std/group/factor.b4m:341:clsPreservesOp`

- **`theCanonicalMapsKernelIsN`** (`aata/10.1-factor-groups-and-normal-subgroups.md:679`)
  > NB: This theorem exists in std in `std/group/factor.b4m:365:clsKernelIsN`


### aata/10.2-the-simplicity-of-the-alternating-group.md — 3

- **`everyEvenPermutationIsAProductOfThreeCycles`** (`aata/10.2-the-simplicity-of-the-alternating-group.md:77`)
  > NB: This theorem exists in std in `std/permutation/alternating.b4m:3348:everyEvenPermutationIsAProductOfThreeCycles`

- **`theAlternatingGroupGetsAThreeCycleFromJudsonsCases`** (`aata/10.2-the-simplicity-of-the-alternating-group.md:267`)
  > NB: This theorem exists in std in `std/permutation/alternating-identities.b4m:21572:theAlternatingGroupGetsAThreeCycleFromJudsonsCases`

- **`theAlternatingGroupIsSimpleAtItself`** (`aata/10.2-the-simplicity-of-the-alternating-group.md:308`)
  > NB: This theorem exists in std in `std/permutation/simplicity.b4m:787:theAlternatingGroupIsSimpleAtItself`


### aata/11.1-group-homomorphisms.md — 15

- **`phiPreservesIdentity`** (`aata/11.1-group-homomorphisms.md:109`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:128:phiPreservesIdentity`
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:130:phiPreservesIdentity`

- **`phiPreservesInverses`** (`aata/11.1-group-homomorphisms.md:134`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:154:phiPreservesInverses`

- **`theImageHasTheIdentity`** (`aata/11.1-group-homomorphisms.md:187`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:416:theImageHasTheIdentity`

- **`theImageIsClosedUnderTheOperation`** (`aata/11.1-group-homomorphisms.md:206`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:436:theImageIsClosedUnderTheOperation`

- **`theImageIsClosedUnderInverses`** (`aata/11.1-group-homomorphisms.md:289`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:520:theImageIsClosedUnderInverses`

- **`thePreimageHasTheIdentity`** (`aata/11.1-group-homomorphisms.md:343`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:591:thePreimageHasTheIdentity`

- **`thePreimageIsClosedUnderTheOperation`** (`aata/11.1-group-homomorphisms.md:356`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:604:thePreimageIsClosedUnderTheOperation`

- **`thePreimageIsClosedUnderInverses`** (`aata/11.1-group-homomorphisms.md:400`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:648:thePreimageIsClosedUnderInverses`

- **`thePreimageOfANormalSubgroupIsNormal`** (`aata/11.1-group-homomorphisms.md:429`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:681:thePreimageOfANormalSubgroupIsNormal`

- **`theKernelHasTheIdentity`** (`aata/11.1-group-homomorphisms.md:507`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:197:theKernelHasTheIdentity`

- **`theKernelIsClosedUnderTheOperation`** (`aata/11.1-group-homomorphisms.md:520`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:284:theKernelIsClosedUnderTheOperation`

- **`theKernelIsClosedUnderInverses`** (`aata/11.1-group-homomorphisms.md:588`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:353:theKernelIsClosedUnderInverses`

- **`theKernelIsNormal`** (`aata/11.1-group-homomorphisms.md:633`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:211:theKernelIsNormal`

- **`aTrivialKernelMakesPhiInjective`** (`aata/11.1-group-homomorphisms.md:716`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:771:aTrivialKernelMakesPhiInjective`

- **`anInjectivePhiHasATrivialKernel`** (`aata/11.1-group-homomorphisms.md:812`)
  > NB: This theorem exists in std in `std/group/homomorphism.b4m:868:anInjectivePhiHasATrivialKernel`


### aata/11.2-the-isomorphism-theorems.md — 13

- **`theCanonicalMapIsAHomomorphism`** (`aata/11.2-the-isomorphism-theorems.md:37`)
  > NB: This theorem exists in std in `std/group/factor.b4m:341:clsPreservesOp`

- **`theCanonicalMapsKernelIsN`** (`aata/11.2-the-isomorphism-theorems.md:59`)
  > NB: This theorem exists in std in `std/group/factor.b4m:365:clsKernelIsN`

- **`etaIsWellDefined`** (`aata/11.2-the-isomorphism-theorems.md:162`)
  > NB: This theorem exists in std in `std/group/first-isomorphism.b4m:152:etaIsWellDefined`

- **`etaPreservesOp`** (`aata/11.2-the-isomorphism-theorems.md:203`)
  > NB: This theorem exists in std in `std/group/first-isomorphism.b4m:194:etaPreservesOp`

- **`etaIsInjective`** (`aata/11.2-the-isomorphism-theorems.md:262`)
  > NB: This theorem exists in std in `std/group/first-isomorphism.b4m:255:etaIsInjective`

- **`hSitsInsideTheProduct`** (`aata/11.2-the-isomorphism-theorems.md:723`)
  > NB: This theorem exists in std in `std/subgroup/product.b4m:544:hSitsInsideTheProduct`

- **`hOverNHasTheIdentity`** (`aata/11.2-the-isomorphism-theorems.md:1086`)
  > NB: This theorem exists in std in `std/group/correspondence.b4m:122:hOverNHasTheIdentity`

- **`hOverNIsClosedUnderTheOperation`** (`aata/11.2-the-isomorphism-theorems.md:1102`)
  > NB: This theorem exists in std in `std/group/correspondence.b4m:138:hOverNIsClosedUnderTheOperation`

- **`hOverNIsClosedUnderInverses`** (`aata/11.2-the-isomorphism-theorems.md:1182`)
  > NB: This theorem exists in std in `std/group/correspondence.b4m:579:hOverNIsClosedUnderInverses`

- **`thePullbackIsClosedUnderTheOperation`** (`aata/11.2-the-isomorphism-theorems.md:1236`)
  > NB: This theorem exists in std in `std/group/correspondence.b4m:306:thePullbackIsClosedUnderTheOperation`

- **`thePullbackContainsN`** (`aata/11.2-the-isomorphism-theorems.md:1280`)
  > NB: This theorem exists in std in `std/group/correspondence.b4m:386:thePullbackContainsN`

- **`thePullbacksImageIsS`** (`aata/11.2-the-isomorphism-theorems.md:1315`)
  > NB: This theorem exists in std in `std/group/correspondence.b4m:425:thePullbacksImageIsS`

- **`equalImagesMakeTheSubgroupsEqual`** (`aata/11.2-the-isomorphism-theorems.md:1391`)
  > NB: This theorem exists in std in `std/group/correspondence.b4m:641:equalImagesMakeTheSubgroupsEqual`


### aata/2.1-induction-exercises.md — 3

- **`sumOfSquares`** (`aata/2.1-induction-exercises.md:102`)
  > NB: This theorem exists in std in `std/integer/sum.b4m:266:sumOfSquares`

- **`sumOfCubes`** (`aata/2.1-induction-exercises.md:120`)
  > NB: This theorem exists in std in `std/integer/sum.b4m:399:sumOfCubes`

- **`sumOfArithmeticProgression`** (`aata/2.1-induction-exercises.md:311`)
  > NB: This theorem exists in std in `std/integer/sum.b4m:522:sumOfArithmeticProgression`


### aata/2.2-division-algorithm.md — 4

- **`remaindersEqual`** (`aata/2.2-division-algorithm.md:133`)
  > NB: This theorem exists in std in `std/integer/divides.b4m:1462:remaindersEqual`

- **`divisionAlgorithmUnique`** (`aata/2.2-division-algorithm.md:281`)
  > NB: This theorem exists in std in `std/integer/divides.b4m:1634:divisionAlgorithmUnique`

- **`remainderSetHasLeast`** (`aata/2.2-division-algorithm.md:466`)
  > NB: This theorem exists in std in `std/integer/divides.b4m:1976:remainderSetHasLeast`

- **`divisionAlgorithmExists`** (`aata/2.2-division-algorithm.md:641`)
  > NB: This theorem exists in std in `std/integer/divides.b4m:2348:divisionAlgorithmExists`


### aata/2.3-primes.md — 12

- **`dividesElim`** (`aata/2.3-primes.md:100`)
  > NB: This theorem exists in std in `std/primes.b4m:124:dividesElim`

- **`addLeftSwap`** (`aata/2.3-primes.md:252`)
  > NB: This theorem exists in std in `std/complex.b4m:230:addLeftSwap`
  > NB: This theorem exists in std in `std/field.b4m:163:addLeftSwap`
  > NB: This theorem exists in std in `std/field/order.b4m:292:addLeftSwap`
  > NB: This theorem exists in std in `std/integer.b4m:2256:addLeftSwap`
  > NB: This theorem exists in std in `std/peano.b4m:989:addLeftSwap`
  > NB: This theorem exists in std in `std/rational.b4m:307:addLeftSwap`
  > NB: This theorem exists in std in `std/real.b4m:342:addLeftSwap`

- **`remainderIsMember`** (`aata/2.3-primes.md:305`)
  > NB: This theorem exists in std in `std/integer/divides.b4m:4525:remainderIsMember`

- **`combinationSetNonempty`** (`aata/2.3-primes.md:416`)
  > NB: This theorem exists in std in `std/integer/divides.b4m:4619:combinationSetNonempty`

- **`mulOneLeft`** (`aata/2.3-primes.md:1243`)
  > NB: This theorem exists in std in `std/field/units.b4m:237:unitsIdentityLeft`
  > NB: This theorem exists in std in `std/integer.b4m:2297:mulOneLeft`
  > NB: This theorem exists in std in `std/integer/mod-n.b4m:1163:mulOneLeft`
  > NB: This theorem exists in std in `std/integer/mod-n.b4m:1238:unitsIdentityLeft`
  > NB: This theorem exists in std in `std/peano.b4m:711:mulOneLeft`
  > NB: This theorem exists in std in `std/rational/units.b4m:138:unitsIdentityLeft`
  > NB: This theorem exists in std in `std/real/units.b4m:138:unitsIdentityLeft`

- **`mulLeftSwap`** (`aata/2.3-primes.md:1267`)
  > NB: This theorem exists in std in `std/complex.b4m:223:mulLeftSwap`
  > NB: This theorem exists in std in `std/field.b4m:122:mulLeftSwap`
  > NB: This theorem exists in std in `std/field/order.b4m:285:mulLeftSwap`
  > NB: This theorem exists in std in `std/integer.b4m:2215:mulLeftSwap`
  > NB: This theorem exists in std in `std/peano.b4m:1025:mulLeftSwap`
  > NB: This theorem exists in std in `std/rational.b4m:300:mulLeftSwap`
  > NB: This theorem exists in std in `std/real.b4m:335:mulLeftSwap`

- **`negDivides`** (`aata/2.3-primes.md:1317`)
  > NB: This theorem exists in std in `std/primes.b4m:151:negDivides`

- **`dividesDecidable`** (`aata/2.3-primes.md:1389`)
  > NB: This theorem exists in std in `std/primes.b4m:205:dividesDecidable`

- **`lessThanSuccSelf`** (`aata/2.3-primes.md:1996`)
  > NB: This theorem exists in std in `std/integer/wellordering.b4m:284:lessThanSelf`
  > NB: This theorem exists in std in `std/peano/order.b4m:876:lessThanSelf`

- **`lessThanMulGreaterThanOne`** (`aata/2.3-primes.md:2714`)
  > NB: This theorem exists in std in `std/primes/classes.b4m:634:factorBelowProduct`

- **`succMonotone`** (`aata/2.3-primes.md:3719`)
  > NB: This theorem exists in std in `std/peano/order.b4m:92:succPreservesOrder`

- **`succInjective`** (`aata/2.3-primes.md:4766`)
  > NB: This theorem exists in std in `std/integer.b4m:75:succInjective`
  > NB: This theorem exists in std in `std/integer/wellordering.b4m:46:succInjective`
  > NB: This theorem exists in std in `std/rational.b4m:677:succInjective`
  > NB: This theorem exists in std in `std/real.b4m:1049:succInjective`


### aata/3.1-integers-mod-n-exercises.md — 1

- **`mulSubtractsRight`** (`aata/3.1-integers-mod-n-exercises.md:112`)
  > NB: This theorem exists in std in `std/integer/divides.b4m:1101:distributesOverDifference`
  > NB: This theorem exists in std in `std/peano/subtraction.b4m:425:mulSubDistribLeft`


### aata/3.2-groups-exercises.md — 1

- **`affineStarIsAssociative`** (`aata/3.2-groups-exercises.md:103`)
  > NB: This theorem exists in std in `std/real/affine-group.b4m:60:starIsAssociative`
  > NB: This theorem exists in std in `std/real/affine-group.b4m:462:starAssociativeOnCut`


### aata/3.2-groups.md — 6

- **`solutionUnique`** (`aata/3.2-groups.md:428`)
  > NB: This theorem exists in std in `std/group.b4m:295:solutionUnique`

- **`cancelRight`** (`aata/3.2-groups.md:508`)
  > NB: This theorem exists in std in `std/group.b4m:363:cancelRight`

- **`cancelLeft`** (`aata/3.2-groups.md:568`)
  > NB: This theorem exists in std in `std/group.b4m:418:cancelLeft`

- **`exponentLawProduct`** (`aata/3.2-groups.md:650`)
  > NB: This theorem exists in std in `std/group/power.b4m:96:powerAdd`

- **`exponentLawPower`** (`aata/3.2-groups.md:784`)
  > NB: This theorem exists in std in `std/group/power.b4m:271:powerMul`

- **`exponentLawAbelian`** (`aata/3.2-groups.md:966`)
  > NB: This theorem exists in std in `std/group/power.b4m:651:powerProductAbelian`


### aata/3.3-subgroups-exercises.md — 1

- **`oneIsNotZero`** (`aata/3.3-subgroups-exercises.md:646`)
  > NB: This theorem exists in std in `std/rational/examples.b4m:152:successorOfZeroIsNonzero`
  > NB: This theorem exists in std in `std/real/examples.b4m:228:successorOfZeroIsNonzero`


### aata/3.3-subgroups.md — 1

- **`subgroupIsAssociative`** (`aata/3.3-subgroups.md:160`)
  > NB: This theorem exists in std in `std/subgroup.b4m:68:opAssoc`


### aata/4.1-cyclic-subgroups-exercises.md — 4

- **`productsHaveSameOrder`** (`aata/4.1-cyclic-subgroups-exercises.md:487`)
  > NB: This theorem exists in std in `std/group/order.b4m:1280:productsHaveSameOrder`

- **`lcmPowerGeneratesIntoTheIntersection`** (`aata/4.1-cyclic-subgroups-exercises.md:643`)
  > NB: This theorem exists in std in `std/group/generated.b4m:1142:lcmPowerIsInBothSubgroups`

- **`lcmPowerGeneratesTheIntersection`** (`aata/4.1-cyclic-subgroups-exercises.md:650`)
  > NB: This theorem exists in std in `std/group/generated.b4m:1346:intersectionOfPowerSubgroupsIsLcmSubgroup`

- **`torsionClosedUnderOpAbelian`** (`aata/4.1-cyclic-subgroups-exercises.md:714`)
  > NB: This theorem exists in std in `std/group/order.b4m:1398:productHasFiniteOrderAbelian`


### aata/4.1-cyclic-subgroups.md — 1

- **`cyclicClosedUnderOp`** (`aata/4.1-cyclic-subgroups.md:105`)
  > NB: This theorem exists in std in `std/group/order-divides.b4m:80:cyclicClosedOp`


### aata/4.2-complex-multiplicative-group-exercises.md — 1

- **`modulusOfConjugate`** (`aata/4.2-complex-multiplicative-group-exercises.md:44`)
  > NB: This theorem exists in std in `std/complex/modulus.b4m:116:absConj`


### aata/4.2-complex-multiplicative-group.md — 12

- **`conjugateProduct`** (`aata/4.2-complex-multiplicative-group.md:130`)
  > NB: This theorem exists in std in `std/complex/modulus.b4m:69:zTimesConjIsNormSq`

- **`modulusOfConjugate`** (`aata/4.2-complex-multiplicative-group.md:147`)
  > NB: This theorem exists in std in `std/complex/modulus.b4m:116:absConj`

- **`modulusMultiplicative`** (`aata/4.2-complex-multiplicative-group.md:170`)
  > NB: This theorem exists in std in `std/complex/modulus.b4m:204:absMul`

- **`cisProduct`** (`aata/4.2-complex-multiplicative-group.md:240`)
  > NB: This theorem exists in std in `std/complex/polar.b4m:376:cisAdd`

- **`polarProduct`** (`aata/4.2-complex-multiplicative-group.md:324`)
  > NB: This theorem exists in std in `std/complex/polar.b4m:518:polarProduct`

- **`modulusOfCis`** (`aata/4.2-complex-multiplicative-group.md:368`)
  > NB: This theorem exists in std in `std/complex/polar.b4m:492:absOfCis`

- **`deMoivre`** (`aata/4.2-complex-multiplicative-group.md:394`)
  > NB: This theorem exists in std in `std/complex/polar.b4m:624:deMoivrePolar`

- **`rootAngleExists`** (`aata/4.2-complex-multiplicative-group.md:532`)
  > NB: This theorem exists in std in `std/complex/polar.b4m:831:rootAngleExists`

- **`rootsOfUnity`** (`aata/4.2-complex-multiplicative-group.md:584`)
  > NB: This theorem exists in std in `std/complex/polar.b4m:769:rootsOfUnity`

- **`circleGroupHasOne`** (`aata/4.2-complex-multiplicative-group.md:645`)
  > NB: This theorem exists in std in `std/complex/polar.b4m:886:circleHasOne`

- **`circleGroupClosedUnderProduct`** (`aata/4.2-complex-multiplicative-group.md:670`)
  > NB: This theorem exists in std in `std/complex/polar.b4m:911:circleClosedUnderProduct`

- **`circleGroupClosedUnderInverse`** (`aata/4.2-complex-multiplicative-group.md:719`)
  > NB: This theorem exists in std in `std/complex/polar.b4m:961:circleClosedUnderInverse`


### aata/5.1-permutation-groups-exercises.md — 1

- **`twoIsSuccSuccZero`** (`aata/5.1-permutation-groups-exercises.md:396`)
  > NB: This theorem exists in std in `std/group/listing.b4m:997:twoIsSuccSuccZero`


### aata/5.1-permutation-groups.md — 12

- **`composeIsAssociative`** (`aata/5.1-permutation-groups.md:64`)
  > NB: This theorem exists in std in `std/function/invertible.b4m:36:composeAssoc`

- **`identityIsAPermutation`** (`aata/5.1-permutation-groups.md:92`)
  > NB: This theorem exists in std in `std/function/invertible.b4m:201:identityInvertible`

- **`identityActsAsTheGroupIdentity`** (`aata/5.1-permutation-groups.md:99`)
  > NB: This theorem exists in std in `std/function/invertible.b4m:140:composeIdentityLeft`

- **`symmetricGroupHasFactorialManyElements`** (`aata/5.1-permutation-groups.md:211`)
  > NB: This theorem exists in std in `std/permutation/count.b4m:2268:symmetricGroupHasFactorialManyElements`

- **`disjointCyclesCommute`** (`aata/5.1-permutation-groups.md:542`)
  > NB: This theorem exists in std in `std/permutation.b4m:490:disjointPermutationsCommute`

- **`everyPermutationIsAProductOfDisjointCycles`** (`aata/5.1-permutation-groups.md:709`)
  > NB: This theorem exists in std in `std/permutation/decomposition.b4m:1617:everyPermutationOfAFiniteSetIsAProductOfDisjointCycles`

- **`reversedIndexInRange`** (`aata/5.1-permutation-groups.md:952`)
  > NB: This theorem exists in std in `std/permutation/alternating.b4m:201:reversedIndexInRange`

- **`nothingBelowZeroIsATransposition`** (`aata/5.1-permutation-groups.md:1490`)
  > NB: This theorem exists in std in `std/permutation/alternating.b4m:122:nothingBelowZeroIsATransposition`

- **`swappingTwoLetters`** (`aata/5.1-permutation-groups.md:1871`)
  > NB: This theorem exists in std in `std/permutation/listing.b4m:130:swappingTwoLetters`

- **`listingsInBijectionHaveEqualLengths`** (`aata/5.1-permutation-groups.md:1975`)
  > NB: This theorem exists in std in `std/permutation/listing.b4m:1864:listingsInBijectionHaveEqualLengths`

- **`twoDividesNoTwoConsecutive`** (`aata/5.1-permutation-groups.md:2654`)
  > NB: This theorem exists in std in `std/peano/parity.b4m:478:twoDividesNoTwoConsecutive`

- **`evenIsNotOdd`** (`aata/5.1-permutation-groups.md:2714`)
  > NB: This theorem exists in std in `std/permutation/alternating.b4m:988:evenIsNotOdd`


### aata/6.1-cosets.md — 4

- **`elementIsInItsOwnCoset`** (`aata/6.1-cosets.md:74`)
  > NB: This theorem exists in std in `std/group/coset.b4m:58:elementIsInItsOwnCoset`

- **`cosetsAreEqualOrDisjoint`** (`aata/6.1-cosets.md:382`)
  > NB: This theorem exists in std in `std/group/coset.b4m:453:cosetsAreEqualOrDisjoint`

- **`everyCosetIsListedByTheSubgroupsLength`** (`aata/6.1-cosets.md:581`)
  > NB: This theorem exists in std in `std/group/coset.b4m:641:everyCosetIsListedByTheSubgroupsLength`

- **`translationIsInjective`** (`aata/6.1-cosets.md:834`)
  > NB: This theorem exists in std in `std/group/coset.b4m:596:translationIsInjective`


### aata/6.2-lagranges-theorem.md — 6

- **`everyCosetIsListedByTheSubgroupsLength`** (`aata/6.2-lagranges-theorem.md:95`)
  > NB: This theorem exists in std in `std/group/coset.b4m:641:everyCosetIsListedByTheSubgroupsLength`

- **`lagrange`** (`aata/6.2-lagranges-theorem.md:325`)
  > NB: This theorem exists in std in `std/group/lagrange.b4m:1792:lagrange`

- **`theSubgroupsLengthDividesTheGroups`** (`aata/6.2-lagranges-theorem.md:404`)
  > NB: This theorem exists in std in `std/group/lagrange.b4m:2021:theSubgroupsLengthDividesTheGroups`

- **`anyTwoGroupListingsHaveTheSameLength`** (`aata/6.2-lagranges-theorem.md:503`)
  > NB: This theorem exists in std in `std/group/lagrange.b4m:1876:anyTwoGroupListingsHaveTheSameLength`

- **`theOrderDividesTheGroupsLength`** (`aata/6.2-lagranges-theorem.md:655`)
  > NB: This theorem exists in std in `std/group/order-divides.b4m:306:theOrderDividesTheGroupsLength`

- **`indicesMultiplyAlongAChain`** (`aata/6.2-lagranges-theorem.md:930`)
  > NB: This theorem exists in std in `std/group/lagrange.b4m:2127:indicesMultiplyAlongAChain`


### aata/6.3-fermat-and-eulers-theorems.md — 2

- **`anElementToTheGroupsLengthIsTheIdentity`** (`aata/6.3-fermat-and-eulers-theorems.md:73`)
  > NB: This theorem exists in std in `std/group/order-divides.b4m:649:anElementToTheGroupsLengthIsTheIdentity`

- **`aMultipleOfTheOrderIsAnIdentityExponent`** (`aata/6.3-fermat-and-eulers-theorems.md:154`)
  > NB: This theorem exists in std in `std/group/order-divides.b4m:562:aMultipleOfTheOrderIsAnIdentityExponent`


### aata/7.1-private-key-cryptography.md — 1

- **`affineDecodes`** (`aata/7.1-private-key-cryptography.md:71`)
  > NB: This theorem exists in std in `std/integer/mod-n.b4m:1312:anAffineCipherWithAUnitMultiplierDecodes`


### aata/7.2-public-key-cryptography.md — 2

- **`anExponentOneAboveAMultipleOfTheOrderIsTheIdentityMap`** (`aata/7.2-public-key-cryptography.md:70`)
  > NB: This theorem exists in std in `std/group/order-divides.b4m:731:anExponentOneAboveAMultipleOfTheOrderIsTheIdentityMap`

- **`anElementToTheGroupsLengthIsTheIdentity`** (`aata/7.2-public-key-cryptography.md:152`)
  > NB: This theorem exists in std in `std/group/order-divides.b4m:649:anElementToTheGroupsLengthIsTheIdentity`


### aata/9.1-definition-and-examples.md — 14

- **`phiIsInjective`** (`aata/9.1-definition-and-examples.md:129`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:74:phiIsInjective`

- **`phiIsSurjective`** (`aata/9.1-definition-and-examples.md:165`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:112:phiIsSurjective`

- **`psiPreservesOp`** (`aata/9.1-definition-and-examples.md:241`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:160:psiPreservesOp`

- **`abelianTransfers`** (`aata/9.1-definition-and-examples.md:290`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:206:abelianTransfers`

- **`theExponentMapIsInjective`** (`aata/9.1-definition-and-examples.md:377`)
  > NB: This theorem exists in std in `std/group/generated.b4m:1266:equalPowersHaveEqualExponents`

- **`reflexivityOfIsomorphism`** (`aata/9.1-definition-and-examples.md:422`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:662:reflexivityOfIsomorphism`

- **`symmetryOfIsomorphism`** (`aata/9.1-definition-and-examples.md:485`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:631:symmetryOfIsomorphism`

- **`transitivityOfIsomorphism`** (`aata/9.1-definition-and-examples.md:512`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:754:transitivityOfIsomorphism`

- **`leftTranslationIsInjective`** (`aata/9.1-definition-and-examples.md:647`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:273:leftTranslationIsInjective`

- **`leftTranslationIsSurjective`** (`aata/9.1-definition-and-examples.md:653`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:281:leftTranslationIsSurjective`

- **`cayleyPreservesOp`** (`aata/9.1-definition-and-examples.md:702`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:356:cayleyPreservesOp`

- **`cayleyIsInjective`** (`aata/9.1-definition-and-examples.md:753`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:409:cayleyIsInjective`

- **`imageHasIdentity`** (`aata/9.1-definition-and-examples.md:842`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:501:imageHasIdentity`

- **`imageClosedUnderComposition`** (`aata/9.1-definition-and-examples.md:863`)
  > NB: This theorem exists in std in `std/group/isomorphism.b4m:523:imageClosedUnderComposition`


### aata/9.2-direct-products.md — 9

- **`prodAssoc`** (`aata/9.2-direct-products.md:81`)
  > NB: This theorem exists in std in `std/group/product.b4m:82:prodAssoc`

- **`prodIdentityLeft`** (`aata/9.2-direct-products.md:87`)
  > NB: This theorem exists in std in `std/group/product.b4m:89:prodIdentityLeft`

- **`prodInverseLeft`** (`aata/9.2-direct-products.md:93`)
  > NB: This theorem exists in std in `std/group/product.b4m:96:prodInverseLeft`

- **`prodIdentityRight`** (`aata/9.2-direct-products.md:105`)
  > NB: This theorem exists in std in `std/group/product.b4m:115:prodIdentityRight`

- **`prodInverseRight`** (`aata/9.2-direct-products.md:111`)
  > NB: This theorem exists in std in `std/group/product.b4m:122:prodInverseRight`

- **`prodCancelLeft`** (`aata/9.2-direct-products.md:117`)
  > NB: This theorem exists in std in `std/group/product.b4m:129:prodCancelLeft`

- **`pairIsIdentityIffComponentsAre`** (`aata/9.2-direct-products.md:146`)
  > NB: This theorem exists in std in `std/group/product.b4m:177:pairIsIdentityIffComponentsAre`

- **`pairPowerIsIdentityIffComponentPowersAre`** (`aata/9.2-direct-products.md:229`)
  > NB: This theorem exists in std in `std/group/product.b4m:504:pairPowerIsIdentityIffComponentPowersAre`

- **`cubeIsIdentityComponentwise`** (`aata/9.2-direct-products.md:250`)
  > NB: This theorem exists in std in `std/group/product.b4m:139:cubeIsIdentityComponentwise`


---

# SETTLED — do not reopen

## Class 1: every chapter proves its own results

Ten chapters proved **zero theorems** when the audit opened (3.2, 6.1, 6.2, 6.3, 7.2, 9.1,
9.2, 10.1, 10.2, 11.2). All now carry their mathematics. `4.3-repeated-squares` is the only
remaining zero, correctly — it is an algorithm section with no stated proposition, and says
so in the prescribed form.

Landed: Lagrange, Cayley, De Moivre, Euler, RSA correctness, Theorem 10.3, $|S_n| = n!$,
the disjoint-cycle decomposition, Theorem 9.7, Theorem 6.7, the full Second Isomorphism
Theorem, and all three Isomorphism Theorems plus Correspondence.

**Citations that are legitimate and must not be "fixed":**
1. **Schemas.** `judsonsLemmaTenTen` and `theAlternatingGroupIsSimple` are
   `theorem …(inN(Fn))`, parameterized by the subgroup predicate because there is no sort
   of subgroups. A schema has no body to lift; §10.2 instantiates both at $N = A_n$. Same
   for `splittingAListing` (`prop(Item)`).
2. **Bare statements** — see the scope ruling above.
3. **Cross-theory sort mismatches**: §10.2's two `normal.b4m` results are over `Grp` while
   that chapter speaks `Fn`.

## Class 2: prose is Judson's

Six false/contradictory claims fixed; §10.2's 142-line retrospective removed (it was nearly
half the file) with his Historical Note restored verbatim, as were §11.2's and §10.1's; all
8 import-horizon justifications stripped; §2.3's invented and colliding result numbers
dropped. Restored exposition includes §2.3's Euclidean Algorithm subsection (the 945/2415
worked example — "945" previously occurred nowhere in the corpus), his prime/composite
definition and Historical Note; §2.1's induction motivation; §1.2.3's partition and
equivalence-class definitions, his named Corollary, the mod-3 example and four relation
examples; and **§5.1's right-to-left composition convention remark**, the one omission that
affected correctness.

**Two corrections of fact**, both verified against the XML: §6.2 had misdescribed his $A_4$
argument as "exhaustion over $A_4$'s elements" (it is index 2 ⇒ $gHg^{-1} = H$, then
conjugating a 3-cycle); §7.2 had truncated his second RSA case to its first sentence.

## The five axiomatization rulings

| # | item | ruling |
|---|---|---|
| 1 | `1.2.3-partitions` `quotientContains` | definition block; `isTheClassOf` reports `— DEFINITION` |
| 2 | §4.1's three `m` axioms | derived from well-ordering |
| 3 | §4.1 `cofactorBezout` | new std lemma `cofactorsSatisfyBezout`, then derived |
| 4 | §3.3's subgroup criterion | split: converse proved, forward half a real (a) limit |
| 5 | §5.2's dihedral relations | **kept** — they are the presentation of $D_n$ |

**The audit was wrong on item 1's premise**: it said comprehension should supply
`quotientContains`, but there is **no comprehension anywhere in `std`**, and
`std/equivalence.b4m` posits classes the same way. The fix was the reporting, not the axiom.
**Item 3 needed real mathematics** — `std` had `bezout` and `coprimeBezout` but nothing
saying a gcd's cofactors are coprime, which is *why* the chapter asserted it.

## Mechanical artifacts

All fixed: 7 `less_than` text corruptions, 2 shipped "(Proof to fill:)" TODOs, a duplicated
paragraph, every exercise number in both chapter-1 exercise files (verified against the
XML), the dangling `std/group/group_lagrange.b4m` import, and 3 mispointed imports whose
name disagreed with their target.

## Lessons worth keeping

- **`--fast` is a STRUCTURAL check and that is the whole promise.** It does not resolve what
  references bind to, so a reference can bind to the **wrong declaration of the right
  shape** and pass. Not a `--fast` defect. Measured twice: `correspondence.b4m`'s
  `hHasIdentity: inHsub(EG)` vs `subgroup.b4m`'s `subgroupHasIdentity: inSubgroup(E)`
  (re-exported as `hHasIdentity`); and `complex/polar.b4m`'s `deMoivre` (cis, 2 args) vs
  `deMoivrePolar` (3 args). Risk scales with how many theories a proof cites across. Now
  recorded in `agents/2b4m-cheatsheet.md` and `GUIDE.md`.
- **A lifted proof needs its INPUTS aliased**, and dependency closure takes a few rounds;
  aliasing a std file's whole exported set at once beats chasing one error at a time.
- **Sibling std theories each declare their own group sort** (`subgroup_product.G` →
  `subgroup.b4m`, `correspondence.G` → `factor.b4m`), so lifted bodies need retyping.
- **`tautology` sees opaque atoms** — it cannot bridge `inN(e⁻¹h)`/`inN(h)`, substitute an
  equation, or flip one. A countermodel naming two atoms you believe are linked *is* the
  missing step.
- **A `define` cannot be aliased** (it is a macro) and **a definition block's clause
  variables take their sorts from argument positions**.
- **A predicated sort relativizes every binder**, so an ambient law needs an explicit
  `fix`/`generalize` to reach a guarded goal.
- When appending to a shared `std` file, **scope renames to the appended text** — a blanket
  regex broke `std/integer.b4m`'s own `ZERO`.
