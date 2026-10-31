# A schema-arg lambda cannot bind two different sorts — and it blocks Lemma 17.12's assembly

**Found 2026-10-31**, while assembling the minimality argument for AATA Lemma 17.12. Minimal
repro in `repro.b4m`.

## The limitation

```2b4m
theorem usesIt(p(Nat, Thing)): forall i: Nat; forall t: Thing; p(i, t) -> p(i, t)
...
[using instantiation usesIt(fun i: Nat, t: Thing => spec2(i, t))]
```

```
repro.b4m:36:43: error: expected '=>', got ','
```

A schema-arg lambda takes **one shared sort annotation for all its binders** — the form every
existing caller uses is `fun y, z: Element => …` (`std/permutation/period.b4m:248`,
`std/permutation/listing.b4m:1914`, both instantiating `functionFromGraph`, whose spec is
`spec(Element, Element)` — *same* sort twice). A spec over two *different* sorts has no lambda
form at all.

## Why it blocks 17.12

`std/rational/integer-product.b4m`'s `anIndexPinnedChoiceIsRealized(spec(Nat, Q))` is the
bounded-choice schema the construction runs on. Its spec relates an INDEX to a VALUE — `Nat`
and `Q` — so it cannot be instantiated at a lambda. The workaround in the file is to declare a
nullary func (`theSubject`) and have the spec read through it:

```2b4m
func theSubject() => qpoly.QPoly
pred isADenominatorFor(i: Nat, v: Q)
axiom denominatorMeaning: … qpoly.qcoeff(theSubject, i) = rational.mul(b, recip(v))
```

**That works for ONE fixed subject and does not scale.** The minimality assembly needs the
choice at a *varying* divisor: given `d` with quotients `q`, it builds the divisor `d·e` and
needs `e`'s quotient sequence — with `d` and `e` bound inside the proof, not pinned at file
scope. Pinning would require `theQuotientSubject`, `theDivisorE`, … one nullary func per
varying argument, each usable at exactly one value, which is not a workaround but a dead end.

**Measured, not predicted:** an attempt got as far as `theQuotientWitnessesExist` (proved,
strict-green, against pinned `theQuotientSubject`/`theDivisorE`) before the scaling problem
became unavoidable. That work is reverted; the file is back at 27 theorems.

## What a fix looks like

Allow per-binder sorts in a schema-arg lambda: `fun i: Nat, v: Q => …`. The schema machinery
already handles a `spec(Nat, Q)` *declaration* — `anIndexPinnedChoiceIsRealized` is declared,
checked, and instantiated at a bare predicate name (`aDenominatorSequenceExists` does exactly
that). Only the LAMBDA surface syntax is missing, so this looks like a parser/elaborator change
rather than a semantics one. Worth confirming against the existing single-sort path before
estimating.

**Workaround if the fix is not wanted:** give the choice schema the varying arguments as
ordinary binders of the THEOREM rather than closing over them in the spec — i.e. state it as
`forall d, e: Q; … exists t: QSeq; …` with the spec taking only `(Nat, Q)` and the relation
to `d`/`e` expressed in the body. Not obviously possible for this shape; not yet attempted.

## State of 17.12

All four of Judson's stages are proved (`a7ce162` and earlier), as are well-ordering on ℚ's
naturals (`36b6a84`) and the descent facts (`45128fa`, `547781d`). What is NOT done is the
minimality assembly that ties them together, and it is blocked here — not on mathematics.

One design note worth keeping from the attempt: a first draft had **two nested wrappers**
threading the same nine hypotheses to reach a single mathematical step. That is the
throwaway-abstraction smell; the content belongs in one theorem.
