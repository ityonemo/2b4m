# Lemma 12.1, decomposed

The manuscript's Lemma 12.1 constructs the Hilbert parameter spaces. It was previously a
hole; its proof uses nothing but standard machinery, each piece cited in the paper, so it
decomposes into axioms that really are well-known.

## What it says

> **Lemma 12.1 (Hilbert parameter spaces).** There is a countable collection of connected
> reduced complex analytic spaces `H`, each proper over `U`, with a flat family of
> subschemes `Z_H ⊂ A ×_U H`, such that every closed subscheme of every fiber `A_Π` occurs
> in at least one family. Each image `H → U` is closed analytic. Consequently the union
> `E_Hilb` of those images which are proper subsets is a countable union of proper closed
> analytic subsets of `U`.

## The standard inputs it uses

Reading its proof, every step is a citation:

- the projective Hilbert scheme and its universal flat family — [16]
- proper analytic cohomology and base change, and relative generation after shrinking — [15]
- relative Serre vanishing on the projective Hilbert scheme
- **Remmert's proper mapping theorem** — the image of a proper map is closed analytic [15]
- complex analytic spaces are locally path connected, and second countable (so at most
  countably many components)
- countably many Hilbert polynomials

So the lemma itself is assembly. What the consumer needs from it is two things: that the
components are countable and proper over `U` with closed analytic image, and hence that
`E_Hilb` is a countable union of proper closed analytic subsets.

```2b4m
sort AnalyticSpace // a parameter component H
sort AnalyticSubset // a closed analytic subset of U

pred isProperOverTheBase(h: AnalyticSpace)
pred isConnectedAndReduced(h: AnalyticSpace)
func imageInTheBase(h: AnalyticSpace) => AnalyticSubset
pred isClosedAnalytic(e: AnalyticSubset)
pred isAProperSubsetOfTheBase(e: AnalyticSubset)
pred hasEmptyInterior(e: AnalyticSubset)

// WELL-KNOWN (Remmert's proper mapping theorem, cited as [15]): the image of a proper map
// of complex analytic spaces is closed analytic.
hole remmertProperMapping cites "Grauert-Remmert, Coherent Analytic Sheaves [15]: proper mapping theorem": forall h: AnalyticSpace;
  isProperOverTheBase(h) -> isClosedAnalytic(imageInTheBase(h))

// WELL-KNOWN: a proper closed analytic subset of a connected complex manifold has empty
// interior. (This is what the Baire argument in §12.3 consumes.)
hole aProperClosedAnalyticSubsetHasEmptyInterior cites "standard: a proper closed analytic subset of a connected complex manifold has empty interior": forall e: AnalyticSubset;
  isClosedAnalytic(e) -> isAProperSubsetOfTheBase(e) -> hasEmptyInterior(e)

// LEMMA 12.1's consequence, PROVED from the two citations: a proper-over-U component whose
// image is a proper subset contributes a set with empty interior — which is exactly what
// E_Hilb is a countable union of.
theorem eachExceptionalComponentHasEmptyInterior: forall h: AnalyticSpace;
  isProperOverTheBase(h) -> isAProperSubsetOfTheBase(imageInTheBase(h)) ->
  hasEmptyInterior(imageInTheBase(h))
proof
  @generalize-h |
    fix h: AnalyticSpace {
      @given-proper |
        assume isProperOverTheBase(h) {
          @the-component-is-proper |
            isProperOverTheBase(h)
            [by hypothesis given-proper]
          @given-the-image-is-a-proper-subset |
            assume isAProperSubsetOfTheBase(imageInTheBase(h)) {
              @the-image-is-a-proper-subset |
                isAProperSubsetOfTheBase(imageInTheBase(h))
                [by hypothesis given-the-image-is-a-proper-subset]
              @the-image-is-closed-analytic |
                isClosedAnalytic(imageInTheBase(h))
                [using specialize remmertProperMapping(h) the-component-is-proper]
              @conclusion-empty-interior |
                hasEmptyInterior(imageInTheBase(h))
                [using specialize aProperClosedAnalyticSubsetHasEmptyInterior(imageInTheBase(h)) the-image-is-closed-analytic the-image-is-a-proper-subset]
            }
          @conclusion-proper-subset-gives |
            isAProperSubsetOfTheBase(imageInTheBase(h)) -> hasEmptyInterior(imageInTheBase(h))
            [by implies_intro given-the-image-is-a-proper-subset]
        }
      @conclusion-at-h |
        isProperOverTheBase(h) -> isAProperSubsetOfTheBase(imageInTheBase(h)) ->
          hasEmptyInterior(imageInTheBase(h))
        [by implies_intro given-proper]
    }
  @conclusion |
    forall h: AnalyticSpace;
      isProperOverTheBase(h) -> isAProperSubsetOfTheBase(imageInTheBase(h)) ->
      hasEmptyInterior(imageInTheBase(h))
    [by forall_intro generalize-h]
qed
```

## What remains assumed

The *existence* of the countable collection — the Hilbert scheme construction, the incidence
locus, the flatness of the pulled-back universal family. That needs coherent sheaves and
flatness, i.e. the tower this exercise avoids, and the manuscript cites [15] and [16] for it.
So it is an axiom, and a fair one: it is textbook algebraic geometry, not the paper's
contribution.

```2b4m
// WELL-KNOWN ([16] Hilbert schemes; [15] proper base change): the countable collection of
// connected reduced components, proper over U, carrying flat families, exists and covers
// every closed subscheme of every fiber.
hole theHilbertParameterSpacesExist cites "Grothendieck, Bourbaki exp. 221 [16] (Hilbert schemes) + [15] proper base change; manuscript Lemma 12.1": exists h: AnalyticSpace;
  isConnectedAndReduced(h) and isProperOverTheBase(h)
```
