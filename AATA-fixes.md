# AATA transcription audit — WHAT REMAINS

**Status 2026-10-20: the transcription work is COMPLETE.** Zero main-text one-line
re-exports remain, zero chapters prove nothing (bar §4.3, correctly), and Theorem 9.17 is
proved, and the 159-entry duplicate catalog is placed. Of the one engine question left, the
import half is now closed (see below); the uncited-alias half remains — that is ALL that is
open.

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

## 1. The engine question — HALF CLOSED 2026-10-20

The question as recorded had two halves. **The import half is now closed; the `fact`-alias
half is still open.**

**CLOSED — an uncited import is now a hard error.** `check` fails with
`import 'X' is never used — cite it or remove it`. Implemented in `src/parser.zig` as a
PARSE-TIME syntactic check (an `unused_imports` set filled at the import decl, drained by
any `X.name` qualifier token and by a theory-rule argument like `using import(X) thm`), not
by eager resolution — the engine stays demand-driven. A misspelled path like
`std/group/group_lagrange.b4m` can no longer hide behind a green gate.

The user rejected the first design (a "used" bit set at the six engine sites that resolve a
qualifier) as overengineering, and the parser version turned out to be *more* correct as
well as far smaller: syntactic use is complete by construction, whereas the six-site version
would have been complete only until someone added a seventh resolution path. It also
dissolved the hard case — six corpus imports are used ONLY inside `model` blocks.

Landing it required removing 18 dead imports (12 in `std`, 6 in `aata`) plus 4
test/example fixtures. Both `aata/6.2`'s duplicate aliases of one file
(`group_lagrange` + `lagrange_theory`) are the residue class this now prevents.

**STILL OPEN — the uncited alias, and it is broader than `fact`.** An uncited alias is
never resolved, so both of these pass `check` with exit 0:

- a dangling MEMBER of a real file — `fact lagrange = group_lagrange.noSuchTheorem`;
- a dangling FILE reached through a mentioned import — `import lib <<< "no-such-file.b4m"`
  plus `sort A = lib.X`. The new import check correctly stays quiet here: the import IS
  mentioned. Only resolution would catch it, and nothing demands it.

**Measured 2026-10-20: all five alias kinds have the hole** — `sort`, `pred`, `func`,
`const`, `fact` each report `OK: 2 declarations` against a nonexistent file. So this is not
a `fact`-alias quirk; it is every alias.

**Root cause** (located by the plan agent, `src/Engine/ParseTask.zig:255-262`): the root
scan racks a ProveTask only for `.theorem => .local`; `.alias => {}` is an explicit no-op.
Nothing ever demands an alias, so no FetchTask is racked for its qualifier — a
`check --trace-facts` on the dangling case shows no `[fetch]` event at all.

Candidate fix: resolve aliases AT DECLARATION rather than on first citation. That retires
the loophole the whole Class-1 defect class depended on, and still needs the cost
judgement, since it cuts against the demand-driven design.

## 2. The duplicate catalog — DONE 2026-10-20

**159 cross-reference asides inserted across 29 files.** Generated and placed by
`python3 drafts/aata-audit/insert_asides.py --apply`, which regenerates the catalog
(`dup.py`) first, so it stays correct as `std` line numbers drift. Re-running is safe: it is
idempotent, recognizing all 159 and inserting nothing.

Placement (no precedent existed; set here): in PROSE, between the introducing text and the
```2b4m fence that declares the theorem. Not inside the fence — it would be parsed as 2b4m.
Not above the exercise statement — the aside annotates the proof, not the problem.

```
**Exercise 10.** Prove $A \cup B = (A \cap B) \cup (A \setminus B) \cup (B \setminus A)$.

> NB: This theorem exists in std in `std/set.b4m:1268:unionAsThreePieces`.

```2b4m
```

A theorem whose statement lives in two `std` theories gets one aside listing both, with a
bare `>` separating it from any following aside (else the next `> NB:` reads as another
bullet of the list).

**Duplication in `std` is encouraged** — these are cross-references, not a delete list.

Gate: `check aata` 40 files / 7193 declarations / 423 theorems, exit 0 — identical to
pre-insertion, as it must be, since asides are prose the checker never sees. All 29 files
fmt-clean.

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
