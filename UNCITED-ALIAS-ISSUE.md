# The uncited-alias hole

**An alias whose target does not exist still passes `2b4m check`, as long as nothing in the
file uses the alias.** Surfaced by the AATA audit (a whole chapter rested on a misspelled
import path behind a green gate) but it is an ENGINE issue, not an AATA one.

## What passes today

Verified 2026-10-21 against HEAD. Repros in `drafts/uncited-alias/`.

**A dangling MEMBER of a real file:**

    import group_lagrange <<< "std/group/lagrange.b4m"   // the file exists
    sort G = group_lagrange.Grp                          // makes the import "used"
    fact lagrange = group_lagrange.noSuchTheoremAtAll    // this name does NOT exist
    → OK: 3 declarations, 0 theorems proven, exit 0

**A dangling FILE, behind an alias that IS used:**

    import lib <<< "no-such-file.b4m"
    sort A = lib.X
    const Z: A                        // without this, the unused-alias check fires instead
    → OK: 3 declarations, 0 theorems proven, exit 0

One cause for both: resolution is DEMAND-DRIVEN, and a DECLARATION is never demanded — only
a proof demands anything. So the target of an alias with no proof above it is never looked
up, however heavily the alias is used. Measured: all five alias kinds (`sort`, `pred`,
`func`, `const`, `fact`) accept a nonexistent target. (`define` cannot be aliased
cross-namespace, so there is no sixth.)

**What the landed checks DO catch, so as not to overstate this.** `8b7b6d7` closes the case
where nothing mentions the namespace; `34355ee` closes the case where nothing uses the alias.
Both repros above are built to evade them honestly — the import is mentioned and the alias is
used — because that is what is left. The narrower claim is the accurate one: **a syntactic
check can tell you a name was MENTIONED; only resolution can tell you it resolves.**

Root cause located at **`src/Engine/ParseTask.zig:255-262`**: the root scan racks a ProveTask
for `.theorem => .local` only, and `.alias => {}` is an explicit no-op. A
`check --trace-facts` on the dangling case shows no `[fetch]` event at all.

## What is already fixed, and why it does not cover this

`8b7b6d7` made an **uncited import** a hard error — a parse-time syntactic check in
`src/parser.zig` (an `unused_imports` map filled at the import decl, drained in `stamp` by
any `X.name` qualifier and at a theory-rule argument like `using import(X) thm`, reported at
`parseFile`'s tail).

That closes the case where nothing mentions the namespace at all — which is what `aata/6.2`
was. `34355ee` then made an unused non-`fact` alias an error too, closing a second slice.
Neither closes the cases above: in both, the import is mentioned AND the alias is used.

## Why the same mechanism cannot be extended to declarations

Tried on a branch (`unused-alias-check`), measured, and abandoned as stated — the findings
are worth keeping:

1. **An import is a CONSUMPTION; a declaration is a PUBLICATION.** "This file never reaches
   it" is locally decidable. "Nothing needs this" is a whole-corpus question a parser cannot
   answer.
2. **470 distinct downstream references to non-`fact` forwards (835 total).**
   `std/permutation/simplicity.b4m` uses `permutation.transposition` 98 times where that name
   is an alias in `std/permutation.b4m`; one aata file uses `peano.less_than` 49 times,
   forwarded there from `std/order.b4m`. A façade re-exporting its sub-theories' vocabulary
   is the intended practice, so "unused in its own file" does not mean dead.
3. **The AGGREGATOR requirement, which is soundness rather than convenience.**
   `std/peano.b4m` must keep `pred less_than` even though it never says `less_than` itself:
   16 neighbouring `fact` re-exports are PHRASED in it, and citing `peano.trichotomy` yields
   `… less_than(a,b) or a = b or less_than(b,a)`. Deleting it left `peano.b4m` passing ALONE
   (93 decls, 17 theorems) and failing the LIBRARY sweep with `reference not found` — an
   undemanded `fact` is never resolved, so only a whole-library strict run sees it.
4. **One breakage class is unfixable in a parser, in principle.** An accelerant resolves
   lemmas by BARE NAME at proof time. Deleting `func prev` from `std/integer/divides.b4m`
   made an `arithmetic` step uncertifiable — no syntactic analysis can predict a reference the
   accelerant generates later.

## Where a fix belongs

**`--library`**, which already sees the whole root set and would count those 835 references
as uses.

**The blocker is that no symbol-usage graph exists.** The unused-axiom check rides on
`ctx.axiom_taint` — per proven theorem, the facts its proof rests on. Sorts, consts, funcs
and preds are used by appearing in STATEMENTS AND TERMS, not in a citation closure, and every
`Context` side table is fact-level (`axiom_taint`, `hole_taint`, `model_discharged`).
Building that graph is the design question to answer first.

The narrower alternative, which does not need the graph: **resolve every `fact` alias AT
DECLARATION** rather than on first citation. That closes the dangling-member case directly
and retires the aliasing loophole the whole Class-1 AATA defect class depended on. It cuts
against the demand-driven design, which is the trade to weigh.
