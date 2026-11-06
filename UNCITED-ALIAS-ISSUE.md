# The uncited-alias hole

**An alias whose target does not exist still passes `2b4m check`, as long as nothing in the
file uses the alias.** Status: OPEN, re-probed.

## What passes today

Repros in `drafts/uncited-alias/`.

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

One cause for both: resolution is DEMAND-DRIVEN, and **a DECLARATION is never demanded —
only a proof demands anything.** So the target of an alias with no proof above it is never
looked up, however heavily the alias is used. All five alias kinds (`sort`, `pred`, `func`,
`const`, `fact`) accept a nonexistent target. (`define` cannot be aliased cross-namespace,
so there is no sixth.)

Root cause at **`src/Engine/ParseTask.zig:255-262`**: the root scan racks a ProveTask for
`.theorem => .local` only, and `.alias => {}` is an explicit no-op. `check --trace-facts` on
the dangling case shows no `[fetch]` event at all.

**What the landed checks DO catch**, so as not to overstate this: an **uncited import** is a
hard error (nothing mentions the namespace), and an **unused non-`fact` alias** is too. Both
repros above are built to evade them honestly — the import is mentioned and the alias is
used — because that is what is left. The accurate claim is narrow: **a syntactic check can
tell you a name was MENTIONED; only resolution can tell you it RESOLVES.**

## Why the same mechanism cannot be extended to declarations

1. **An import is a CONSUMPTION; a declaration is a PUBLICATION.** "This file never reaches
   it" is locally decidable; "nothing needs this" is a whole-corpus question a parser cannot
   answer.
2. **A façade re-exporting its sub-theories' vocabulary is the intended practice**, so
   "unused in its own file" does not mean dead — there are 470 distinct downstream references
   to non-`fact` forwards (835 total).
3. **The AGGREGATOR requirement is soundness, not convenience.** `std/peano.b4m` must keep
   `pred less_than` even though it never says `less_than` itself: 16 neighbouring `fact`
   re-exports are PHRASED in it. Deleting it leaves `peano.b4m` passing ALONE and failing the
   LIBRARY sweep with `reference not found` — an undemanded `fact` is never resolved, so only
   a whole-library strict run sees it.
4. **One breakage class is unfixable in a parser, in principle.** An accelerant resolves
   lemmas by BARE NAME at proof time, so no syntactic analysis can predict a reference the
   accelerant generates later.

## Where a fix belongs

**`--library`**, which already sees the whole root set and would count those 835 references
as uses. **The blocker is that no symbol-usage graph exists:** the unused-axiom check rides
on `ctx.axiom_taint` (per proven theorem, the facts its proof rests on), but sorts, consts,
funcs and preds are used by appearing in STATEMENTS AND TERMS rather than in a citation
closure, and every `Context` side table is fact-level. Building that graph is the design
question to answer first.

**The narrower alternative, needing no graph: resolve every `fact` alias AT DECLARATION**
rather than on first citation. That closes the dangling-member case directly and retires the
aliasing loophole an entire class of AATA defects depended on. It cuts against the
demand-driven design, which is the trade to weigh.
