# `local` — a declaration this file does not export

**Status: DESIGNED, not built.** User direction 2026-11-09. Sized below; nothing landed.

## The idea

`local <declaration>` marks a declaration unreachable from another file. It generalizes what
`lemma` already does for proved facts:

| | exported | not exported |
|---|---|---|
| proved fact | `theorem` | `lemma` |
| vocabulary | `sort`/`oper`/`const`/`pred`/`fact` | `local sort`/`local oper`/… |

One concept, two spellings — `lemma` is effectively `local theorem`, and whether to say so in
the docs (or actually unify the two) is open.

## Why a keyword rather than position

The alternative considered and REJECTED was positional: "vocabulary beyond the fold is
implicitly local." Measured cost of that version:

* **601** vocabulary declarations sit beyond the fold across **69** std files;
* **466 call sites in 112 files** genuinely reach across a file boundary into one
  (`complex.conj`, `complex.fromReal`, `collection.bigUnion`, `field.recip`, …).

So position-implied locality makes 601 declarations local BY ACCIDENT and breaks 466 working
call sites — a flag day. With a keyword, nothing changes until an author opts in.

Explicitness is the deeper reason: under the positional rule a declaration's visibility
depends on where the line sits, so MOVING a line silently changes the file's interface.

## `local` COMPLEMENTS the positional rule — they are different axes

User ruling: *"complement, because the positional rule only applies for --library."*

* **`local`** is SEMANTIC. The author states it; it holds in every mode, like `lemma`.
* **The positional rule** (`--library`, `.b4m` only, landed `4f9209e`) is a PUBLISHING
  convention: a published file declares its assumption surface before any proof.

Neither subsumes the other. A `local oper` in the header is fine — declared, just not yours.
A public `oper` beyond the fold is fine in a working directory and an error under `--library`.
And they compose: a file with late vocabulary gets an honest choice — hoist it, or mark it
`local` and leave it where it is.

## What it buys

`2b4m index` (landed `4a314d9`) currently prints the header, which is MOSTLY the interface —
the blind spot being that `sort`/`oper`/`const`/`pred`/`define`/`fact` are legal after the
fold, so a late declaration is silently omitted. With `local`, `index` should print the header
MINUS its `local` declarations, and then it answers exactly "what can I use from here?" —
complete by construction, with no hoist needed.

## Where it lands

* **Lexer**: `local` is FREE — not in the keyword table; 22 occurrences in the corpus, all
  prose/comments, never a declared name. (The Zig-side `ast.*.local` tag is the
  local-vs-alias discriminator, a different namespace — pick a distinct Zig spelling.)
* **Surface**: a prefix on the declaration keyword, so the parser reads it before dispatching.
* **Enforcement**: the choke points already exist from `c884c03` —
  `Site.requireExported` (the citation) and `ProveTask.factAlias` (the `fact` re-export
  bypass). Both compare FILES, not namespaces, which a model transfer requires. They would
  read the same "not exported" bit off a wider set of declaration kinds.
* **`index`**: filter `local` declarations out of the printed header.

## Open questions

1. **Does `local` subsume `lemma`?** If `lemma` == `local theorem`, keeping both is sugar.
   Keeping `lemma` is defensible (it reads as mathematics, not as visibility).
2. **`define`.** It is a MACRO, expanded before anything resolves, so "not exported" means
   something different for it — and it is currently unrestricted by user ruling. Decide
   whether it is in scope at all.
3. **Is an uncited `local` an error**, as an uncited `lemma` is (`8e5c942`)? The same argument
   applies: nothing outside can reach it, so an uncited one is reachable by nobody.
4. **Sequencing.** Worth doing AFTER something consumes `index` — a directory-level table of
   contents, which is the [[std-has-no-index]] problem ("at 1086 theorems a differently-named
   twin is invisible"). Until then the payoff is conceptual; after, a complete-by-construction
   interface is load-bearing.
