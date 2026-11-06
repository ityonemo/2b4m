# Lazy evaluation — the demand-driven engine

Checking is **demand-driven**: nothing is proved until something asks for it. The unit of
work is a theorem, not a file, and the engine racks a task per demand and suspends it when
it needs an answer it does not yet have.

## Motivation: parallelism needs less to do, and `--fast` should do less

Two payoffs, and they pull in the same direction.

**Parallelism.** A theorem-unit task graph is naturally concurrent — independent theorems
have no ordering between them, so workers can take whatever is runnable. An eager
file-at-a-time elaborator has to finish file A before starting file B even when nothing in
B depends on A.

**`--fast` does strictly less work.** When a `using` step is trusted, no proof is generated
and nothing is kernel-checked: the word ADMITS the step (an accelerant runs its own cheap
acceptance; `model`/`import` α-match the already-proven cited statement against the claim).
The step is disclosed as accelerated. In a demand engine "do less" means *rack fewer
tasks*, which is why the saving is real rather than a constant factor.

**Nothing is cached.** A trusted admit stores no verdict, so a later strict demand redoes
the full check. Trust is per-run, never persisted.

## The run queue is a stack

Scheduling is normally LIFO. This is worth knowing because **the order is not guessable
from the source**: early-racked roots tend to parse LAST, and a task that was woken but has
not yet run sits wherever the stack put it. Do not reason about diagnostics ordering, or
write a test that depends on which of two independent failures reports first.

`--chaos[=SEED]` deliberately perturbs the choice among runnable tasks so a run explores a
different interleaving, deterministically per seed.

## How imports work under demand

An `import` binds a namespace value; it does not pull the file in. Resolution follows
qualifiers lazily and is **transitive through alias chains for free**, since each alias
binds to the target's existing `Index` rather than minting anything (see
`namespaces.md`).

The consequence that bites: **a declaration is never demanded — only a proof demands
anything.** So an alias whose target does not exist is never looked up, as long as no proof
above it cites the alias. That is the uncited-alias hole
(`../UNCITED-ALIAS-ISSUE.md`): a syntactic check can tell you a name was MENTIONED, but
only resolution can tell you it RESOLVES.

Two narrower cases are closed by syntactic checks in the parser, which is why they behave
differently from the general one:

- an **uncited import** is a hard error (nothing mentions the namespace at all);
- an **unused non-`fact` alias** is a hard error.

Both are *consumption* checks — "this file never reaches it" is locally decidable, whereas
"nothing needs this" is a whole-corpus question a parser cannot answer.

There is one exception to pure laziness worth knowing: `Elab` cannot suspend, so the
transitive reference closure of what it needs is demanded FIRST.

## Pitfalls

**An incorrect proof that is never evaluated is never caught.** If nothing demands a
theorem, its proof is not checked. A file whose only content is a schema reports
`0 theorems proven` and exits 0, because a schema body is checked at its INSTANTIATIONS —
so an uninstantiated schema is as unverified as a hole while looking green, and silent
about it.

**Consistency can be obscured.** An assumed axiom is never exercised by a proof, so a
contradictory axiom set stays green until something happens to derive from it. `--axioms`
shows what a theorem RESTS on; nothing shows what is inconsistent. Check an axiom against
the degenerate instances of every `define` it quantifies over.

**An undemanded `fact` is never resolved**, so a dangling re-export only surfaces in a
whole-library run. A file can pass alone and fail the library sweep for this reason.

## `--library` — the whole-corpus complement

`--library` over a directory additionally FAILS on any axiom declared in the directory that
no theorem in it rests on: **a library ships no unused assumptions.** It is the mode that
sees the whole root set, which is why it catches what per-file laziness cannot — including
the dangling-`fact` case above.

It rides on per-theorem axiom taint (the facts a proof rests on). Note what that does NOT
cover: sorts, consts, funcs and preds are used by appearing in STATEMENTS AND TERMS rather
than in a citation closure, and no symbol-usage graph exists — so the unused-SYMBOL half of
the same idea is not available. Note also that a rewrite named in a `simplify` set does not
appear in taint, so `--axioms` will not show it.

## See also

- `acceleration.md` — the `--fast` trust boundary per word.
- `namespaces.md` — what a namespace is, and why alias identity is by origin.
