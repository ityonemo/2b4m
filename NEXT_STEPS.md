# NEXT_STEPS — the demand-driven reentrant prover

Roadmap for turning proving demand-driven, on branch `reentrant-prover` (off main
`9bd80b4`). This is the summary; the full design + the immediate InternPool-datatypes
slice live in the plan file `~/.claude/plans/ok-claude-can-you-wondrous-pine.md`.

## Where we are

Landed: parse/fetch/prove task engine, InternPool (interned entities), FactKV + IdentKV
demand tables, ProveTask/FetchTask entry protocol (claim / suspend-on-in-flight / use).
The eager `elaborateAll` back-end still does the ACTUAL proving; everything so far is
behavior-neutral. **In progress (not in this doc):** enriching the InternPool datatypes
(terms, signatures, per-kind identifiers, fact formulas) — see the plan file.

## The core idea

**Any name resolution might suspend** — every sort/const/func/pred/define/axiom/theorem
name resolves through a namespace, which may reach an unparsed import or an unfetched
identifier. `ParseTask` resolves no names → never suspends; `FetchTask` and `ProveTask`
both resolve names → both can suspend. You can't save a native call stack at an arbitrary
deep resolution (Zig, no coroutines), so:

**It is ONE WALK of the theorem.** Not a separate scan pass + prove pass — a single
traversal. As the walk proceeds it carries a **live local-identifier set on the ProveTask's
ARENA** (bound vars from `fix`/`forall`/`unpack`/`lambda` + local step/block labels,
order-respecting, descoped on block exit). At each name:

- **in the local set** → resolve in-proof (it's a bound var / local label).
- **NOT in the local set** → it's a global identifier/fact → rack a `FetchTask` (or
  `ProveTask` for a cited theorem) and **SUSPEND** blocked-on it.

A fetch that finds nothing anywhere → `UndefinedError` (the demand-exhausted replacement
for today's eager "unknown identifier"). On resume, the walk continues from its saved step
position with the demanded thing now present. The local set IS the local-vs-global
discriminator — no separate oracle. It's order/scope dependent precisely because lazy
resolution makes local identifiers order-dependent.

## Three task types (split by what they PRODUCE)

- **ParseTask** — bytes → AST. Never suspends.
- **FetchTask** — a non-fact identifier (sort/const/func/pred/define/import) → its interned
  entity. Suspends on a ParseTask (unparsed import) or another FetchTask (its shape
  references another identifier, e.g. `func succ(n: Nat): Nat` must resolve `Nat`).
  Exception: a `define`'s body is stored as an unelaborated template (expanded during
  proving), so it doesn't suspend on its body's contents.
- **ProveTask** — a fact-producer → an interned `.fact`. Axiom = trivial leaf (claim,
  publish, never suspends). Theorem = the real one-walk. Schema deferred.

The Fetch/Prove split is the same fact/non-fact line as the pool's `.fact`-vs-rest.

## Free wins from the uniform demand graph

- **One cycle detector covers all cycle kinds.** Fetch and Prove suspend through the same
  `blocked_on TaskIndex` + parked-queue machinery, so a cyclic identifier dependency wedges
  identically to a proof cycle. The deferred wedge/cycle detector (run queue empty + parked
  non-empty; walk `blocked_on` to name it) catches identifier cycles, proof cycles, and
  mixed chains with zero extra code.
- **Task-on-task blocking is kind-agnostic** — a prover blocking on a ParseTask (lazy
  import) needs no special case.

## Remaining slices (after the InternPool datatypes land)

2. **Split `elaborateFile`: register decls, make the per-theorem walk callable.** The
   whole-file sweep registers sorts/syms/axioms/theorem-statements (so names resolve) but
   STOPS proof-checking theorems; the per-theorem walk becomes standalone-callable. Keep
   green via a temporary separate eager prove pass. First behavior-adjacent structural
   break; corpus should stay green.
3. **The one walk in ProveTask (the behavior SWITCH — corpus may go RED in flight).**
   ProveTask does the single traversal: local-set on its arena, demand non-locals + suspend,
   resume from saved position, lower inline. Turn OFF the temporary eager prove pass — the
   ENGINE now drives all proving, demand-first. Corpus green again = the milestone.
4. **Retire the eager pass; clean up.** `elaborateAll` no longer proof-checks.

## Out of scope / deferred

`by model(M)` (model-transfer rework), schemata (the second reentrancy kind), the
`model`-replay `fact.proof` bridge, folding `term.Pool` fully into the kernel/accelerants,
the cycle detector (edges exist; detection later), multi-threading.

## Verification (every slice)

`zig build test` + the corpus loop (`for f in std/**/*.bpa aata/**/*.md examples/**;
bpa check $f` → 70/70, excluding `examples/incorrect.bpa`), on the branch. Slice 2 stays
green; slice 3 is the switch (may go red in flight; done = byte-identical `bpa check`
output). Demand-minimality spot-check after slice 3: a small root importing a large std
tower proves only its citation closure. **Merge to main only when the branch corpus is
100% green.**
