# The accelerant pruning boundary

**THE INVARIANT, swept 2026-10-26 across all 17 trustable words:** `--fast` must never ADMIT a
goal the strict path REFUTES. (Distinct from the legitimate case where strict decides the goal
TRUE but can build no certificate — `--fast` admits that, by design.) Result: ten of the eleven
distinct words reject correctly; **`specialize` is the single violation**, pinned by
`tests/cases/specialize_claim_mismatch_fast.b4m`. Probes and the table:
`drafts/fast-soundness/`.

**Status:** EIGHT of the nine decision words FIXED (`arithmetic` 2026-10-24, `simplify`
2026-10-25, `polynomial`/`tautology`/`chain`/`assoc`/`assoc_commut`/`extensionality`
2026-10-26). `specialize` is the one exception and the reason is recorded below. Regression
gates: `tests/cases/{arithmetic,simplify,polynomial,tautology,chain}_false_fast.b4m` plus
`simplify_alias_fast.b4m`. The tradeoff this note
originally flagged — a slower `--fast` loop — **measured as negligible**: whole-std `--fast` is
16.8s against strict's 233.7s, still 14x, because certify-first keeps the decision off the
common path.

## What `using` means, and what `--fast` is

`using` marks a site where an **accelerant may stand in for a subtree of the check**. Each
accelerant decides for itself how much of that subtree it prunes — there is no global trust
list, and `--fast` is not a dial that switches one on. `--fast` is the mode in which an
accelerant is permitted to prune *more* than it otherwise would.

That design is right, and the producers really do differ. Measured by reading each admit
branch in `src/Engine/ProveTask/Prove.zig`:

| accelerant | retained under `--fast` | pruned |
|---|---|---|
| `chain` | goal is an equation; ≥1 cited equation; no args | the chain construction |
| `specialize` | a head is present | head resolution, ∀-peeling, premise matching |
| `tautology` | no args | the propositional decision |
| `simplify` | **nothing** | everything — and cannot do better, see below |
| `arithmetic` | **the verdict** (fixed 2026-10-24) | certificate construction |
| `instantiation` | **everything** (never prunes — see GUIDE) | nothing |

`instantiation` is the principled extreme: its entire content IS the per-instance proof, so
there is no subtree it could drop without dropping the soundness gate.

## The defect

Three accelerants prune a check that **no certificate would have produced anyway** — and so
`--fast` accepts statements that are not merely unproved but FALSE.

Measured (all four probes in `drafts/accelerant-pruning/`):

    using arithmetic  on  succ(ZERO) = succ(succ(ZERO))        --fast: OK   strict: "the statement is false"
    using simplify    on  add(ZERO, succ(ZERO)) = succ(succ(ZERO))
                                                                --fast: OK   strict: rejected
    using model(M)    on a theorem needing an UNMAPPED abstract axiom
                                                                --fast: OK   strict: rejected

The third is the one that prompted this note. A model that leaves an obligation unmapped is
rejected strictly — the guard at `Prove.zig:403` fires because the substitution affects the
unmapped axiom ("giving an axiom a free transferred leaf would let an unmapped axiom through
(unsound)"). Under `--fast` the model accelerant admits the transfer wholesale, so the
mapping is never consulted and a consumer gets, for instance, an equivalence relation whose
transitivity nothing supplied.

This violates the recorded invariant that **`--fast` and strict must agree both ways**
(`fast-strict-invariant-and-rummage-rule`, whose 5th listed cause was "fast ACCEPTED a typo'd
ref"). These are causes 6, 7 and 8.

## The principle

> **`--fast` means we do not EMIT the certificate. Every check before the certificate still
> runs.**

That is a statement about where in the pipeline the cut falls, not a judgment about which
checks matter — which makes it decidable per accelerant by inspection: find the point where
construction begins, and admit there.

Deciding `1 = 2` is false is not certificate generation — it is the precondition for there
being a certificate at all. Resolving a model's obligation overlay is not certificate
generation — it is what makes the transfer meaningful. `chain` already draws the line here
(its goal-shape check survives admit mode); `arithmetic`, `simplify` and `model` draw it in
the wrong place.

Note this is not "check more under `--fast`". It is "the pruned subtree was mis-identified".
The decision procedures already run on the strict path and already produce these verdicts;
the proposal is that the verdict, not the certificate, is the thing admit mode must keep.

## What the fix taught us

Implementing it for `arithmetic` surfaced three things the reading had not:

**1. `fallback(thm)` must admit early.** A `fallback` names a proven theorem standing in where
no certifier can build a cert; resolving it calls `resolveFactRef`, which needs the fact
DEMANDED — and admit mode has not demanded it. Running the chain first broke
`std/integer/order.b4m`. So the fallback path admits before resolving: the certifiers declined,
and what adjudicates the goal is the cited theorem, whose own proof the strict pass checks.

**2. "Valid but uncertifiable" must be ADMITTED, not failed.** Two corpus sites
(`std/integer/divides.b4m`, `std/permutation/alternating.b4m`) hit a goal the decision procedure
confirms TRUE but no certifier can certify. That is exactly the verdict `--fast` exists to
accept — the error message even says "use --fast to accept the accelerated verdict". The
boundary is therefore sharper than "retain the decision": `--fast` may accept a verdict reached
without a certificate, but may not accept a goal the decision procedure REFUTES.

**3. The real blocker was the READ PASS, not the producer.** A trusted step diverts to
`trustedReadPass`, which resolves ident-domain refs but SKIPPED `demandArithIdents` — the hook
the untrusted path uses to demand the theory's well-known names. So the admitted decision saw
`nonneg = null` and read a ℕ goal over ℤ: measured, strict decides
`less_than(a, add(a, succ(b)))` with `nonneg=true` and 2 injected guards (VALID), while the
admit path got `nonneg=false, nprems=0` (FALSE). Adding the same demand to `trustedReadPass`
fixed it — the machinery already existed, including the park channel. Two dead ends before
finding this: assembling the decision's inputs by hand in the producer (wrong fragment), and
parking from inside the producer via `error.Recover` (which SILENTLY DROPPED a theorem, 4 → 3
proven — worse than the original bug).

**4. `simplify` — FIXED 2026-10-25, in two deliberate steps.** Its decision needs each cited
rule's STATEMENT, not its proof, and the right-weight tool already existed:
`elaborateFactStatement` reads a statement and racks NO ProveTask. So `prepareRule` uses it in
admit mode, the trusted read pass demands the statements up front (where parking is free), and
admit lands after the normal-form comparison. Step 1 landed that RED on purpose — four
`fact X = ns.y` re-exports failed with "'X' has no stated formula" — so the fallout could be
seen rather than guessed at. Step 2 was one root cause: `factOrigin` gave up (`return .ready`)
when the alias target's import name had not been fetched yet, handing the caller an unresolved
alias. It now racks the fetch and suspends, as `resolveRefs` does for a qualified ref.

Two engine bugs were found on the way, both now fixed: a producer that PARKS (racks a demand,
`suspendOn`) signalled it with `error.Recover`, which `demandUsing` read as a diagnosed
REJECTION — and rejecting a step drops its LABEL from the walk, surfacing as "unknown
reference" at the NEXT step that cited it (the std/peano/divides.b4m:171 mystery). And
`producer_premise_refs` was left set on admit, making the admitted path resolve global rule
names as step labels. Lesson from the dead ends: probing readability with a call that WRITES
DIAGNOSTICS on failure makes `--fast` report errors strict never gives; demand the thing
properly in the read pass instead.

## Cost, and what remains

The feared cost did not materialize: `--fast` over std is 16.8s versus strict's 233.7s. The
decision procedure is far cheaper than the certificate it replaces, which is the whole reason
the certify-first ordering exists.

**Still open, in priority order:**

1. **`model`.** Its accelerant admits the transfer wholesale, so a partial model's unmapped
   obligation is never noticed under `--fast` (`model-partial-accepted.b4m`). Strict catches it
   via the guard at `Prove.zig:403`, so this is a `--fast`/strict divergence rather than a
   corpus unsoundness — but it is the one that matters, since the whole point of a model is
   that its obligations are discharged. Resolving the overlay does not obviously need a fetch
   the way `simplify`'s rules do, so this looks tractable.
2. **`specialize`**, as described above — it needs the claim-match moved into the producer, or
   `fvar_binds` installed before the producer runs.

## What this is NOT

An earlier draft of this discussion proposed an `abstract axiom` keyword, on the belief that
an unmapped obligation could be silently inherited through a model. **It cannot, on the strict
path** — the probe above confirms strict rejects it. So the keyword is not needed for the case
that motivated it. It would remain a genuine question only for an obligation whose statement
the model's substitution does not touch, and no instance of that is known; one should be found
before a keyword is added for it.
