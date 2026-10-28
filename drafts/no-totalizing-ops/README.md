# No totalizing operations — the invariant, and ℕ's `sub` as its one violation

**USER INVARIANT (2026-10-28):** "one of the promises of 2b4m is that its stdlib never has
totalizing operations." The invariant is not currently written down anywhere — not in
`GUIDE.md`, not in `CONVENTIONS.md`, not in `agents/`. That is the first gap.

## Three things that look alike and are not

A survey of every partial-looking operation in `std/` (`sub`, `recip`, `inverse`, `sqrt`,
`prev`, `at`, `degree`, `div`, `mod`) sorts into three kinds. **Only the third violates the
invariant.**

| kind | examples | is it a problem? |
|---|---|---|
| **total and correct** | `sub` over ℤ/ℚ/ℝ | No. Subtraction really is total on a ring. |
| **unconstrained junk** | `recip(ZERO)`, `degree(ZEROP)`, `at(s, i)` past the end, `prev` on ℤ | No, and this is the library's deliberate idiom. The value exists as a function result but EVERY axiom about the symbol is guarded, so nothing can be derived about it. |
| **totalized with an asserted value** | **ℕ `sub`** | **Yes.** `subZeroLeft` ASSERTS `sub(ZERO, b) = ZERO`, so a proof can use the junk. |

`std/field.b4m:13` already documents the middle row as intentional: "`recip` is TOTAL as a
function (`recip(ZERO)` is an unconstrained junk value); the ONLY axiom about it is guarded
on `x ≠ ZERO`, so `recip(ZERO)` is never usable."

The two probe files here are the measurement:

- `nat-sub-asserts-a-lie.b4m` — `sub(ZERO, succ(ZERO)) = ZERO` is **PROVED**, strict green,
  in one step from `subZeroLeft`. That is 0 − 1 = 0 as a theorem.
- `recip-junk-is-unreachable.b4m` — the analogous `recip(ZERO) = ZERO` is **REJECTED**: the
  guarded axiom cannot be specialized to it. This is the contrast that shows the middle row
  is genuinely safe.

`div` and `mod` already carry `requires` guards (`func div(a: Nat, b: Nat) => Nat requires
b != ZERO`), so the guarded-`func` route is established in the library — `sub` is the
inconsistency, not the precedent.

## What changing it costs — measured, not estimated

14 files import `std/peano/subtraction.b4m`. The churn is wide but shallow; the real cost is
that **two theorems get weaker**, because they are unconditional only BY the truncation:

- **`mulSubDistribLeft`** (`mul(d, sub(a,b)) = sub(mul(d,a), mul(d,b))`) holds for all
  `d, a, b` today. Both sides truncate, so the `b > a` case is `d·0 = 0`. Guarded, it needs
  `b <= a` AND `mul(d,b) <= mul(d,a)` — two obligations at every use.
- **`dividesSub`** (`divides(d,a) -> divides(d,b) -> divides(d, sub(a,b))`) inherits that.
  Today it carries no ordering hypothesis at all; guarded, every caller proves the order
  first. `aata/3.1-integers-mod-n-exercises.md` cites it.

The one internal use of `subZeroLeft` is inside `mulSubDistribLeft`'s own `a = ZERO` arm.

## What it does NOT buy

**It does not unlock the `arithmetic` accelerant.** The certifier's subtraction rule fires
only when `sub` AND `neg` both resolve in scope (`Prove.zig:8910`), unfolding
`definitionOfSubtraction` into the additive fragment. ℕ has no `neg` either way, so a ℕ `sub`
goal stays in the "valid, no certifier covers the shape" case. Guarding changes the symbol's
honesty, not the accelerant's reach.

(Separately established while probing: `sub` is NOT opaque to `arithmetic`. It is in the
well-known vocabulary, resolved from scope, and the DECISION handles it over both ℕ and ℤ — a
false ℕ `sub` goal is refuted with a concrete countermodel. Over ℤ it also CERTIFIES, once
the lemmas its certificate cites are in scope; a missing one reports as a SCOPE error, not a
fragment error. Two earlier commit messages of mine said "opaque", which is wrong.)

## The options

1. **`func sub(a: Nat, b: Nat) => Nat requires lessOrEqual(b, a)`** — the honest symbol, and
   matches `div`/`mod`. Every application carries an obligation; `sub(ZERO, succ(b))` becomes
   unwritable rather than zero. Costs: the two theorems above, plus an obligation at each of
   the ~14 files' use sites.
2. **Keep totality, drop the ASSERTION** — delete `subZeroLeft`, leaving `sub(ZERO, b)` an
   unconstrained junk value, which moves ℕ `sub` from row three to row two. **MEASURED, both
   halves:**
   - The junk really does become unreachable. With `subZeroLeft` gone, `sub(ZERO, succ(ZERO))
     = ZERO` is no longer provable from the other two equations — `subSuccSucc` needs a `succ`
     on both arguments and `ZERO` is not one, `subZeroRight` needs the second argument to be
     `ZERO`. `simplify` reports "normal forms differ". So the value is not pinned indirectly.
   - Deleting it breaks **exactly one** site: `mulSubDistribLeft`'s `a = ZERO` arm
     (`subtraction.b4m:466`), and that arm is IRREPARABLE. With `a = ZERO` and `b = succ(k)`,
     both sides of `mul(d, sub(a,b)) = sub(mul(d,a), mul(d,b))` are junk, and the step proves
     them equal only because `subZeroLeft` says both are `ZERO`. The unconditional theorem IS
     the truncation; there is no weaker-hypothesis version that survives.

   So option 2 costs `mulSubDistribLeft` its unconditional form — the same casualty as option
   1, without option 1's benefit of making the symbol's partiality visible at use sites.
3. **Leave it, document it** — cheapest, but the invariant then has a known exception.

**Recommendation: option 1.** Option 2 was the attractive one on paper (smallest diff, keeps
the library's junk-value idiom) but the measurement kills its advantage: it loses the same
theorem option 1 does, while leaving `sub` total and therefore still writable at
`sub(ZERO, b)` — silently junk instead of loudly wrong, which is worse for a reader than
either alternative. If `mulSubDistribLeft` must weaken either way, take the option that also
makes every use site declare `b <= a`.

## Status

DESIGN NOTE ONLY, nothing changed. Chapter 17 does not depend on this either way — the
polynomial-degree layer uses `subInvolution` and `succOfSubSucc`, both of which already carry
`b <= a` / `b < a` hypotheses, so they survive any of the three options unchanged.
