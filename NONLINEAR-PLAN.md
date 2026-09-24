# Nonlinear arithmetic — plan and scope

## What "nonlinear arithmetic" actually bundles

The request "support nonlinear arithmetic" covers several capabilities of
very different difficulty. Naming them apart is the whole point, because one
of them is provably impossible and the rest are not.

| Capability | Difficulty | Accelerated? |
|---|---|---|
| Nonlinear **identities** (`(k+1)² = k²+2k+1`) | low — a canonicalizing tactic | **no** (kernel-checked rewrites) |
| Polynomial **equality entailment** (Gröbner) | medium | no (reduction is a certificate) |
| Nonlinear **inequalities** (SOS / Positivstellensatz) | hard, incomplete | yes (disclosed) |
| **Full** nonlinear decision | **impossible** (Matiyasevich) | n/a |
| Euclidean `div` / `mod` | low–medium — axiomatize + reuse Cooper | mostly no |
| Rationals / field division | separate construction | n/a here |

Key facts that shape everything below:

- **Nonlinear integer arithmetic is undecidable** (Hilbert's 10th / the MRDP
  theorem). There can be no complete decision procedure, unlike Cooper's
  algorithm for the linear fragment. So the goal is *useful incomplete
  fragments*, disclosed honestly where they fall back.
- **Polynomial normalization is equational rewriting** — commutativity,
  associativity, and distributivity are all proven `std/peano.bpa` theorems.
  So a large class of nonlinear *identities* proves with **every step kernel-checked**, with zero new
  trust surface, using exactly the fabricated-rewrite-trace machinery the
  `ac` tactic already uses. This is the high-value, low-risk rung.
- **Division over Nat is a definitional problem, not a solver problem.**
  Euclidean `div`/`mod` characterized by `a = b·q + r ∧ r < b` (guarded by
  `b ≠ 0`, which the existing `requires`/TCC machinery handles) reduces
  reasoning to *linear* arithmetic plus the defining equation. Cooper's
  algorithm already handles divisibility atoms (`k | x` — the `.div`/`.ndiv`
  nodes in `src/presburger.zig`), so this is mostly declarations + axioms,
  not new solver technology.

## Recommended scope: two rungs, both mostly kernel-checked

### Rung 1 — `polynomial` tactic (nonlinear identities, emits kernel steps) — LANDED

**STATUS (landed):** `polynomial` / `polynomial_quantified` are implemented in
`src/elaborate.zig` (`polynomialEquation` + `polyCanon`, reusing `acPlan`/
`emitJoin`; per-monomial sub-traces lifted to whole-term context via
`liftMonoTrace`, outer sum right-nested first). It is **theory-parameterized**
like `arithmetic` (`polynomial(peano)`), NOT well-known-name in local scope —
the parser's theory-arg gate generalized to an `isTheoryRule` set. Elaborated by
construction (no accelerated step). Fixtures: `tests/cases/polynomial.bpa` (green, incl.
`(a+b)²`) + `polynomial_bad.bpa` (located "sides expand differently"). The
Gauss `target` payoff was deferred: it needs `succ`-expansion, and `succ` is
kept opaque (a deliberate non-privileging decision) — √2's algebra is pure
`add`/`mul`/`ONE` and needs no `succ`. The description below is the original
design; it matches the implementation except for the theory-arg change.

A canonicalizing tactic that proves `s = t` when both are polynomials over
`add`/`mul` with the same expansion — the nonlinear analogue of `ac`. This
is the immediate payoff: it kills the residual hand-tuned `simplify` in
proofs like Gauss's `target` step (`k·(k+1) + 2·(k+1) = (k+1)·(k+2)`).

**Surface:** `claim| s = t  [by polynomial]` — no refs (lemmas by
well-known name), bare equation only (a `polynomial_quantified` companion
mirrors `simplify_quantified` later, via `peelUniversal`).

**Algorithm — canonicalize both sides to a sorted sum of sorted monomials:**
1. **Distribute** `mul` over `add` to a flat sum of products, using
   `mulAddDistribLeft`/`mulAddDistribRight` as *terminating, oriented*
   rewrite rules (distribution strictly shrinks the nesting of `mul` over
   `add`, so it terminates — unlike commutativity). Run via
   `simplify_mod.normalize` with just those two rules, exactly as `ac`
   phase-1 runs `addIsAssociative`.
2. **Normalize each monomial** — a product of atoms — with `mulIsAssociative`
   (right-nest) then a `mul`-bubble-sort by `termOrder` (the sorting
   primitive `mulLeftSwap`, a new kernel-checked std lemma — see below). Reuse the
   generalized `sortTrace` with a `mul` symbol instead of `add`.
3. **Normalize the sum of monomials** — with `addIsAssociative` then the
   `add`-bubble-sort — i.e. delegate to the `ac` machinery for the outer
   sum.
4. **Constant/one/zero folding** — `mulOneLeft`/`mulOneRight`/`mulZeroLeft`/
   `mulZeroRight`/`addZeroLeft`/`addZeroRight` collapse identity/absorbing
   factors, as terminating rules in the same normalize passes.
5. Both sides reach the same canonical polynomial iff the expansions are
   equal; `emitJoin` produces the kernel-checked certificate. Different expansions →
   located `polynomial: sides expand differently: '<nf(s)>' vs '<nf(t)>'`
   (never accelerated — this tactic has no accelerated step).

**Prerequisite std lemma** (provable with every step kernel-checked, using `simplify`/`ac`, like
`addLeftSwap` was): `mulLeftSwap: forall r, y, x; mul(x, mul(y, r)) =
mul(y, mul(x, r))` — the monomial sorting primitive. Adding it also
retroactively unblocks `ac`'s mul mode (currently errors "needs mulLeftSwap").

**Reuse, not duplicate:** the `flattenSum`/`sortTrace`/`buildComb`/`emitJoin`
machinery generalizes over the operator. Factor the op-specific bits
(`add_sym` vs `mul_sym`, the assoc/comm/swap rule indices) into a small
`AcOp` struct so `ac` and the monomial-sorting inside `polynomial` share one
implementation. This is the same generalization move that let `ac` share
`sortTrace` with the arithmetic path via `termOrder`.

**Fragment / honest limits:** identities only (`=`), not inequalities;
whole-number coefficients only (Nat); no cancellation (`x·a = x·b ⊢ a = b`
is *not* an identity — that stays with `arithmetic`/`mulCancel`). A goal with
a subtraction-like or division-like shape is out of fragment → located
error, not a false countermodel.

### Rung 2 — Euclidean `div` / `mod` (mostly linear, guarded)

Add exact integer division and remainder as **declarations + axioms**, not a
new solver:

```
func div(a: Nat, b: Nat) => Nat requires b != ZERO
func mod(a: Nat, b: Nat) => Nat requires b != ZERO
axiom divMod: forall a, b: Nat; b != ZERO ->
  add(mul(b, div(a, b)), mod(a, b)) = a
axiom modBound: forall a, b: Nat; b != ZERO -> less_than(mod(a, b), b)
```

The `b != ZERO` guards are ordinary TCC obligations (the `div_ok.bpa` /
`requires` pattern already in the kernel). Reasoning about `div`/`mod` then
reduces to linear arithmetic plus the two defining facts — and Cooper's
algorithm in `src/presburger.zig` **already** decides divisibility atoms
(`.div`/`.ndiv`), so the `arithmetic` accelerated tactic largely handles `div`/`mod`
goals once the vocabulary and axioms exist. Certificate coverage grows
incrementally as with the other C2 stages.

Placement: a new `std/division.bpa` importing `std/peano.bpa`, so it's
opt-in and the core theory stays minimal. Add `div`/`mod`/`divMod`/`modBound`
to the well-known-name set the `arithmetic` symbol resolver looks up.

## Explicitly deferred / out of scope

- **Nonlinear inequalities** (SOS, Positivstellensatz): incomplete, would be
  a *disclosed accelerated tactic*. Real but a separate, later decision — the
  kernel-checked identity tactic covers the common program-verification identities
  first.
- **Gröbner-basis equality entailment** (proving an equation *from* other
  nonlinear equations, not just an identity): medium effort, certificate-
  producing (reduction chain), but only worth it once identities land and a
  concrete need appears.
- **Rationals / field division**: a `Rational` sort construction, unrelated
  to integer nonlinearity. This is what the sqrt(2) proof needs; track it
  there, not here.
- **Full nonlinear decision**: impossible (undecidable). Not a goal; the
  disclosure/`--pure` machinery keeps every incomplete fallback honest.

## Sequencing

1. **`mulLeftSwap`** std lemma (kernel-checked; also unblocks `ac`'s mul mode).
2. **`AcOp` refactor** — parameterize the `ac` sort machinery over the
   operator so `add` and `mul` sorting share code.
3. **`polynomial` tactic** — distribute → sort monomials → sort sum →
   fold; RED fixture (`(k+1)² = k²+2k+1` and the Gauss `target` shape),
   `poly_bad` (different expansions), `--pure` gate, unit tests. Rewrite
   Gauss's `target` step as `[by polynomial]` as the payoff.
4. **`polynomial_quantified`** — compose `peelUniversal` + `polynomial`.
5. **`std/division.bpa`** + `div`/`mod` in the arithmetic vocabulary; RED
   fixtures for a `div`/`mod` identity and a guarded-division TCC.

Each rung is RED-first (integration `.bpa` fixture + `build.zig` golden with
`has_side_effects`/`--pure`/exact stdout-stderr) per the fractal-TDD
directive, with unit tests in the touched modules.

## Verification

- `zig build test` — all existing goldens green + new gates.
- `bpa check --pure` green on every new fixture (rungs 1–2 are kernel-checked; the
  `div`/`mod` accelerated uses are disclosed if any fall outside certificate
  coverage).
- Payoff: Gauss's `target` step collapses to `[by polynomial]`; a
  `div`/`mod` identity proves in one step.
