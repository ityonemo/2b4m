# The sign bookkeeping of a withdrawn manuscript

A literate `2b4m` formalization of the sign computations in **"Algebraicity of Weil classes on
split abelian eightfolds"** (OpenAI, September 18 2026) — one of three manuscripts
[withdrawn on October 7 2026](https://github.com/openai/math/blob/main/history.md) because,
in OpenAI's words, *"a sign error invalidates a stabilization-trace cancellation argument and
the construction used by two dependent papers."*

The withdrawn text is recovered from commit `adc7f1241b` of `github.com/openai/math`, at
`preprints/Algebraicity-of-Weil-classes-on-split-abelian-eightfolds-September-18-2026/paper.pdf`.
It is absent from the current catalogue.

Run `2b4m check openai-erratum` to verify this directory.

## Why this is formalizable at all

The paper's subject sounds unreachable — the rational Hodge conjecture needs vector spaces,
sheaves, cohomology, complex manifolds, Chow groups, none of which `std` has. But the paper
is mostly **symplectic topology**, and the part that failed is narrower still. Section 6
opens:

> Throughout this section all sign exponents are read modulo two.

Every sign claim in that section is therefore a polynomial identity over the field with two
elements. That is finite, decidable, and needs none of the tower. So the strategy is to
**axiomatize the interface and formalize the arithmetic**: the geometric inputs the paper
cites become axioms, and its own sign computations become theorems.

The paper states its imports explicitly, which is what makes the line defensible:

> We use established immersion and embedding results, the ordinary family Floer theorems,
> and standard algebraic and analytic geometry with their hypotheses stated at the point of
> use.

Those are the axioms. Everything the paper claims to *prove* is a theorem here.

## What this can and cannot catch

Stated plainly, because it bounds what any conclusion below is worth.

**Can catch:** an error in the sign *arithmetic* — a dropped Koszul factor, a parity
miscount, an identity that simply is not valid over 𝔽₂.

**Cannot catch:** an error in the *inputs* to that arithmetic. If the paper miscounts how
many times two determinant lines cross, or imports a cited lemma's sign convention
backwards, then formalizing its stated crossing numbers reproduces the mistake faithfully.
The kernel checks that the conclusion follows from the premises; it has no opinion about
whether the premises match the geometry.

This is the standing risk of axiomatizing an interface, and it is sharper here than usual:
the error is *known to exist*, so a formalization that goes through has probably assumed it
away rather than vindicated the paper.

## The sign field

Signs here are genuinely elements of 𝔽₂, not naturals carrying a parity predicate — the
paper's claims are equations, and the kernel should check them as such. `parity.b4m`
axiomatizes the two-element field directly: the ring axioms, plus `exhaustion`
(`a = ZED or a = ONE`), which is the finiteness every proof below leans on.

One thing worth recording, because it shaped every proof: **`polynomial` cannot do this
work alone.** Idempotence (`a*a = a`) is not a ring identity, so a normalizer treating `+`
and `*` formally has no way to know it. Strict check rejects
`[using polynomial(parity)]` on `mul(a, a) = a` with *"sides expand differently"* — correctly.
𝔽₂-specific facts need `exhaustion`, which is why `parity.b4m` carries
`oneVariableExhaustion` as a schema: an n-variable identity costs n nested applications
rather than 2^n hand-written cases.

```2b4m
import parity <<< "parity.b4m"

sort F2 = parity.F2
const ZED = parity.ZED
const ONE = parity.ONE
func add = parity.add
func mul = parity.mul
axiom exhaustion = parity.exhaustion
axiom addZeroRight = parity.addZeroRight
axiom addSelf = parity.addSelf
axiom addIsCommutative = parity.addIsCommutative
axiom addIsAssociative = parity.addIsAssociative
axiom mulOneRight = parity.mulOneRight
axiom mulZeroRight = parity.mulZeroRight
axiom mulIsCommutative = parity.mulIsCommutative
axiom mulIsAssociative = parity.mulIsAssociative
axiom mulDistributes = parity.mulDistributes
theorem addZeroLeft = parity.addZeroLeft
theorem mulOneLeft = parity.mulOneLeft
theorem mulZeroLeft = parity.mulZeroLeft
theorem mulSelf = parity.mulSelf
theorem aRepeatedTermVanishes = parity.aRepeatedTermVanishes
axiom oneVariableExhaustion = parity.oneVariableExhaustion
```

## Lemma 6.2 — the boundary orientation sign

The paper computes the sign by which a split boundary face differs from the product
orientation. Setting

$$A = 1 + p_0 + l + P_<, \qquad R = r + P_>, \qquad C = s + P_{D'}$$

its four crossings contribute, in its own words:

> The parent node factor crosses the preceding parent slots, the child `K` crosses the
> remaining parent slots, and the child node factor crosses those same slots. Finally the
> child input block crosses the trailing parent slots. Their total permutation sign is
> $$(1 + p_z)A + (A + R) + (1 + p_z)(A + R) + CR = A + (p_z + C)R$$

That displayed equality is the first thing to check. It is a four-variable 𝔽₂ identity, so
`exhaustion` decides it — and note what is and is not being verified: the four crossing
*counts* are the paper's geometry, taken as given; only their *collapse* is proved.

`polynomial(parity)` is not enough, and the reason is worth stating: it expands both sides
as ring expressions and then reports

    'add(r, add(r, add(a, add(a, add(a, ...)))))'  vs  'add(a, ...)'

— a residue that is precisely a sum of *doubled* terms. Closing it needs `x + x = ZED`, which
is not a ring identity, so no polynomial normalizer can know it. `simplify` with a
doubled-term rewrite also stalls: it distributes but will not reassociate to bring the
doubled `(1+pz)a` terms adjacent.

So every variable is exhausted. With all four ground, each of the sixteen corners is a
single `simplify` over the constant arithmetic, and nested applications of
`oneVariableExhaustion` lift them back to the universal statement. First the corners:

```2b4m
theorem cornerAtZZZZ:
  add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(ZED, ZED))
  = add(ZED, mul(add(ZED, ZED), ZED))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(ZED, ZED))
      = add(ZED, mul(add(ZED, ZED), ZED))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtZZZO:
  add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(ONE, ZED))
  = add(ZED, mul(add(ZED, ONE), ZED))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(ONE, ZED))
      = add(ZED, mul(add(ZED, ONE), ZED))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtZZOZ:
  add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(ZED, ONE))
  = add(ZED, mul(add(ZED, ZED), ONE))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(ZED, ONE))
      = add(ZED, mul(add(ZED, ZED), ONE))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtZZOO:
  add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(ONE, ONE))
  = add(ZED, mul(add(ZED, ONE), ONE))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(ONE, ONE))
      = add(ZED, mul(add(ZED, ONE), ONE))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtZOZZ:
  add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(ZED, ZED))
  = add(ONE, mul(add(ZED, ZED), ZED))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(ZED, ZED))
      = add(ONE, mul(add(ZED, ZED), ZED))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtZOZO:
  add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(ONE, ZED))
  = add(ONE, mul(add(ZED, ONE), ZED))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(ONE, ZED))
      = add(ONE, mul(add(ZED, ONE), ZED))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtZOOZ:
  add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(ZED, ONE))
  = add(ONE, mul(add(ZED, ZED), ONE))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(ZED, ONE))
      = add(ONE, mul(add(ZED, ZED), ONE))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtZOOO:
  add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(ONE, ONE))
  = add(ONE, mul(add(ZED, ONE), ONE))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(ONE, ONE))
      = add(ONE, mul(add(ZED, ONE), ONE))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtOZZZ:
  add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(ZED, ZED))
  = add(ZED, mul(add(ONE, ZED), ZED))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(ZED, ZED))
      = add(ZED, mul(add(ONE, ZED), ZED))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtOZZO:
  add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(ONE, ZED))
  = add(ZED, mul(add(ONE, ONE), ZED))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(ONE, ZED))
      = add(ZED, mul(add(ONE, ONE), ZED))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtOZOZ:
  add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(ZED, ONE))
  = add(ZED, mul(add(ONE, ZED), ONE))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(ZED, ONE))
      = add(ZED, mul(add(ONE, ZED), ONE))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtOZOO:
  add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(ONE, ONE))
  = add(ZED, mul(add(ONE, ONE), ONE))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(ONE, ONE))
      = add(ZED, mul(add(ONE, ONE), ONE))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtOOZZ:
  add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(ZED, ZED))
  = add(ONE, mul(add(ONE, ZED), ZED))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(ZED, ZED))
      = add(ONE, mul(add(ONE, ZED), ZED))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtOOZO:
  add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(ONE, ZED))
  = add(ONE, mul(add(ONE, ONE), ZED))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(ONE, ZED))
      = add(ONE, mul(add(ONE, ONE), ZED))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtOOOZ:
  add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(ZED, ONE))
  = add(ONE, mul(add(ONE, ZED), ONE))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(ZED, ONE))
      = add(ONE, mul(add(ONE, ZED), ONE))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed

theorem cornerAtOOOO:
  add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(ONE, ONE))
  = add(ONE, mul(add(ONE, ONE), ONE))
proof
  @conclusion |
    add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(ONE, ONE))
      = add(ONE, mul(add(ONE, ONE), ONE))
    [using simplify addSelf mulZeroLeft mulZeroRight addZeroLeft addZeroRight mulOneLeft mulOneRight]
qed
```

Then the lift — exhaust `c` at each ground `(pz, a, r)`, then `r`, then `a`, then `pz`:

```2b4m
theorem allCZZZ: forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(c, ZED)) = add(ZED, mul(add(ZED, c), ZED))
proof
  @at-zed |
    add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(ZED, ZED)) = add(ZED, mul(add(ZED, ZED), ZED))
    [by cite cornerAtZZZZ]
  @at-one |
    add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(ONE, ZED)) = add(ZED, mul(add(ZED, ONE), ZED))
    [by cite cornerAtZZZO]
  @conclusion |
    forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(c, ZED)) = add(ZED, mul(add(ZED, c), ZED))
    [using instantiation oneVariableExhaustion((fun c: F2 => add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(c, ZED)) = add(ZED, mul(add(ZED, c), ZED)))) at-zed at-one]
qed

theorem allCZZO: forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(c, ONE)) = add(ZED, mul(add(ZED, c), ONE))
proof
  @at-zed |
    add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(ZED, ONE)) = add(ZED, mul(add(ZED, ZED), ONE))
    [by cite cornerAtZZOZ]
  @at-one |
    add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(ONE, ONE)) = add(ZED, mul(add(ZED, ONE), ONE))
    [by cite cornerAtZZOO]
  @conclusion |
    forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(c, ONE)) = add(ZED, mul(add(ZED, c), ONE))
    [using instantiation oneVariableExhaustion((fun c: F2 => add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(c, ONE)) = add(ZED, mul(add(ZED, c), ONE)))) at-zed at-one]
qed

theorem allCZOZ: forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(c, ZED)) = add(ONE, mul(add(ZED, c), ZED))
proof
  @at-zed |
    add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(ZED, ZED)) = add(ONE, mul(add(ZED, ZED), ZED))
    [by cite cornerAtZOZZ]
  @at-one |
    add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(ONE, ZED)) = add(ONE, mul(add(ZED, ONE), ZED))
    [by cite cornerAtZOZO]
  @conclusion |
    forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(c, ZED)) = add(ONE, mul(add(ZED, c), ZED))
    [using instantiation oneVariableExhaustion((fun c: F2 => add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(c, ZED)) = add(ONE, mul(add(ZED, c), ZED)))) at-zed at-one]
qed

theorem allCZOO: forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(c, ONE)) = add(ONE, mul(add(ZED, c), ONE))
proof
  @at-zed |
    add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(ZED, ONE)) = add(ONE, mul(add(ZED, ZED), ONE))
    [by cite cornerAtZOOZ]
  @at-one |
    add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(ONE, ONE)) = add(ONE, mul(add(ZED, ONE), ONE))
    [by cite cornerAtZOOO]
  @conclusion |
    forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(c, ONE)) = add(ONE, mul(add(ZED, c), ONE))
    [using instantiation oneVariableExhaustion((fun c: F2 => add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(c, ONE)) = add(ONE, mul(add(ZED, c), ONE)))) at-zed at-one]
qed

theorem allCOZZ: forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(c, ZED)) = add(ZED, mul(add(ONE, c), ZED))
proof
  @at-zed |
    add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(ZED, ZED)) = add(ZED, mul(add(ONE, ZED), ZED))
    [by cite cornerAtOZZZ]
  @at-one |
    add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(ONE, ZED)) = add(ZED, mul(add(ONE, ONE), ZED))
    [by cite cornerAtOZZO]
  @conclusion |
    forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(c, ZED)) = add(ZED, mul(add(ONE, c), ZED))
    [using instantiation oneVariableExhaustion((fun c: F2 => add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(c, ZED)) = add(ZED, mul(add(ONE, c), ZED)))) at-zed at-one]
qed

theorem allCOZO: forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(c, ONE)) = add(ZED, mul(add(ONE, c), ONE))
proof
  @at-zed |
    add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(ZED, ONE)) = add(ZED, mul(add(ONE, ZED), ONE))
    [by cite cornerAtOZOZ]
  @at-one |
    add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(ONE, ONE)) = add(ZED, mul(add(ONE, ONE), ONE))
    [by cite cornerAtOZOO]
  @conclusion |
    forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(c, ONE)) = add(ZED, mul(add(ONE, c), ONE))
    [using instantiation oneVariableExhaustion((fun c: F2 => add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(c, ONE)) = add(ZED, mul(add(ONE, c), ONE)))) at-zed at-one]
qed

theorem allCOOZ: forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(c, ZED)) = add(ONE, mul(add(ONE, c), ZED))
proof
  @at-zed |
    add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(ZED, ZED)) = add(ONE, mul(add(ONE, ZED), ZED))
    [by cite cornerAtOOZZ]
  @at-one |
    add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(ONE, ZED)) = add(ONE, mul(add(ONE, ONE), ZED))
    [by cite cornerAtOOZO]
  @conclusion |
    forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(c, ZED)) = add(ONE, mul(add(ONE, c), ZED))
    [using instantiation oneVariableExhaustion((fun c: F2 => add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(c, ZED)) = add(ONE, mul(add(ONE, c), ZED)))) at-zed at-one]
qed

theorem allCOOO: forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(c, ONE)) = add(ONE, mul(add(ONE, c), ONE))
proof
  @at-zed |
    add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(ZED, ONE)) = add(ONE, mul(add(ONE, ZED), ONE))
    [by cite cornerAtOOOZ]
  @at-one |
    add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(ONE, ONE)) = add(ONE, mul(add(ONE, ONE), ONE))
    [by cite cornerAtOOOO]
  @conclusion |
    forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(c, ONE)) = add(ONE, mul(add(ONE, c), ONE))
    [using instantiation oneVariableExhaustion((fun c: F2 => add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(c, ONE)) = add(ONE, mul(add(ONE, c), ONE)))) at-zed at-one]
qed

theorem allRCZZ: forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, r)), mul(add(ONE, ZED), add(ZED, r))), mul(c, r)) = add(ZED, mul(add(ZED, c), r))
proof
  @at-zed |
    forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ZED)), mul(add(ONE, ZED), add(ZED, ZED))), mul(c, ZED)) = add(ZED, mul(add(ZED, c), ZED))
    [by cite allCZZZ]
  @at-one |
    forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, ONE)), mul(add(ONE, ZED), add(ZED, ONE))), mul(c, ONE)) = add(ZED, mul(add(ZED, c), ONE))
    [by cite allCZZO]
  @conclusion |
    forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, r)), mul(add(ONE, ZED), add(ZED, r))), mul(c, r)) = add(ZED, mul(add(ZED, c), r))
    [using instantiation oneVariableExhaustion((fun r: F2 => forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, r)), mul(add(ONE, ZED), add(ZED, r))), mul(c, r)) = add(ZED, mul(add(ZED, c), r)))) at-zed at-one]
qed

theorem allRCZO: forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, r)), mul(add(ONE, ZED), add(ONE, r))), mul(c, r)) = add(ONE, mul(add(ZED, c), r))
proof
  @at-zed |
    forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ZED)), mul(add(ONE, ZED), add(ONE, ZED))), mul(c, ZED)) = add(ONE, mul(add(ZED, c), ZED))
    [by cite allCZOZ]
  @at-one |
    forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, ONE)), mul(add(ONE, ZED), add(ONE, ONE))), mul(c, ONE)) = add(ONE, mul(add(ZED, c), ONE))
    [by cite allCZOO]
  @conclusion |
    forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, r)), mul(add(ONE, ZED), add(ONE, r))), mul(c, r)) = add(ONE, mul(add(ZED, c), r))
    [using instantiation oneVariableExhaustion((fun r: F2 => forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, r)), mul(add(ONE, ZED), add(ONE, r))), mul(c, r)) = add(ONE, mul(add(ZED, c), r)))) at-zed at-one]
qed

theorem allRCOZ: forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, r)), mul(add(ONE, ONE), add(ZED, r))), mul(c, r)) = add(ZED, mul(add(ONE, c), r))
proof
  @at-zed |
    forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ZED)), mul(add(ONE, ONE), add(ZED, ZED))), mul(c, ZED)) = add(ZED, mul(add(ONE, c), ZED))
    [by cite allCOZZ]
  @at-one |
    forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, ONE)), mul(add(ONE, ONE), add(ZED, ONE))), mul(c, ONE)) = add(ZED, mul(add(ONE, c), ONE))
    [by cite allCOZO]
  @conclusion |
    forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, r)), mul(add(ONE, ONE), add(ZED, r))), mul(c, r)) = add(ZED, mul(add(ONE, c), r))
    [using instantiation oneVariableExhaustion((fun r: F2 => forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, r)), mul(add(ONE, ONE), add(ZED, r))), mul(c, r)) = add(ZED, mul(add(ONE, c), r)))) at-zed at-one]
qed

theorem allRCOO: forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, r)), mul(add(ONE, ONE), add(ONE, r))), mul(c, r)) = add(ONE, mul(add(ONE, c), r))
proof
  @at-zed |
    forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ZED)), mul(add(ONE, ONE), add(ONE, ZED))), mul(c, ZED)) = add(ONE, mul(add(ONE, c), ZED))
    [by cite allCOOZ]
  @at-one |
    forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, ONE)), mul(add(ONE, ONE), add(ONE, ONE))), mul(c, ONE)) = add(ONE, mul(add(ONE, c), ONE))
    [by cite allCOOO]
  @conclusion |
    forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, r)), mul(add(ONE, ONE), add(ONE, r))), mul(c, r)) = add(ONE, mul(add(ONE, c), r))
    [using instantiation oneVariableExhaustion((fun r: F2 => forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, r)), mul(add(ONE, ONE), add(ONE, r))), mul(c, r)) = add(ONE, mul(add(ONE, c), r)))) at-zed at-one]
qed

theorem allARCZ: forall a: F2; forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), a), add(a, r)), mul(add(ONE, ZED), add(a, r))), mul(c, r)) = add(a, mul(add(ZED, c), r))
proof
  @at-zed |
    forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), ZED), add(ZED, r)), mul(add(ONE, ZED), add(ZED, r))), mul(c, r)) = add(ZED, mul(add(ZED, c), r))
    [by cite allRCZZ]
  @at-one |
    forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), ONE), add(ONE, r)), mul(add(ONE, ZED), add(ONE, r))), mul(c, r)) = add(ONE, mul(add(ZED, c), r))
    [by cite allRCZO]
  @conclusion |
    forall a: F2; forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), a), add(a, r)), mul(add(ONE, ZED), add(a, r))), mul(c, r)) = add(a, mul(add(ZED, c), r))
    [using instantiation oneVariableExhaustion((fun a: F2 => forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), a), add(a, r)), mul(add(ONE, ZED), add(a, r))), mul(c, r)) = add(a, mul(add(ZED, c), r)))) at-zed at-one]
qed

theorem allARCO: forall a: F2; forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), a), add(a, r)), mul(add(ONE, ONE), add(a, r))), mul(c, r)) = add(a, mul(add(ONE, c), r))
proof
  @at-zed |
    forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), ZED), add(ZED, r)), mul(add(ONE, ONE), add(ZED, r))), mul(c, r)) = add(ZED, mul(add(ONE, c), r))
    [by cite allRCOZ]
  @at-one |
    forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), ONE), add(ONE, r)), mul(add(ONE, ONE), add(ONE, r))), mul(c, r)) = add(ONE, mul(add(ONE, c), r))
    [by cite allRCOO]
  @conclusion |
    forall a: F2; forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), a), add(a, r)), mul(add(ONE, ONE), add(a, r))), mul(c, r)) = add(a, mul(add(ONE, c), r))
    [using instantiation oneVariableExhaustion((fun a: F2 => forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), a), add(a, r)), mul(add(ONE, ONE), add(a, r))), mul(c, r)) = add(a, mul(add(ONE, c), r)))) at-zed at-one]
qed

theorem theCrossingSignsCollapse:
  forall pz: F2; forall a: F2; forall r: F2; forall c: F2; add(add(add(mul(add(ONE, pz), a), add(a, r)), mul(add(ONE, pz), add(a, r))), mul(c, r)) = add(a, mul(add(pz, c), r))
proof
  @at-zed |
    forall a: F2; forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ZED), a), add(a, r)), mul(add(ONE, ZED), add(a, r))), mul(c, r)) = add(a, mul(add(ZED, c), r))
    [by cite allARCZ]
  @at-one |
    forall a: F2; forall r: F2; forall c: F2; add(add(add(mul(add(ONE, ONE), a), add(a, r)), mul(add(ONE, ONE), add(a, r))), mul(c, r)) = add(a, mul(add(ONE, c), r))
    [by cite allARCO]
  @conclusion |
    forall pz: F2; forall a: F2; forall r: F2; forall c: F2; add(add(add(mul(add(ONE, pz), a), add(a, r)), mul(add(ONE, pz), add(a, r))), mul(c, r)) = add(a, mul(add(pz, c), r))
    [using instantiation oneVariableExhaustion((fun pz: F2 => forall a: F2; forall r: F2; forall c: F2; add(add(add(mul(add(ONE, pz), a), add(a, r)), mul(add(ONE, pz), add(a, r))), mul(c, r)) = add(a, mul(add(pz, c), r)))) at-zed at-one]
qed
```

**Verdict: the identity holds.** All sixteen corners check, and the collapse is valid over
𝔽₂. The error is not here.
