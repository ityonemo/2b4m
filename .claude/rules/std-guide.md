---
paths:
  - "std/**/*.b4m"
---

# Writing the standard library (`std/*.b4m`)

`std/` is reusable production infrastructure, not pedagogy. The demonstrative spellings
live in `examples/` and the `aata/*.md` transliterations; here the goal is the shortest
kernel-checked proof and a vocabulary a caller can trust. `design/conventions.md` governs layout
and labels corpus-wide; `agents/style-guide.md` covers the drift-prone parts. This file is
what is specific to `std/`.

## NO TOTALIZATION — the hard rule

**A `std` operation that invents a value where the mathematics has none is forbidden.**
Declare the guard on the DECLARATION, with `requires`, so every application owes the
obligation at the call site:

```2b4m
func div(a: Int, b: Int) => Int requires less_than(ZERO, b)
func recip(a: Field) => Field requires nonzero(a)
func sqrt(x: Real) => Real requires less_or_equal(ZERO, x)
func inverse(f: Fn) => Fn requires invertible(f)
```

**Why it is a safety property and not a style preference** (user, 2026-11-03): this software
may be used to verify software. Take pitot averages, let the sample count be zero, and a
TOTAL reciprocal divides by it — the proof discharges, the junk value propagates, and the
formal artifact flags nothing. You can crash an airplane with verified code. A guarded
operation turns "prove the count is nonzero" into an obligation where the division happens.

**The guarded-AXIOM dodge is the same violation.** A total `func recip` plus
`axiom fieldInverse: a != ZERO -> mul(a, recip(a)) = ONE` makes `recip(ZERO)` unusable in a
proof but still WRITABLE in a statement, so a term can still mean nothing. `std/field.b4m`
and `std/function.b4m` both used to state this in their own words as a defence; neither
header does now, and if you find one that still does, it is stale. **And there are no
"documented partial" exemptions** — a local alias to an unguarded operation is totalization
wearing a comment.

**What is NOT a violation.** An operation total and correct on its whole domain:
`sub` on ℤ, `prev` on ℤ/ℚ/ℝ, and `gcd` — where `gcd(0, 0) = 0` is the mainstream convention
under the order-theoretic definition (greatest in the DIVISIBILITY order), agreed by
Bourbaki/Lang/Dummit–Foote, Knuth TAOCP §4.5.2, and every CAS. The line: `sub(0,5)` and
`recip(0)` have no defensible value, so asserting one is junk; `gcd(0,0)` has one the
literature agrees on.

**Two traps, both paid for:**

- **A guard in a DISCHARGED CONCLUSION must come from the ANTECEDENT.** The conclusion is
  elaborated in the PARENT block, outside the `assume` that proves the guard, so it threads
  through every `generalize`/`discharge` restatement. Where the guard is TOTAL (a partial
  product of permutations is a permutation), derive it instead inside every `fix` and outside
  every `assume` — that placement serves the whole nesting with no antecedent.
- **A `define` whose body calls a guarded operation propagates the guard to EVERY use site.**
  `define abs(z) = sqrt(normSq(z))` re-raised `0 <= normSq(z)` at all 84 uses. If the defined
  symbol is itself TOTAL, convert it to a `func` with a defining axiom so the obligation is
  met ONCE.

When a guarded operation cannot satisfy an existing interface, **restate the thing as a
RELATION** — do not totalize the function. `std/integer/family-gcd.b4m`'s `isFamilyGcd` is
built that way precisely because a gcd fold would need a total `gcd`.

## How names are picked

**The rule.** In `std/<theory>/*` or `std/<theory>.b4m`, THAT theory owns the unmodified
const and operator names. A visiting theory takes a **full-word prefix** — never a bare
letter:

```2b4m
// in std/integer/embedding.b4m — ℤ is the theory, ℕ is visiting
const ZERO      = integer.ZERO        func add     = integer.add
const NAT_ZERO  = peano.ZERO          func nat_add = peano.add
```

Spell the prefix `nat_`/`NAT_`, `int_`/`INT_`, `real_`/`REAL_`, `complex_`/`COMPLEX_`, and for
ℤ_n the file's own `zn_`/`ZN_`. The corpus drifted into `NZERO`, `nadd`, `imul`, `rless_than`
and more — about 4770 uses, cleared over eight commits ending `1009499`, plus ~1300 more in
the words that sweep missed (`IONE`, `isub`, `ineg`, `iprev`, `RONE`, `rneg`, `rrecip`,
`CONE`, `crecip`, `NONE`, `NTWO`, `ITWO`, `nsub`, `zadd`, `zneg`) — because a one-letter
prefix also breaks the full-word naming rule.

**In `aata/`, follow the names the book uses.** Judson writes ℤ_n, so the ℤ_n visitor prefix
there is `zn_`/`ZN_` (matching the `ZN_ZERO` already in `4.1-cyclic-subgroups-exercises.md`),
not the import's module name. A prefix taken from the surrounding file's own convention beats
one derived from a path.

**Two exceptions, both discovered by auditing rather than assumed:**

- **A file about a DERIVED structure lets that structure own the bare names.** The mod-n
  family lives in `std/integer/` but is about ℤ_n, so `mod_n.ZERO` is bare and ℤ takes
  `INT_ZERO`.
- **A POLYNOMIAL file is a root concept parameterized over its coefficients.**
  `std/ring/polynomial.b4m` is the definition; `integer/polynomial.b4m`,
  `field/polynomial.b4m`, `rational/polynomial.b4m` are instances. The directory records
  WHICH COEFFICIENTS, not the subject, so the bare names go to the degree/index arithmetic —
  the ring's own zero is the zero POLYNOMIAL (`IZEROP`), and the coefficient zero is
  `INT_ZERO`.

**Never prefix a name nothing competes for.** `nat_less_than` in a permutation file guards
against a `less_than` that does not exist (permutations have no order) and reads as a
collision where there is none. Check first: if no local declaration claims the bare name,
take it.

**A file whose aliases disagree about their own subject is the real smell** — ℂ owning bare
`ZERO` and `mul` while its own addition is `cadd` was a genuine inconsistency in
`std/complex/polar.b4m`, not a convention.

**Renaming mechanics that bite:**

- **A rename must never touch a QUALIFIED name.** `integer.succ` is the SOURCE theory's name
  and is not yours to respell — rewriting alias right-hand sides broke three files mid-pass.
  Same class as a model block's LEFT-HAND keys, where a regex sweep once rewrote
  `sequence.ZERO` → `sequence.NAT_ZERO` and broke the block. A qualified name moves ONLY when
  its source is in the same rename set.
- **Order matters.** Vacate the outgoing bare names BEFORE the incoming ones arrive, or they
  collide mid-rename.
- **A comment that quotes a name being renamed cannot survive the rename.** One said "the
  spelling is the style guide's, not `NZERO`" and the sweep inverted its meaning.
- Keep theorem counts IDENTICAL across a naming commit — that is the signal it carried no
  mathematics. `check std --library` and `check aata` both report them.

## Aliasing, not re-declaring

**ALIAS what exists; declare bare only what is NEW.** 47 files declare a bare `sort X`
(61 declarations as of 2026-11-05). Most are legitimate — a root theory with nothing above it
(`peano`, `set`, `integer`, `real`, `group`, `function`, `field`, `ring`), a schema's opaque
parameter (`G`, `H`, `Value`), or a genuinely new sort (the `Seq`/`Poly`/`Quot` families).
What is NOT legitimate is re-declaring a sort another theory already owns:
`std/subgroup.b4m` used to declare its own abstract parent group and re-prove seven group
theorems verbatim, and aliasing `group.Grp` instead removed 255 lines.

**Verify a dependency cycle before claiming one.** The subgroup/group "inversion" was
defended as cycle-avoidance; the cycle did not exist.

A FACT re-export is always `fact T = X.t`, whatever the target's kind — `axiom T = X.t` and
`theorem T = X.t` are hard errors. And an UNCITED `fact` alias is never resolved, so it
proves nothing; if the point is to verify something, write a theorem with a one-line import
proof.

## File boundaries

Split or merge by **CATEGORY and honest import names**, never by dependency weight — lazy
imports make over-importing free, so eval cost is not the criterion. Each file is one clean
concept.

The counter-example worth knowing: divisibility, the division algorithm, and gcd/Bézout were
initially three files per number system, then merged into ONE number-theory unit each
(`std/peano/divides.b4m`, `std/integer/divides.b4m`) by user re-decision. The module alias is
`peano_divides` / `int_divides`; **bare `divides` is ALWAYS the divisibility PREDICATE**,
never the module.

## Proof style

**Shortest kernel-checked proof.** Collapse hand rewrite/elimination ladders with accelerated
tactics wherever they verify AND kernel-check — `simplify` for recursion-unfold ladders,
`arithmetic` for linear ℕ/ℤ facts, `polynomial` for nonlinear identities. Zero trust cost
when the certificate is emitted. (`aata/` has the opposite rule: do not accelerate a step
Judson spells out.)

**`--library` means every axiom must be exercised.** `check std --library` fails on an axiom
declared under `std/` that no theorem there rests on, which is why 14 theories carry a
`<namespace>/examples.b4m` whose only job is to use their own axioms. If you add an axiom,
add the example that uses it.

**One hole anywhere under `std/` poisons the whole gate** — it forces the sweep into
`--draft` and blinds it to every other file. Keep hole-bearing scaffolds in `drafts/` and
move them in once filled.

## Before writing a new theorem: look for it

**At 2377 theorems across 151 files, nobody holds the inventory.** 90 lines of a
`powerSequenceExists` were written before discovering `std/group/counting.b4m`'s
`powersAreListed` was exactly that theorem, already proved — a grep on the chosen name found
nothing because the existing one is named differently.

**Search by the distinctive TERM, not a guessed name** (`exists v: Seq; … at(v, i) = power(…)`),
and use the `2b4m-query` tooling rather than grep for anything shape-related.
