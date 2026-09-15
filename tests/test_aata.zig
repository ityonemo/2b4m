//! Integration gates — the AATA literate transliterations (aata/*.md).
//!
//! Each gate spawns the built `bpa` binary and asserts its stdout / stderr /
//! exit code; wired into the `test` step via `test_step.dependOn`.

const std = @import("std");
const Ctx = @import("Ctx.zig");

pub fn addTests(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    test_step: *std.Build.Step,
) void {
    const ctx = Ctx.init(b, exe, test_step);

    // AATA §3.1 Integers mod n: the ℤ_n arithmetic proposition (all six parts)
    // modeled as ℤ-congruence n | (a−b) over the plain Int sort.
    ctx.okSilent(&.{ "check", "aata/3.1-integers-mod-n.md" });
    // §3.1 exercises: the ℤ_n structural laws (Ex 19–24 — additive/multiplicative
    // identity, inverses, well-definedness, associativity, distributivity) proved
    // as ℤ-congruences; Ex 22's well-definedness carries the ab−a'b' split. std used
    // liberally.
    ctx.okSilent(&.{ "check", "aata/3.1-integers-mod-n-exercises.md" });

    // AATA group theory: the literate translation of Groups basic-properties (5
    // propositions) + 5 in-scope exercises. The 10 theorems now ALIAS the library
    // proofs in std/group.bpa (the .md is book-notation presentation; the checked
    // derivations live in std) — verified (proven; no accelerated tactic).
    ctx.okSilent(&.{ "check", "aata/3.2-groups.md" });
    // §3.2 exercises: migrated out of the main text. Proves Ex 25 (conjugation
    // power a·bⁿ·a⁻¹ = (aba⁻¹)ⁿ over a ℤ exponent) and Ex 33 ((ab)²=a²b² ⟹
    // abelian); forwards cancellation / exponent laws / xa=b to §3.2; defers the
    // concrete-structure exercises (ℤ_n, matrices, reals, counting).
    ctx.okSilent(&.{ "check", "aata/3.2-groups-exercises.md" });

    // AATA §3.3 Subgroups: the literate transliteration of the subgroup definition,
    // the one-step subgroup test (both directions), and the intersection-of-
    // subgroups exercise. Aliases std/subgroup.bpa to the book's H ≤ G notation;
    // concrete example subgroups (ℚ*, SL₂, ℤ₄, ℤ₂×ℤ₂) are summarized, not formalized
    // (Tier-3 carriers). Proven; no accelerated tactic.
    ctx.okSilent(&.{ "check", "aata/3.3-subgroups.md" });
    // §3.3 exercises: the abstract subgroup-criterion ones proved by the
    // three-closure pattern — Ex 48 (center Z(G)), 53 (centralizer C(H)), 54
    // (conjugate gHg⁻¹), plus Ex 49 and Ex 51 (equational abelian-ness). Ex 45
    // (H∩K) forwarded to the main text; concrete-group ones (S₃, D₄, Q₈, …)
    // deferred. std used liberally.
    ctx.okSilent(&.{ "check", "aata/3.3-subgroups-exercises.md" });

    // AATA Chapter 4 (Cyclic Groups). §4.1 "Cyclic Subgroups": the five main-text
    // theorems transcribed following Judson — ⟨a⟩ is the smallest subgroup, cyclic ⇒
    // abelian, every subgroup of a cyclic group is cyclic (division algorithm +
    // well-ordering, with the elided memberPowerInH induction spelled out), a^k=e ⟺ n|k,
    // and ord(a^k)=n/gcd(k,n). Exercises: Ex 23(a) proved via hasOrder; rest forward/defer/skip.
    ctx.okSilent(&.{ "check", "aata/4.1-cyclic-subgroups.md" });
    ctx.okSilent(&.{ "check", "aata/4.1-cyclic-subgroups-exercises.md" });
    // §4.2 "The Multiplicative Group of ℂ": ℂ arithmetic + the modulus identities
    // (real proofs via std/complex-modulus.bpa); polar/DeMoivre/roots-of-unity deferred
    // as prose on the trigonometry gap. Exercises: Ex 19 a/b/f proved; rest skip/defer.
    ctx.okSilent(&.{ "check", "aata/4.2-complex-multiplicative-group.md" });
    ctx.okSilent(&.{ "check", "aata/4.2-complex-multiplicative-group-exercises.md" });
    // §4.3 "The Method of Repeated Squares": prose-only (an algorithm, not a theorem;
    // needs a concrete ℤ_n + binary representation). Exercises: brute numeric, skipped.
    ctx.okSilent(&.{ "check", "aata/4.3-repeated-squares.md" });
    ctx.okSilent(&.{ "check", "aata/4.3-repeated-squares-exercises.md" });

    // AATA set theory: the literate transliteration of Chapter 1 §1.2.1
    // (the set-algebra proposition + De Morgan's laws proved by hand; the §1.2
    // exercises discharged in one line each by the `ext` tactic).
    ctx.okSilent(&.{ "check", "aata/1.2.1-sets.md" });
    // §1.2.1 exercises migrated out: the five set-identity element-chases
    // (symmetric difference &c.), each one line of `extensionality_quantified`.
    ctx.okSilent(&.{ "check", "aata/1.2.1-sets-exercises.md" });

    // AATA functions: the literate transliteration of Chapter 1 §1.2.2
    // (composition associativity/preservation + invertible⟺bijective, BOTH
    // directions). The backward direction (bijective ⇒ invertible) constructs the
    // inverse by definite description (the `functionFromGraph` axiom-schema — the
    // total+unique preimage graph realized as a function). Verified; the one
    // theorem resting on that disclosed axiom.
    ctx.okSilent(&.{ "check", "aata/1.2.2-functions.md" });
    // §1.2.2 exercises migrated out: Ex 25 ((g∘f)⁻¹ = f⁻¹∘g⁻¹) via inverse
    // uniqueness; re-proves composeAssoc locally (not in std) so citations resolve.
    ctx.okSilent(&.{ "check", "aata/1.2.2-functions-exercises.md" });

    // AATA relations: the FOL-tractable part of Chapter 1 §1.2.3 — the three
    // equivalence-projections + the "reflexivity is redundant" exercise. The
    // equivalence⇔partition correspondence is deferred (needs sets-of-sets).
    ctx.okSilent(&.{ "check", "aata/1.2.3-relations.md" });
    // §1.2.3 relations exercises migrated out: Ex 24 (reflexivity is redundant
    // under symmetry + transitivity + seriality).
    ctx.okSilent(&.{ "check", "aata/1.2.3-relations-exercises.md" });

    // AATA equivalence classes/partitions (§1.2.3): classes are nonempty, [x]=[y]
    // iff x~y, any two are equal-or-disjoint, AND the classes FORM A PARTITION —
    // covers the universe (⋃[x] = universe) and are pairwise-disjoint, discharging
    // isPartition. The partition packaging (a set of sets) is now stateable via
    // std/collection.bpa (a Collection = a set of Sets, modeling std/set.bpa one
    // level up). Fully proven, no holes.
    ctx.okSilent(&.{ "check", "aata/1.2.3-partitions.md" });

    // AATA Chapter 2 "The Integers", §2.1 Mathematical Induction, fully proven —
    // the base case AND the ∀n≥0 3|(4ⁿ−1) nonneg-induction (its inductive step
    // splits 4^(k+1)−1 = 4(4ᵏ−1)+3 and uses dividesMul/dividesAdd), plus the
    // Second Principle (strong induction) and the Principle of Well-Ordering,
    // both aliased from std/integer-wellordering.bpa (proved there from ordinary
    // induction). No hole; the file checks WITHOUT --draft.
    ctx.okSilent(&.{ "check", "aata/2.1-induction.md" });
    // §2.1 exercises: Judson's Ch2 induction exercises segregated out. Ex 5
    // (3 | 10ⁿ⁺¹+10ⁿ+1) and Ex 9 (geometric sum 1+2+…+2ⁿ = 2ⁿ⁺¹−1) proved by
    // nonneg-induction; the rest forwarded (induction-principle equivalence) or
    // deferred (Σ / factorial / reals / cardinality). std used liberally.
    ctx.okSilent(&.{ "check", "aata/2.1-induction-exercises.md" });
    // §2.2 The Division Algorithm: Ch1-style — the proofs now live in
    // std/integer-divides.bpa; this file aliases them and narrates. Existence
    // over all of ℤ + uniqueness.
    ctx.okSilent(&.{ "check", "aata/2.2-division-algorithm.md" });
    // §2.2 exercises: Ex 16/18 (Bézout ⟹ coprime, all three coprimality claims),
    // Ex 22 (unique residue mod n via the division algorithm), Ex 23 (lcm exists
    // & unique, from std/integer-divides's lcm). Deferred: gcd·lcm product (24,25),
    // product-of-coprimes (26). std used liberally.
    ctx.okSilent(&.{ "check", "aata/2.2-division-algorithm-exercises.md" });
    // §2.3 Primes: stub for the GCD/Bézout/Euclid/FTA material to come; imports
    // the division library and aliases the two headline theorems.
    ctx.okSilent(&.{ "check", "aata/2.3-primes.md" });
    // §2.3 exercises: Ex 20 (every perfect square is 4k or 4k+1, via the division
    // algorithm at divisor 2 + the odd-square identity). Ex 27 forwarded (Euclid's
    // Lemma, in the main text / std/primes). Deferred: Fibonacci, FTA perfect
    // squares, Mersenne, Dirichlet forms, √2 (see examples/sqrt2.bpa). std used
    // liberally.
    ctx.okSilent(&.{ "check", "aata/2.3-primes-exercises.md" });
}
