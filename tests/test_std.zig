//! Integration gates — the standard library files (std/peano* , group, set, function) — the pinned declaration/theorem counts.
//!
//! Each gate spawns the built `2b4m` binary and asserts its stdout / stderr /
//! exit code; wired into the `test` step via `test_step.dependOn`.

const std = @import("std");
const Ctx = @import("Ctx.zig");

pub fn addTests(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    test_step: *std.Build.Step,
) void {
    const ctx = Ctx.init(b, exe, test_step);

    // the standard library must check
    ctx.okSilent(&.{ "check", "std/peano.b4m" });

    // the order theory + strong induction + well-ordering, split into its own
    // layer; proven, and --recursive re-verifies the imported peano proofs too
    ctx.okSilent(&.{ "check", "std/peano/order.b4m" });

    ctx.okSilent(&.{ "check", "std/peano/order.b4m" });

    // truncated subtraction + the gcd measure lemma (Euclid foundation)
    ctx.okSilent(&.{ "check", "std/peano/subtraction.b4m" });

    // divisibility, the guarded Euclidean div/mod, and THE PAYOFF: Euclid's
    // algorithm proved correct (common divisor + greatest), by strong
    // induction on the decreasing modulus — the whole ℕ number-theory unit
    ctx.okSilent(&.{ "check", "std/peano/divides.b4m" });

    // parity: even/odd + the crux 2|p² → 2|p, proven (no accelerated tactic)
    ctx.okSilent(&.{ "check", "std/peano/parity.b4m" });

    // factorial: n! by its two recursion clauses (as axioms — a bare constant on a
    // definition-block clause's right-hand side reads as a clause variable), never zero
    ctx.okSilent(&.{ "check", "std/peano/factorial.b4m" });

    // power: b^e on ℕ by its two recursion clauses (axioms, as factorial); b^1 = b
    ctx.okSilent(&.{ "check", "std/peano/power.b4m" });

    // the ℤ base std/integer.b4m now bundles the ring algebra (left/right
    // recursion, commutativity, associativity, n+(-n)=0, mul lemmas), the nonneg
    // subclass + its transferred Peano induction, DERIVED bidirectional induction,
    // and the IntegerRing model — the former integer-ring / integer-nonneg /
    // integer-ring-model files collapsed into it. Checked below with the base.

    // ℤ subtraction (total: a-b = a+(-b)) + the strict/non-strict order, over
    // the ring algebra. The order's gap witness is pinned NONNEGATIVE (an
    // unconstrained ℤ gap would make less_than the total relation — the naive
    // Peano port was a latent bug); irreflexivity rests on nonnegSuccNotZero (ℤ's
    // distinctness axiom, on the nonneg subclass). Full order corpus proven:
    // irreflexivity/transitivity/trichotomy (bidirectional induction on the
    // difference), addition preserves/cancels order, less_or_equal refl/trans/
    // split/antisymmetric. subSelf/subAddCancel from the inverse law, no induction.
    ctx.okSilent(&.{ "check", "std/integer/order.b4m" });

    // strong induction + the Principle of Well-Ordering over the NONNEGATIVE
    // integers (std/integer/wellordering.b4m), layered above the ℤ order (it can't
    // live in integer-nonneg, which sits below the order in the import DAG).
    // nonnegStrongInduction (course-of-values) and nonnegWellOrdering (every
    // nonempty nonneg subset has a least element) — nonneg-guarded ports of the
    // peano-order proofs; the Division Algorithm's existence half runs on these.
    ctx.okSilent(&.{ "check", "std/integer/wellordering.b4m" });

    // abstract divisibility (std/divisibility.b4m): a carrier with mul/add/ONE
    // and the divides predicate; dividesRefl/dividesMul/dividesAdd proved once,
    // over the abstract carrier. ℕ and ℤ `model` this to inherit them.
    ctx.okSilent(&.{ "check", "std/divisibility.b4m" });

    // the whole ℤ number-theory unit (std/integer/divides.b4m): divisibility
    // (`divides` intro/elim, the refl/mul/add facts TRANSFERRED from the abstract
    // theory via `model IntegerDivisibility`) + powers; the Division Algorithm
    // (existence over all of ℤ via well-ordering on {a−bk≥0} + uniqueness, with the
    // product-of-nonnegatives / bounded-multiple-is-zero / remainder-difference
    // machinery); and the GCD / Bézout theory (the existence-form gcd `bezout` and
    // its coprime specialization `coprimeBezout`, the engine of Euclid's Lemma). An
    // independent std development of the theory AATA §2.2/§2.3 prove inline.
    ctx.okSilent(&.{ "check", "std/integer/divides.b4m" });
    // the DIVISOR LATTICE (std/integer/lattice.b4m): gcd and lcm as the meet and join —
    // gcd(lcm(m, n), N) = lcm(gcd(m, N), gcd(n, N)), the distributivity AATA §4.1 Ex 28's
    // finite-order half needs. Proved from the gcd/lcm universal properties and Bézout,
    // with no prime factorization.
    ctx.okSilent(&.{ "check", "std/integer/lattice.b4m" });

    // the abstract, ℕ-indexed sequence + FOLD theory (std/sequence.b4m): an opaque
    // `Seq` over an abstract `Value` with an `at` accessor, an abstract `combine`/
    // `IDENTITY` fold (`foldUpTo`) + recursion axioms, and fold-structure theorems.
    // This is the STRUCTURE that std/integer-sequence.b4m models (Value:Int,
    // combine:mul, IDENTITY:ONE, foldUpTo:productUpTo) to recover the finite product.
    ctx.okSilent(&.{ "check", "std/sequence.b4m" });

    // finite integer sequences + products (std/integer-sequence.b4m): a `Seq` sort
    // with an `at(s,i)` accessor and a recursive `productUpTo(s,k)` over the nonneg-ℤ
    // index sort, obtained by MODELING the abstract fold above (2b4m has no lists/
    // finite products, so the indexed family is reified as a sort). everyEntryDivides-
    // Product — each entry below the bound divides the product — is the lemma the
    // infinitude/FTA arguments need. Plus the reification-existence axioms
    // (seqSingletonExists/seqConcatExists/seqRemoveExists) that let FTA
    // witness/splice/cancel factorization sequences.
    ctx.okSilent(&.{ "check", "std/integer/sequence.b4m" });
    ctx.okSilent(&.{ "check", "std/integer/product.b4m" });

    // WORKED EXAMPLES (`std/<theory>/examples.b4m`): a theory's axioms are demonstrated by the
    // library itself, not left for callers to be the first to exercise. `--library` over
    // std/ is what makes this an obligation rather than a nicety — an axiom no derivation
    // touches has never had its binders, guards or direction checked.
    ctx.okSilent(&.{ "check", "std/sequence/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/integer/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/real/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/rational/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/collection/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/equivalence/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/function/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/complex/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/ring/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/field/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/peano/examples.b4m" });

    // the reusable ℤ PRIME THEORY (std/primes.b4m): primality packaged once as a
    // transparent `define is_prime`, then Euclid's Lemma (via coprimeBezout),
    // primeDividesProductImpliesMember (FTA-uniqueness crux), and the infinitude
    // of primes — an independent std development of the facts that aata/2.3-primes.md
    // proves inline. Layers over std/integer/divides.b4m + std/integer-sequence.b4m.
    ctx.okSilent(&.{ "check", "std/primes.b4m" });
    // PRIMES IN A RESIDUE CLASS (std/primes/classes.b4m): the Dirichlet-type constructions
    // Euclid's argument still reaches — infinitely many primes ≡ 5 (mod 6) and ≡ 3 (mod 4),
    // by strong induction ("a number ≡ 5 mod 6 above 1 has a prime factor ≡ 5 mod 6"), plus
    // the Mersenne divisibility (2^a − 1) | (2^ab − 1).
    ctx.okSilent(&.{ "check", "std/primes/classes.b4m" });

    // the group theory (std/group.b4m): THREE axioms (associativity + LEFT identity
    // + LEFT inverse) + an opt-in `opCommutative`; the right-sided laws and the
    // basic-property theorems (identityUnique, inverseUnique, invProduct, cancelLeft,
    // …) are proved from those axioms alone. aata/3.2-groups.md aliases these.
    ctx.okSilent(&.{ "check", "std/group.b4m" });

    // group powers (std/group/power.b4m): g^n over a Nat exponent, layered over
    // std/group.b4m + std/peano.b4m (keeping the core group theory import-free).
    // Defines pow(g,n) recursively and proves the exponent-addition law
    // powAdd: pow(g, m+n) = op(pow(g,m), pow(g,n)) by induction on n.
    ctx.okSilent(&.{ "check", "std/group/power.b4m" });

    // finite group products (std/group/sequence.b4m): models std/sequence.b4m's
    // fold with op/E to get productUpTo(s, n) = g0·…·g_{n-1}, and proves the n-ary
    // inverse law invOfProduct: inv(g0·…·g_{n-1}) = g_{n-1}⁻¹·…·g0⁻¹ (Judson §3.2
    // Ex 27) by induction, step = binary invProduct. Never cites opCommutative.
    ctx.okSilent(&.{ "check", "std/group/sequence.b4m" });
    // ...and its five sequence-BUILDING postulates, each unpacked once (an existential whose
    // witness is never unpacked is one whose shape has never been checked). These also carry
    // the GroupSeq model's obligations for std/sequence.b4m's same-named axioms.
    ctx.okSilent(&.{ "check", "std/group/sequence-examples.b4m" });

    // finite integer sums (std/integer-sum.b4m): the SECOND fold over sequence.b4m
    // (combine:add, IDENTITY:ZERO) → sumUpTo(s, n) = Σ_{i<n} at(s,i). Identity-style
    // sequences (at(i)=i, i², i³, (3i+1)X) + nonneg-induction prove §2.1 Ex 1/2/4 and
    // the Gauss sum in DIVISION-FREE form (6·Σi²=(n-1)n(2n-1), 4·Σi³=(n(n-1))², etc.)
    // — ℚ not needed, only the fractional notation would be; ring steps by polynomial.
    ctx.okSilent(&.{ "check", "std/integer/sum.b4m" });
    // ONE sequence carries BOTH folds: the sort is shared, so a single `s` has a
    // product and a sum. Two sorts would make this file ill-typed.
    ctx.okSilent(&.{ "check", "tests/cases/integer_seq_both_folds.b4m" });

    // subgroups (std/subgroup.b4m, Judson §3.3): a STANDALONE theory (declares its own
    // parent group) — the subgroup criteria, the one-step test (both directions), the
    // intersection, and the five group axioms proven on the subgroup (what a group-
    // model @-projects). Authored to plug into std/group.b4m via a model stack.
    ctx.okSilent(&.{ "check", "std/subgroup.b4m" });
    // COSETS (std/group/coset.b4m): the left coset gH as a two-place MEMBERSHIP predicate (the
    // device std/group/generated.b4m uses for a variable generator), so the chapter stays
    // first-order with no sets of group elements. Judson §6.1: the membership criterion
    // (x ∈ gH iff g⁻¹x ∈ H), Lemma 6.1 (gH = kH iff g⁻¹k ∈ H), Theorem 6.2 (the cosets are
    // equal-or-disjoint and cover the group), and Proposition 6.4's translation bijection
    // h ↦ gh — the engine of Lagrange, since it makes every coset the size of the subgroup.
    ctx.okSilent(&.{ "check", "std/group/coset.b4m" });
    // LAGRANGE (std/group/lagrange.b4m, Judson §6.2): |G| = [G:H]·|H| as LISTINGS — k coset
    // representatives and a p-long listing of H give a (k·p)-long listing of G. The block
    // decomposition: each block is a translate of H's listing (Prop 6.4), the blocks are
    // pairwise disjoint (Thm 6.2) so the concatenation is injective across every seam, and
    // they cover G. Induction on the representative count, one `seqConcat` per step.
    // THE ABSTRACT INDEXED CONTAINER (std/indexed.b4m): the list-BUILDING pattern every finite
    // list sort in std was re-declaring, named once — singleton/prepend/concat/reverse/remove
    // over an abstract `Indexed`/`Item`, with NO fold, which is what lets a carrier whose items
    // have no monoid structure (Points) model it. examples.b4m exercises every axiom AND
    // instantiates `mappedListExists`, which is where that schema's proof is actually checked
    // (`check std/indexed.b4m` alone reports zero theorems — a schema body is only verified at
    // an instantiation).
    ctx.okSilent(&.{ "check", "std/indexed.b4m" });
    ctx.okSilent(&.{ "check", "std/indexed/examples.b4m" });
    ctx.okSilent(&.{ "check", "std/group/lagrange.b4m" });
    // AN ELEMENT'S ORDER DIVIDES |G| (std/group/order-divides.b4m, Judson's Corollary 6.7).
    // ⟨gen⟩ is listed by its order (the powers g⁰…g^(n−1) — distinct by minimality, exhaustive
    // by reducing the exponent mod n), it satisfies the three subgroup criteria, so a model
    // carries the whole coset/Lagrange corpus onto it and the divisibility corollary applies.
    ctx.okSilent(&.{ "check", "std/group/order-divides.b4m" });

    // cyclic subgroups (std/cyclic.b4m, Judson §4.1): ⟨a⟩ = {a^k} as a membership
    // predicate over a fixed generator const, proved a subgroup (identity/closure) and
    // the smallest one containing a (integer induction), plus cyclic ⇒ abelian.
    ctx.okSilent(&.{ "check", "std/cyclic.b4m" });

    // order of a group element (std/group/order.b4m, Judson §4.1): the fixed-A/N form
    // proves a^k = e ⟺ n|k and ord(a^k) = n/gcd(k,n) (via euclidFromBezout); the
    // hasOrder(g,n) RELATION generalizes order over arbitrary elements (orderIsUnique,
    // inverseHasSameOrder = |a|=|a⁻¹|).
    ctx.okSilent(&.{ "check", "std/group/order.b4m" });
    // the cyclic subgroup ⟨g⟩ of a VARIABLE generator (std/group/generated.b4m, Judson §4.1
    // exercises 27, 30, 37): inGenerated(g, x) as a two-place relation, its closure laws,
    // the trivial intersection of coprime-order cyclic subgroups (Bézout), and "no proper
    // nontrivial (cyclic) subgroups ⟹ cyclic".
    ctx.okSilent(&.{ "check", "std/group/generated.b4m" });
    // two distinct order-2 elements of an ABELIAN group span a subgroup of order 4
    // (std/group/klein.b4m, Judson §4.1 exercise 33): {e, a, b, ab} is closed under the
    // operation and inverses (every member is its own inverse) and has four distinct members.
    ctx.okSilent(&.{ "check", "std/group/klein.b4m" });
    // orders against SIZES (std/group/counting.b4m, Judson §4.1 exercise 34): pigeonhole for
    // listings (distinct entries drawn from a listing of length n number at most n), the
    // powers g⁰..g^(n−1) of an element of order n are distinct, so in a group of n elements
    // such an element generates. Bridges ℕ-indexed listings to ℤ-valued orders via toInt.
    ctx.okSilent(&.{ "check", "std/group/counting.b4m" });

    // the integers mod n (std/integer/mod-n.b4m, Judson §4.1 concrete): ℤ_n as a
    // quotient sort ℤ/nℤ whose group/ring axioms LIFT from ℤ via cls-homomorphism,
    // with ZnGroup/ZnGroupPower/ZnRing models (⟨1⟩ cyclic) and the units U(n) as a
    // group (UnitsGroup). An abstract TEMPLATE modeled at a concrete n.
    ctx.okSilent(&.{ "check", "std/integer/mod-n.b4m" });

    // ℤ_n COUNTED (std/integer/mod-n-listing.b4m): the n classes as a listing (a ℕ → ℤ
    // embedding, the quotient identification with the bounded-remainder lemma for
    // distinctness, the division algorithm for coverage), and Judson §4.1 Ex 29 — an even
    // number of generators for n > 2 — by MODEL TRANSFER of std/group/listing.b4m's
    // theorem for all finite groups through one overlay over group, group_power and
    // group_sequence (ZnListing).
    // the embedding ℕ → ℤ (std/integer/embedding.b4m): toInt by two recursion clauses;
    // additive, order-preserving/-reflecting, injective, onto the nonnegatives. What lets
    // ℕ-indexed listings talk about ℤ-valued orders and exponents.
    ctx.okSilent(&.{ "check", "std/integer/embedding.b4m" });
    ctx.okSilent(&.{ "check", "std/integer/mod-n-listing.b4m" });
    // the DIRECT PRODUCT of two groups (std/group/product.b4m): the pair sort with
    // componentwise operation, as a model of std/group.b4m so its theorems transfer; and
    // (std/integer/mod-n-product.b4m) ℤ_n × ℤ_n as one instance of it.
    ctx.okSilent(&.{ "check", "std/group/product.b4m" });
    ctx.okSilent(&.{ "check", "std/integer/mod-n-product.b4m" });
    // ℤ_p has no proper nontrivial subgroups (std/integer/mod-n-prime.b4m, Judson §4.1
    // exercise 26): a subgroup (a predicate closed under 0, +, −) is closed under integer
    // multiples; a nonzero member cls(a) has N ∤ a, so for PRIME N Bézout puts cls(1) in it.
    // The schema is exhibited at an opaque subgroup predicate.
    ctx.okSilent(&.{ "check", "std/integer/mod-n-prime.b4m" });
    // the generators of ℤ_N (std/integer/mod-n-generators.b4m, Judson §4.1 corollary +
    // exercise 24): cls(r) generates iff r is Bézout-coprime to N; for N = pq (distinct primes)
    // the non-generators are the multiples of p or q, listed explicitly as q + (p − 1) classes,
    // so the generators number (p − 1)(q − 1) — by pigeonhole on listings.
    ctx.okSilent(&.{ "check", "std/integer/mod-n-generators.b4m" });

    // the ring theory (std/ring.b4m): an additive abelian group + associative,
    // distributing multiplication. Its additive half MODELS std/group.b4m (a
    // TWO-LEVEL structure — a model inside a modelable theory). Judson's first
    // ring proposition (a·0=0·a=0; a(-b)=(-a)b=-(ab); (-a)(-b)=ab) is proved by
    // TRANSFERRING the additive-group cancelRight/inverseUnique/invInvolution
    // through the AdditiveGroup model rather than re-deriving them. Left-axiomatic:
    // only addZeroLeft/addNegLeft are axioms; the RIGHT laws (addZeroRight,
    // addNegRight) are the two derived theorems the model no longer needs to map.
    // (the synthetic materialized theorems are suppressed.)
    ctx.okSilent(&.{ "check", "std/ring.b4m" });

    // the field theory (std/field.b4m): a commutative ring with unit + a partial
    // multiplicative inverse `recip` (total func, guarded axiom x≠0 → x·recip x = 1).
    // MODELS std/ring.b4m to inherit the ring corpus; derives mulOneRight,
    // recipMulLeft, and noZeroDivisors (a·b=0 → a=0 or b=0). Base of the ℚ/ℝ/ℂ tower.
    ctx.okSilent(&.{ "check", "std/field.b4m" });

    // the ordered-field theory (std/field/order.b4m): a field + a total strict order
    // `less_than` compatible with the ops (translation-invariant add, positive
    // product). MODELS std/field.b4m; postulates the order abstractly (opaque pred +
    // axioms, unlike the constructed ℤ order) and derives asymmetry etc. ℚ/ℝ model it.
    ctx.okSilent(&.{ "check", "std/field/order.b4m" });
    // the multiplicative group F* of an ordered field (std/field/units.b4m): the nonzero cut
    // as a GUARDED model of std/group.b4m, natural powers, and "the elements of finite order
    // are ±1" (Judson §4.1 exercise 10 for ℚ* and ℝ*) proved once over the ordered field.
    ctx.okSilent(&.{ "check", "std/field/units.b4m" });

    // the rationals ℚ (std/rational.b4m): the prime ordered field. MODELS
    // std/field/order.b4m (RationalOrderedField, the algebra lens) + a ring embedding
    // ℤ↪ℚ (fromInt: homomorphism + injective) linking integer arithmetic to ℚ.
    // Derives fromIntNonzero (nonzero ints embed to invertible rationals). First
    // concrete sort of the tower; independent, containment-by-embedding.
    ctx.okSilent(&.{ "check", "std/rational.b4m" });
    // ℚ* (std/rational/units.b4m): models field_order + field_units onto ℚ in one block;
    // ℚ* as a guarded group model; finite order ⟺ ±1 by transfer.
    ctx.okSilent(&.{ "check", "std/rational/units.b4m" });

    // the reals ℝ (std/real.b4m): an axiomatic COMPLETE ordered field. MODELS
    // std/field/order.b4m + the least-upper-bound completeness AXIOM (a Real->Prop
    // predicate-argument axiom, like nonnegInduction). Carries isRational +
    // fromRational (ℚ↪ℝ embedding) to STATE facts about rationals — NO ℚ→ℝ transfer
    // model (ℚ has strictly fewer theorems than ℝ; nothing to lift, unlike ℕ↪ℤ).
    ctx.okSilent(&.{ "check", "std/real.b4m" });
    // ℝ* (std/real/units.b4m): the same for ℝ.
    ctx.okSilent(&.{ "check", "std/real/units.b4m" });
    // INTEGER POWERS on ℝ* (std/real/units-power.b4m): x^k for k ∈ ℤ, making ℝ* a model of
    // the group-power theory so the exponent laws and cyclic subgroups transfer.
    ctx.okSilent(&.{ "check", "std/real/units-power.b4m" });
    // ℝ∖{−1} UNDER a∗b = a + b + ab (std/real/affine-group.b4m): multiplication in disguise
    // ((1+a)(1+b) = 1 + a∗b), as a guarded model of std/group.b4m — AATA §3.2 Ex 7.
    ctx.okSilent(&.{ "check", "std/real/affine-group.b4m" });

    // the nonnegative square root on ℝ (std/real/sqrt.b4m): sqrt pinned by its
    // guarded defining axioms (sqrt(x)·sqrt(x)=x, sqrt≥0 for x≥0); proves
    // sqrtMulNonneg, sqrtOne. (Also hosts the ℝ-order helpers squareNonneg etc. —
    // those live in std/real.b4m.)
    ctx.okSilent(&.{ "check", "std/real/sqrt.b4m" });
    // trigonometry on ℝ (std/real/trig.b4m): sin, cos, π adjoined by their characterizing
    // identities (values at 0 and π, angle addition, Pythagoras); cos 2π = 1, sin 2π = 0 derived.
    ctx.okSilent(&.{ "check", "std/real/trig.b4m" });
    // natural multiples n·θ and the embedding ℕ → ℝ (std/real/scaling.b4m).
    ctx.okSilent(&.{ "check", "std/real/scaling.b4m" });

    // the complex numbers ℂ (std/complex.b4m): an axiomatic FIELD (NOT ordered).
    // MODELS std/field.b4m; adjoins the imaginary unit I with I²=−1; embeds ℝ via
    // fromReal/isReal with re/im parts and conj. Top of the ℚ/ℝ/ℂ tower. (A guarded
    // RealsInComplex order-transfer model is left unbuilt until a theorem needs it.)
    ctx.okSilent(&.{ "check", "std/complex.b4m" });

    // the complex modulus (std/complex/modulus.b4m, Judson §4.2): normSq/abs on ℂ and
    // the modulus identities (|z̄|=|z|, zz̄=|z|², |zw|=|z||w|) proved from ℂ's
    // projection algebra + real-sqrt (no trigonometry).
    ctx.okSilent(&.{ "check", "std/complex/modulus.b4m" });
    // polar form on ℂ (std/complex/polar.b4m, Judson §4.2): cis θ · cis φ = cis(θ+φ),
    // |cis θ| = 1, DeMoivre (r cis θ)^n = r^n cis(nθ), cis(2kπ/n)^n = 1, and the circle
    // group T as a subgroup of ℂ* (z⁻¹ = z̄ on T).
    ctx.okSilent(&.{ "check", "std/complex/polar.b4m" });

    // ℤ modeling the ring theory now lives INSIDE std/integer.b4m (the
    // `model IntegerRing` block + the negMulNeg transfer smoke test) — the
    // THREE-LEVEL chain ℤ → ring → group, checked with the base above.

    // the set theory (std/set.b4m): the membership axioms + extensionality, and
    // the 19 set-algebra identities (idempotence, identity, associativity,
    // commutativity, distributivity, De Morgan, difference laws) proved from them
    // by the extensionality→unfold→tautology recipe. Available for a structure to
    // `model` and inherit. The AATA transcription (aata/1.2.1-sets.md) aliases these.
    ctx.okSilent(&.{ "check", "std/set.b4m" });
    // EQUINUMEROSITY + finite cardinality (std/set/finite.b4m): size by BIJECTION, not by
    // an inductive count — so the vocabulary also covers infinite sets. The empty set has
    // size ZERO and is the ONLY set of that size (the base case of size uniqueness).
    ctx.okSilent(&.{ "check", "std/set/finite.b4m" });
    // THE POWER SET, COUNTED (std/set/subsets.b4m): the subsets of segment(n) as a LISTING
    // with 2^n entries — each subset of segment(n+1) is one of segment(n)'s either as it
    // stands or with the new letter added. AATA §2.1 Ex 12.
    ctx.okSilent(&.{ "check", "std/set/subsets.b4m" });

    // collections (std/collection.b4m): sets of sets, one level up. A Collection MODELS
    // std/set.b4m with set.Element -> Set, set.Set -> Collection, so the whole set
    // algebra transfers onto collections for free (contains = member one level up).
    // Plus the CROSS-LEVEL operations set.b4m lacks — bigUnion/bigIntersection
    // (collapse a collection to a set), a universe, and the partition apparatus
    // (covers / pairwiseDisjoint / isPartition) a quotient needs.
    ctx.okSilent(&.{ "check", "std/collection.b4m" });

    // the function theory (std/function.b4m): axioms only, no theorems — a
    // declarations-only DEPENDENCY. A direct check has nothing to prove, which is
    // a clean success (a file that proves zero theorems is fine).
    ctx.okSilent(&.{ "check", "std/function.b4m" });

    // invertible functions form a GROUP (std/function/invertible.b4m): the bijections
    // of a set under composition. A GUARDED model of std/group.b4m (guard = invertible)
    // — the group axioms proved on invertible functions (assoc/identities from funcExt;
    // inverse laws + closure under compose/inverse), then the group corpus (identity/
    // inverse uniqueness, involution, cancellation) transfers onto them for free.
    // Exercises cross-sort guarded weakening (group.Grp -> Fn where invertible).
    ctx.okSilent(&.{ "check", "std/function/invertible.b4m" });

    // ITERATES (std/function/iterate.b4m): f applied n times, with the two laws every orbit
    // argument leans on — the successor can be applied first or last (f^(n+1)(x) =
    // f^n(f(x))), and f^(m+n)(x) = f^m(f^n(x)).
    ctx.okSilent(&.{ "check", "std/function/iterate.b4m" });

    // permutations (std/permutation.b4m): the invertible maps as `Perm`, with what a
    // bare group lacks — the SUPPORT of a permutation (a comprehension set), that a
    // permutation preserves its support, disjoint-support permutations COMMUTE
    // (Judson's "disjoint cycles commute", cycle-free), transpositions (= finite.b4m's
    // swap: involution, permutation, own inverse), and `permutes(f, a)` — the
    // permutations OF a set — closed under identity, composition, inverse, and
    // containing every transposition of two members. Exercises aliasing a predicated
    // sort (`sort Perm = function_invertible.InvFn`), a `func` alias of a
    // definition-block symbol, and define-forwarding of another file's defines.
    ctx.okSilent(&.{ "check", "std/permutation.b4m" });

    // sequences of permutations (std/permutation/sequence.b4m): the group-sequence
    // postulates restated for permutations (every entry invertible), then a GUARDED model
    // of std/group/sequence.b4m onto Perm transfers the product laws. The transferred
    // inverse-of-a-product proof cites std/group.b4m's inverseUnique/invProduct through
    // group_sequence's ALIASES — the overlay-over-the-universe case
    // (tests/cases/model_alias_borrowed.b4m), on real std theories. What aata/5.1's
    // parity theory runs on.
    ctx.okSilent(&.{ "check", "std/permutation/sequence.b4m" });
    // ... and the worked examples that unpack its three sequence-building postulates.
    ctx.okSilent(&.{ "check", "std/permutation/sequence-examples.b4m" });

    // CYCLE NOTATION (std/permutation/cycle.b4m): (a₀ … a_k) over a list of points, DEFINED
    // by Judson's factorization (a₀ a_k)∘(a₀ … a_{k-1}) — always consistent, a permutation by
    // a one-line induction — with the textbook ACTION as theorems under distinctness: fixes
    // the unlisted, wraps the last to the first, advances the rest. One-cycle = identity,
    // two-cycle = transposition.
    ctx.okSilent(&.{ "check", "std/permutation/cycle.b4m" });

    // ORBITS (std/permutation/orbit.b4m): the set of iterates of a point, a comprehension set
    // like `support`; the point is in it, it is closed under the map, every iterate is the
    // point or a moved point (so the orbit sits inside support ∪ {x}), hence FINITE when the
    // support is — the first use of subsetOfFiniteIsFinite and of adding one element.
    ctx.okSilent(&.{ "check", "std/permutation/orbit.b4m" });

    // PERIODS (std/permutation/period.b4m): the family i ↦ f^i(x) packaged as a map on
    // numerals (definite description), the PIGEONHOLE principle (finite.b4m: a map from size
    // n+1 into size n collides — positive form, induction on n) applied to segment(m+1) → the
    // orbit, the collision cancelled through injectivity of iterates to a RETURN
    // f^(succ p)(x) = x, and a LEAST period by well-ordering.
    ctx.okSilent(&.{ "check", "std/permutation/period.b4m" });

    // THE CYCLE OF AN ORBIT (std/permutation/orbit-cycle.b4m): Points now has singleton and
    // prepend postulates; the list of iterates x, f(x), …, f^n(x) exists (induction with the
    // start quantified inside), every iterate is an early one once f^(p+1)(x) = x, the first
    // p+1 are distinct when p is the LEAST period (a collision would cancel to an earlier
    // return), and the cycle on that list agrees with f on the orbit (advance = next iterate;
    // wrap = the return) and fixes off it. orbitIsACycle packages the one-orbit decomposition.
    ctx.okSilent(&.{ "check", "std/permutation/orbit-cycle.b4m" });

    // THE DECOMPOSITION (std/permutation/decomposition.b4m): Judson's Theorem 5.8 — every
    // permutation of a finite set is a product of disjoint cycles. Peel one orbit's cycle c
    // off (f = c ∘ g with g = c⁻¹ ∘ f fixing the orbit and agreeing with f elsewhere, so
    // support(g) = support(f) \ orbit — a PROPER subset), strong induction on the size of
    // the support (properSubsetIsSmaller), prepend c to g's cycle sequence; c lives in the
    // orbit and g's cycles outside it, so the cycles stay pairwise disjoint. Runs over Fn
    // with `invertible` as a hypothesis and applies Perm-quantified theorems at those
    // terms — the refined-sort guard discharged from the prior step.
    ctx.okSilent(&.{ "check", "std/permutation/decomposition.b4m" });

    // PRODUCTS OF TRANSPOSITIONS (std/permutation/transpositions.b4m): a cycle is a product of
    // transpositions by its definition read as a prepend fold; concatenation keeps "every
    // entry is a transposition"; a product of products of transpositions is one; hence
    // Judson's Proposition 5.12 — every permutation of a finite set is a product of
    // transpositions (no "at least two elements": the identity is the empty product).
    ctx.okSilent(&.{ "check", "std/permutation/transpositions.b4m" });
    // JUDSON'S PARITY LEMMA, PROVED (std/permutation/parity.b4m): the identity is a product of
    // an EVEN number of transpositions. His four rewrite identities over concrete
    // transpositions, the classification of an adjacent pair, the sequence surgeries that keep
    // the product, the fixed-point argument, the descending loop and the outer strong
    // induction. Hole-free — it was an ASSUMPTION of aata/5.1 for a year on the mistaken
    // reading that it needs well-founded induction; it needs two nested ordinary ones.
    ctx.okSilent(&.{ "check", "std/permutation/parity.b4m" });

    // THE COUNT (std/permutation/count.b4m): |S_n| = n!, stated as a LISTING — a sequence
    // of n! permutations of the segment {0..n-1}, pairwise distinct, hitting every one.
    // Judson's exercise: a permutation of n+1 letters sending the top to k is (k n) times a
    // permutation of n letters, so n+1 blocks of n! entries (blocks concatenate by seqConcat,
    // a block is a swap mapped over the n-letter listing by mappedSequenceExists).
    ctx.okSilent(&.{ "check", "std/permutation/count.b4m" });

    // LISTING TOOLS (std/permutation/listing.b4m): SPLITTING a listing by a predicate (theorem
    // schemas in the predicate — sub-listings extend or skip an entry, an induction over the
    // prefix, lengths add up) and EQUAL LENGTHS of listings in bijection through an invertible
    // map (the index map, by definite description, bijects the two segments;
    // segmentSizeIsUnique). What |A_n| = n!/2 in aata/5.1 runs on.
    ctx.okSilent(&.{ "check", "std/permutation/listing.b4m" });

    // THE DIHEDRAL GROUP (std/permutation/dihedral.b4m): |D_n| = 2n for n ≥ 3, as a listing.
    // The rotation ρ is the n-cycle on the list of letters (cycle theory), the reflection σ
    // (i ↦ n - i, fixing 0) by definite description; a rigid motion preserves adjacency
    // (ρx = y or ρy = x). Powers of a map, the relation σρ = ρ⁻¹σ on the letters, ρ^k and
    // ρ^k∘σ are motions, EXHAUSTION by walking the letters (t(i+2) is a neighbour of
    // u(i+1) other than u(i)), the listing (powers ++ reflected powers), distinctness.
    ctx.okSilent(&.{ "check", "std/permutation/dihedral.b4m" });
    // INTEGER POWERS of a permutation (std/permutation/power.b4m): f^k for k ∈ ℤ by the three
    // group-power clauses; Perm as a GUARDED model of std/group/power.b4m, so the exponent laws
    // and the order theory (f^k = id ⟺ |f| divides k, conjugates share an order) transfer.
    ctx.okSilent(&.{ "check", "std/permutation/power.b4m" });
    // ORDERS IN D_n (std/permutation/dihedral-orders.b4m): the rotation has order n, and every
    // reflected power ρ^jσ has order 2 (σρ = ρ⁻¹σ as maps, so (ρ^jσ)² = id; no reflection is a
    // rotation) — the concrete answer to AATA §4.1 Ex 6 (D_4).
    ctx.okSilent(&.{ "check", "std/permutation/dihedral-orders.b4m" });

    // LISTINGS OF GROUP ELEMENTS (std/group/listing.b4m): splitting an injective listing by a
    // predicate (theorem schemas, as std/permutation/listing.b4m for maps), the PAIRING lemma
    // (a listing with no self-inverse entry and closed under inverse has even length — strong
    // induction, splitting off {g, g⁻¹}), and a finite group of even order has an element of
    // order 2 (Judson §3.2 Ex 32).
    ctx.okSilent(&.{ "check", "std/group/listing.b4m" });
}
