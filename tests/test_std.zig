//! Integration gates — the standard library files (std/peano* , group, set, function) — the pinned declaration/theorem counts.
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

    // the standard library must check
    ctx.okSilent(&.{ "check", "std/peano.bpa" });

    // the order theory + strong induction + well-ordering, split into its own
    // layer; proven, and --recursive re-verifies the imported peano proofs too
    ctx.okSilent(&.{ "check", "std/peano-order.bpa" });

    ctx.okSilent(&.{ "check", "std/peano-order.bpa" });

    // truncated subtraction + the gcd measure lemma (Euclid foundation)
    ctx.okSilent(&.{ "check", "std/peano-subtraction.bpa" });

    // divisibility, the guarded Euclidean div/mod, and THE PAYOFF: Euclid's
    // algorithm proved correct (common divisor + greatest), by strong
    // induction on the decreasing modulus — the whole ℕ number-theory unit
    ctx.okSilent(&.{ "check", "std/peano-divides.bpa" });

    // parity: even/odd + the crux 2|p² → 2|p, proven (no accelerated tactic)
    ctx.okSilent(&.{ "check", "std/peano-parity.bpa" });

    // the ℤ base std/integer.bpa now bundles the ring algebra (left/right
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
    ctx.okSilent(&.{ "check", "std/integer-order.bpa" });

    // strong induction + the Principle of Well-Ordering over the NONNEGATIVE
    // integers (std/integer-wellordering.bpa), layered above the ℤ order (it can't
    // live in integer-nonneg, which sits below the order in the import DAG).
    // nonnegStrongInduction (course-of-values) and nonnegWellOrdering (every
    // nonempty nonneg subset has a least element) — nonneg-guarded ports of the
    // peano-order proofs; the Division Algorithm's existence half runs on these.
    ctx.okSilent(&.{ "check", "std/integer-wellordering.bpa" });

    // abstract divisibility (std/divisibility.bpa): a carrier with mul/add/ONE
    // and the divides predicate; dividesRefl/dividesMul/dividesAdd proved once,
    // over the abstract carrier. ℕ and ℤ `model` this to inherit them.
    ctx.okSilent(&.{ "check", "std/divisibility.bpa" });

    // the whole ℤ number-theory unit (std/integer-divides.bpa): divisibility
    // (`divides` intro/elim, the refl/mul/add facts TRANSFERRED from the abstract
    // theory via `model IntegerDivisibility`) + powers; the Division Algorithm
    // (existence over all of ℤ via well-ordering on {a−bk≥0} + uniqueness, with the
    // product-of-nonnegatives / bounded-multiple-is-zero / remainder-difference
    // machinery); and the GCD / Bézout theory (the existence-form gcd `bezout` and
    // its coprime specialization `coprimeBezout`, the engine of Euclid's Lemma). An
    // independent std development of the theory AATA §2.2/§2.3 prove inline.
    ctx.okSilent(&.{ "check", "std/integer-divides.bpa" });

    // the abstract, ℕ-indexed sequence + FOLD theory (std/sequence.bpa): an opaque
    // `Seq` over an abstract `Value` with an `at` accessor, an abstract `combine`/
    // `IDENTITY` fold (`foldUpTo`) + recursion axioms, and fold-structure theorems.
    // This is the STRUCTURE that std/integer-sequence.bpa models (Value:Int,
    // combine:mul, IDENTITY:ONE, foldUpTo:productUpTo) to recover the finite product.
    ctx.okSilent(&.{ "check", "std/sequence.bpa" });

    // finite integer sequences + products (std/integer-sequence.bpa): a `Seq` sort
    // with an `at(s,i)` accessor and a recursive `productUpTo(s,k)` over the nonneg-ℤ
    // index sort, obtained by MODELING the abstract fold above (bpa has no lists/
    // finite products, so the indexed family is reified as a sort). everyEntryDivides-
    // Product — each entry below the bound divides the product — is the lemma the
    // infinitude/FTA arguments need. Plus the reification-existence axioms
    // (seqSingletonExists/seqConcatExists/seqRemoveExists) that let FTA
    // witness/splice/cancel factorization sequences.
    ctx.okSilent(&.{ "check", "std/integer-sequence.bpa" });

    // the reusable ℤ PRIME THEORY (std/primes.bpa): primality packaged once as a
    // transparent `define is_prime`, then Euclid's Lemma (via coprimeBezout),
    // primeDividesProductImpliesMember (FTA-uniqueness crux), and the infinitude
    // of primes — an independent std development of the facts that aata/2.3-primes.md
    // proves inline. Layers over std/integer-divides.bpa + std/integer-sequence.bpa.
    ctx.okSilent(&.{ "check", "std/primes.bpa" });

    // the group theory (std/group.bpa): THREE axioms (associativity + LEFT identity
    // + LEFT inverse) + an opt-in `opCommutative`; the right-sided laws and the
    // basic-property theorems (identityUnique, inverseUnique, invProduct, cancelLeft,
    // …) are proved from those axioms alone. aata/3.2-groups.md aliases these.
    ctx.okSilent(&.{ "check", "std/group.bpa" });

    // group powers (std/group-power.bpa): g^n over a Nat exponent, layered over
    // std/group.bpa + std/peano.bpa (keeping the core group theory import-free).
    // Defines pow(g,n) recursively and proves the exponent-addition law
    // powAdd: pow(g, m+n) = op(pow(g,m), pow(g,n)) by induction on n.
    ctx.okSilent(&.{ "check", "std/group-power.bpa" });

    // finite group products (std/group-sequence.bpa): models std/sequence.bpa's
    // fold with op/E to get productUpTo(s, n) = g0·…·g_{n-1}, and proves the n-ary
    // inverse law invOfProduct: inv(g0·…·g_{n-1}) = g_{n-1}⁻¹·…·g0⁻¹ (Judson §3.2
    // Ex 27) by induction, step = binary invProduct. Never cites opCommutative.
    ctx.okSilent(&.{ "check", "std/group-sequence.bpa" });

    // finite integer sums (std/integer-sum.bpa): the SECOND fold over sequence.bpa
    // (combine:add, IDENTITY:ZERO) → sumUpTo(s, n) = Σ_{i<n} at(s,i). Identity-style
    // sequences (at(i)=i, i², i³, (3i+1)X) + nonneg-induction prove §2.1 Ex 1/2/4 and
    // the Gauss sum in DIVISION-FREE form (6·Σi²=(n-1)n(2n-1), 4·Σi³=(n(n-1))², etc.)
    // — ℚ not needed, only the fractional notation would be; ring steps by polynomial.
    ctx.okSilent(&.{ "check", "std/integer-sum.bpa" });

    // subgroups (std/subgroup.bpa, Judson §3.3): a STANDALONE theory (declares its own
    // parent group) — the subgroup criteria, the one-step test (both directions), the
    // intersection, and the five group axioms proven on the subgroup (what a group-
    // model @-projects). Authored to plug into std/group.bpa via a model stack.
    ctx.okSilent(&.{ "check", "std/subgroup.bpa" });

    // the ring theory (std/ring.bpa): an additive abelian group + associative,
    // distributing multiplication. Its additive half MODELS std/group.bpa (a
    // TWO-LEVEL structure — a model inside a modelable theory). Judson's first
    // ring proposition (a·0=0·a=0; a(-b)=(-a)b=-(ab); (-a)(-b)=ab) is proved by
    // TRANSFERRING the additive-group cancelRight/inverseUnique/invInvolution
    // through the AdditiveGroup model rather than re-deriving them. Left-axiomatic:
    // only addZeroLeft/addNegLeft are axioms; the RIGHT laws (addZeroRight,
    // addNegRight) are the two derived theorems the model no longer needs to map.
    // (the synthetic materialized theorems are suppressed.)
    ctx.okSilent(&.{ "check", "std/ring.bpa" });

    // the field theory (std/field.bpa): a commutative ring with unit + a partial
    // multiplicative inverse `recip` (total func, guarded axiom x≠0 → x·recip x = 1).
    // MODELS std/ring.bpa to inherit the ring corpus; derives mulOneRight,
    // recipMulLeft, and noZeroDivisors (a·b=0 → a=0 or b=0). Base of the ℚ/ℝ/ℂ tower.
    ctx.okSilent(&.{ "check", "std/field.bpa" });

    // the ordered-field theory (std/field-order.bpa): a field + a total strict order
    // `less_than` compatible with the ops (translation-invariant add, positive
    // product). MODELS std/field.bpa; postulates the order abstractly (opaque pred +
    // axioms, unlike the constructed ℤ order) and derives asymmetry etc. ℚ/ℝ model it.
    ctx.okSilent(&.{ "check", "std/field-order.bpa" });

    // the rationals ℚ (std/rational.bpa): the prime ordered field. MODELS
    // std/field-order.bpa (RationalOrderedField, the algebra lens) + a ring embedding
    // ℤ↪ℚ (fromInt: homomorphism + injective) linking integer arithmetic to ℚ.
    // Derives fromIntNonzero (nonzero ints embed to invertible rationals). First
    // concrete sort of the tower; independent, containment-by-embedding.
    ctx.okSilent(&.{ "check", "std/rational.bpa" });

    // the reals ℝ (std/real.bpa): an axiomatic COMPLETE ordered field. MODELS
    // std/field-order.bpa + the least-upper-bound completeness AXIOM (a Real->Prop
    // predicate-argument axiom, like nonnegInduction). Carries isRational +
    // fromRational (ℚ↪ℝ embedding) to STATE facts about rationals — NO ℚ→ℝ transfer
    // model (ℚ has strictly fewer theorems than ℝ; nothing to lift, unlike ℕ↪ℤ).
    ctx.okSilent(&.{ "check", "std/real.bpa" });

    // the complex numbers ℂ (std/complex.bpa): an axiomatic FIELD (NOT ordered).
    // MODELS std/field.bpa; adjoins the imaginary unit I with I²=−1; embeds ℝ via
    // fromReal/isReal with re/im parts and conj. Top of the ℚ/ℝ/ℂ tower. (A guarded
    // RealsInComplex order-transfer model is left unbuilt until a theorem needs it.)
    ctx.okSilent(&.{ "check", "std/complex.bpa" });

    // ℤ modeling the ring theory now lives INSIDE std/integer.bpa (the
    // `model IntegerRing` block + the negMulNeg transfer smoke test) — the
    // THREE-LEVEL chain ℤ → ring → group, checked with the base above.

    // the set theory (std/set.bpa): the membership axioms + extensionality, and
    // the 19 set-algebra identities (idempotence, identity, associativity,
    // commutativity, distributivity, De Morgan, difference laws) proved from them
    // by the extensionality→unfold→tautology recipe. Available for a structure to
    // `model` and inherit. The AATA transcription (aata/1.2.1-sets.md) aliases these.
    ctx.okSilent(&.{ "check", "std/set.bpa" });

    // collections (std/collection.bpa): sets of sets, one level up. A Collection MODELS
    // std/set.bpa with set.Element -> Set, set.Set -> Collection, so the whole set
    // algebra transfers onto collections for free (contains = member one level up).
    // Plus the CROSS-LEVEL operations set.bpa lacks — bigUnion/bigIntersection
    // (collapse a collection to a set), a universe, and the partition apparatus
    // (covers / pairwiseDisjoint / isPartition) a quotient needs.
    ctx.okSilent(&.{ "check", "std/collection.bpa" });

    // the function theory (std/function.bpa): axioms only, no theorems — a
    // declarations-only DEPENDENCY. A direct check has nothing to prove, which is
    // the correct outcome: an informational note, exit 0 (NOT a warning — the
    // warning is reserved for a file that DECLARES theorems but proves none).
    ctx.ok(&.{ "check", "std/function.bpa" },
        \\OK: 16 declarations, 0 theorems proven
        \\  — note: no theorems to check (a declarations-only file: axioms/defs/schemas — a dependency, not a proof file).
        \\
    );

    // invertible functions form a GROUP (std/function-invertible.bpa): the bijections
    // of a set under composition. A GUARDED model of std/group.bpa (guard = invertible)
    // — the group axioms proved on invertible functions (assoc/identities from funcExt;
    // inverse laws + closure under compose/inverse), then the group corpus (identity/
    // inverse uniqueness, involution, cancellation) transfers onto them for free.
    // Exercises cross-sort guarded weakening (group.Grp -> Fn where invertible).
    ctx.okSilent(&.{ "check", "std/function-invertible.bpa" });
}
