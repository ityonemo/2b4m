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

    // cyclic subgroups (std/cyclic.b4m, Judson §4.1): ⟨a⟩ = {a^k} as a membership
    // predicate over a fixed generator const, proved a subgroup (identity/closure) and
    // the smallest one containing a (integer induction), plus cyclic ⇒ abelian.
    ctx.okSilent(&.{ "check", "std/cyclic.b4m" });

    // order of a group element (std/group/order.b4m, Judson §4.1): the fixed-A/N form
    // proves a^k = e ⟺ n|k and ord(a^k) = n/gcd(k,n) (via euclidFromBezout); the
    // hasOrder(g,n) RELATION generalizes order over arbitrary elements (orderIsUnique,
    // inverseHasSameOrder = |a|=|a⁻¹|).
    ctx.okSilent(&.{ "check", "std/group/order.b4m" });

    // the integers mod n (std/integer/mod-n.b4m, Judson §4.1 concrete): ℤ_n as a
    // quotient sort ℤ/nℤ whose group/ring axioms LIFT from ℤ via cls-homomorphism,
    // with ZnGroup/ZnGroupPower/ZnRing models (⟨1⟩ cyclic) and the units U(n) as a
    // group (UnitsGroup). An abstract TEMPLATE modeled at a concrete n.
    ctx.okSilent(&.{ "check", "std/integer/mod-n.b4m" });

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

    // the rationals ℚ (std/rational.b4m): the prime ordered field. MODELS
    // std/field/order.b4m (RationalOrderedField, the algebra lens) + a ring embedding
    // ℤ↪ℚ (fromInt: homomorphism + injective) linking integer arithmetic to ℚ.
    // Derives fromIntNonzero (nonzero ints embed to invertible rationals). First
    // concrete sort of the tower; independent, containment-by-embedding.
    ctx.okSilent(&.{ "check", "std/rational.b4m" });

    // the reals ℝ (std/real.b4m): an axiomatic COMPLETE ordered field. MODELS
    // std/field/order.b4m + the least-upper-bound completeness AXIOM (a Real->Prop
    // predicate-argument axiom, like nonnegInduction). Carries isRational +
    // fromRational (ℚ↪ℝ embedding) to STATE facts about rationals — NO ℚ→ℝ transfer
    // model (ℚ has strictly fewer theorems than ℝ; nothing to lift, unlike ℕ↪ℤ).
    ctx.okSilent(&.{ "check", "std/real.b4m" });

    // the nonnegative square root on ℝ (std/real/sqrt.b4m): sqrt pinned by its
    // guarded defining axioms (sqrt(x)·sqrt(x)=x, sqrt≥0 for x≥0); proves
    // sqrtMulNonneg, sqrtOne. (Also hosts the ℝ-order helpers squareNonneg etc. —
    // those live in std/real.b4m.)
    ctx.okSilent(&.{ "check", "std/real/sqrt.b4m" });

    // the complex numbers ℂ (std/complex.b4m): an axiomatic FIELD (NOT ordered).
    // MODELS std/field.b4m; adjoins the imaginary unit I with I²=−1; embeds ℝ via
    // fromReal/isReal with re/im parts and conj. Top of the ℚ/ℝ/ℂ tower. (A guarded
    // RealsInComplex order-transfer model is left unbuilt until a theorem needs it.)
    ctx.okSilent(&.{ "check", "std/complex.b4m" });

    // the complex modulus (std/complex/modulus.b4m, Judson §4.2): normSq/abs on ℂ and
    // the modulus identities (|z̄|=|z|, zz̄=|z|², |zw|=|z||w|) proved from ℂ's
    // projection algebra + real-sqrt (no trigonometry).
    ctx.okSilent(&.{ "check", "std/complex/modulus.b4m" });

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
}
