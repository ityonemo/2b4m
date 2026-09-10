# Corpus failure catalog (88 red build-steps, 2026-09-10)

All remaining reds are genuine Phase-5 feature backlog, punted debug/query
commands, or deliberately-deferred checks — NOT test/golden drift.

## [5] A: negative test now passes (deferred check: #93 schema / model-decl / feature gap)

- `t/div_nested.bpa` — OK: 4 declarations, 0 theorems proven
- `t/model_define_source_bad.bpa` — OK: 8 declarations, 0 theorems proven
- `t/model_schema_bad.bpa` — OK: 8 declarations, 0 theorems proven
- `t/schema_arithmetic_fallback_bad.bpa` — OK: 11 declarations, 1 theorems proven
- `t/schema_arithmetic_param_bad.bpa` — OK: 9 declarations, 0 theorems proven

## [1] C-model: arith/model diagnostic degraded (left red)

- `--fast t/model_bad.bpa` — the claim does not match the model transfer of 'source.opUnitLeftTwice':

## [15] C1: tautology over free var (unbuilt)

- `aata/1.2.1-sets.md` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `aata/1.2.3-partitions.md` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `aata/2.1-induction-exercises.md` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `std/cyclic.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `std/group-power.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `std/integer-order.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `std/integer-wellordering.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `std/peano-order.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `std/peano-order.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `std/peano-parity.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `std/set.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `t/arithmetic_cert_neg_cancel.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `t/arithmetic_cert_numeral_leaf.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `t/model_accel_tautology.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)
- `t/use_all_facts_accel_chain_ok.bpa` — tautology over a proof-local variable is not yet supported (free variable in the goal)

## [13] C2: 'not a predicate' resolution gap

- `aata/2.2-division-algorithm-exercises.md` — 'less_than' is not a predicate
- `aata/2.2-division-algorithm.md` — 'less_than' is not a predicate
- `aata/2.3-primes-exercises.md` — 'less_than' is not a predicate
- `aata/2.3-primes.md` — 'less_than' is not a predicate
- `aata/3.1-integers-mod-n-exercises.md` — 'divides' is not a predicate
- `aata/3.1-integers-mod-n.md` — 'divides' is not a predicate
- `aata/4.1-cyclic-subgroups-exercises.md` — 'less_than' is not a predicate
- `aata/4.1-cyclic-subgroups.md` — 'less_than' is not a predicate
- `examples/euclid.bpa` — 'divides' is not a predicate
- `std/complex-modulus.bpa` — 'less_or_equal' is not a predicate
- `std/group-order.bpa` — 'less_than' is not a predicate
- `std/primes.bpa` — 'inSeqBefore' is not a predicate
- `std/real-sqrt.bpa` — 'less_or_equal' is not a predicate

## [11] C3: polynomial/assoc_commut algebra gap

- `--fast t/polynomial_coeff.bpa` — polynomial: the goal has no add/mul structure
- `--fast t/polynomial_field.bpa` — polynomial: the goal has no add/mul structure
- `--fast t/polynomial_neg.bpa` — polynomial: the goal has no add/mul structure
- `std/field.bpa` — polynomial: the goal has no add/mul structure
- `std/rational.bpa` — polynomial: the goal has no add/mul structure
- `std/real.bpa` — polynomial: the goal has no add/mul structure
- `t/distribute.bpa` — assoc_commut: sides have different summands: 'add(mul(a, c), mul(b, c))' vs 'add(mul(b, c), mul(a, c))'
- `t/polynomial_coeff.bpa` — polynomial: the goal has no add/mul structure
- `t/polynomial_field.bpa` — polynomial: the goal has no add/mul structure
- `t/polynomial_inverse.bpa` — polynomial: sides expand differently: 'add(x, add(mul(a, r), neg(mul(a, r))))' vs 'x'
- `t/polynomial_neg.bpa` — polynomial: the goal has no add/mul structure

## [5] C4: guarded functions unsupported

- `examples/incorrect.bpa` — guarded functions ('requires') are not yet supported by the demand prover
- `std/peano-divides.bpa` — guarded functions ('requires') are not yet supported by the demand prover
- `t/div_bad.bpa` — guarded functions ('requires') are not yet supported by the demand prover
- `t/div_ok.bpa` — guarded functions ('requires') are not yet supported by the demand prover
- `t/imports/guarded_bad.bpa` — guarded functions ('requires') are not yet supported by the demand prover

## [7] C5: arithmetic certifier declines

- `aata/2.1-induction.md` — 'arithmetic' is valid but no certifier could prove it here (equation/order/exists, farkas, cooper all declined
- `examples/gauss.bpa` — 'arithmetic' is valid but no certifier could prove it here (equation/order/exists, farkas, cooper all declined
- `t/arithmetic_bad.bpa` — arithmetic: not a consequence of the cited premises
- `t/arithmetic_frag.bpa` — arithmetic: not a consequence of the cited premises
- `t/cooper_gap_raw.bpa` — 'arithmetic' is valid but no certifier could prove it here (equation/order/exists, farkas, cooper all declined
- `t/cooper_witness.bpa` — 'arithmetic' is valid but no certifier could prove it here (equation/order/exists, farkas, cooper all declined
- `t/smt_bad.bpa` — arithmetic: not a consequence of the cited premises

## [20] C6: name/sort resolution gap

- `aata/1.2.1-sets-exercises.md` — 'set' names an identifier, not an axiom/theorem
- `aata/1.2.2-functions-exercises.md` — 'function' names an identifier, not an axiom/theorem
- `aata/3.2-groups-exercises.md` — unknown sort ''
- `aata/3.3-subgroups-exercises.md` — unknown sort ''
- `aata/4.2-complex-multiplicative-group-exercises.md` — 'abs' is not a function
- `aata/4.2-complex-multiplicative-group.md` — 'abs' is not a function
- `examples/euclid-compute.bpa` — unknown sort ''
- `examples/sqrt2.bpa` — unknown sort 'Dividable'
- `std/collection.bpa` — expected sort 'Set', got 'Collection'
- `std/complex.bpa` — expected sort 'Complex', got 'Real'
- `std/function-invertible.bpa` — forall_elim: 'invertible(inverse(inverse(a))) -> forall y: Fn; invertible(y) -> forall z: Fn; invertible(z) ->
- `std/integer-divides.bpa` — '' is not callable
- `std/integer-mod-n.bpa` — expected sort 'Zn', got 'Int'
- `std/integer-sequence.bpa` — reference not found: 'nonneg'
- `std/integer-sum.bpa` — reference not found: 'nonneg'
- `t/arithmetic_missing_lemma_diagnostic.bpa` — reference not found: 'addLeftSwap'
- `t/model_axiom_colon_bad.bpa` — 'combineZedLeft' names a fact, not a sort/constant/function/predicate
- `t/model_maps_theorem_bad.bpa` — 'leftUnit' names a fact, not a sort/constant/function/predicate
- `t/model_symbol_arrow_bad.bpa` — 'op' names an identifier, not an axiom/theorem
- `t/strong_induction.bpa` — reference not found: 'myPred'

## [3] C7: unused-fact strictness

- `--fast examples/peano.bpa` — unused fact: step 'inductive-hypothesis' is never used — no later step or the conclusion cites it (a proof mus
- `--fast t/arithmetic.bpa` — unused fact: step 'have' is never used — no later step or the conclusion cites it (a proof must use every fact
- `--fast t/use_all_facts_fast_schema_ok.bpa` — unused fact: step 'premise' is never used — no later step or the conclusion cites it (a proof must use every f

## [1] C9: extensionality accelerant gap

- `t/model_accel_extensionality.bpa` — extensionality_quantified requires an extensionality lemma: [using extensionality_quantified(<lemma>) <unfold 

## [3] Z: individual

- `std/field-order.bpa` — step claims 'forall a: OrderedField; add(a, neg(a)) = ZERO' but the theorem derives 'forall a: Field; add(a, n
- `t/define_where_guard_inline.bpa` — sort refinement 'isBig' must be a unary predicate
- `t/use_all_facts_tcc_ok.bpa` — unproved obligation: 'forall g: G; inH(g) -> inH(succ(g))'

## [4] Z: other

- `15` — usage: bpa check [--fast | --fast-only W… | --fast-except W…] [--draft] <file.bpa>
- `polySchema poly-step` — usage: bpa check [--fast | --fast-only W… | --fast-except W…] [--draft] <file.bpa>
- `sumParity conclusion` — usage: bpa check [--fast | --fast-only W… | --fast-except W…] [--draft] <file.bpa>
- `valArith arith-step` — usage: bpa check [--fast | --fast-only W… | --fast-except W…] [--draft] <file.bpa>
