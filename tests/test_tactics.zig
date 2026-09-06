//! Integration gates — the automation tactics and their fixtures: simplify, ac / assoc / distribute, polynomial, tautology, arithmetic / Presburger, Farkas, and their `_bad` diagnostics.
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
    // Milestone A: simplify — certificate-producing rewrite tactic
    ctx.okSilent(&.{ "check", "tests/cases/simplify.bpa" });

    // simplify always emits kernel steps (never accelerates): the default check accepts it
    ctx.okSilent(&.{ "check", "tests/cases/simplify.bpa" });

    // unjoinable normal forms: the diagnostic shows both, copy-pasteable
    ctx.fail(&.{ "check", "tests/cases/simplify_bad.bpa" }, "tests/cases/simplify_bad.bpa:14:16: error: simplify: normal forms differ: 'add(n, ZERO)' vs 'n'\n");

    // cycling rules hit the hard rewrite cap instead of hanging
    ctx.fail(&.{ "check", "tests/cases/simplify_loop.bpa" }, "tests/cases/simplify_loop.bpa:13:12: error: simplify: rewrite limit reached (looping rule set?)\n");

    // ac: associative-commutative sum reordering over opaque atoms, emits kernel steps
    ctx.okSilent(&.{ "check", "tests/cases/ac.bpa" });

    // ac over multiplication: same bubble-sort machinery, mul lemma triple
    // (mulIsAssociative/mulIsCommutative/mulLeftSwap), emits kernel steps
    ctx.okSilent(&.{ "check", "tests/cases/ac_mul.bpa" });

    // ac_quantified: peel the forall prefix then run the ac core (add + mul)
    ctx.okSilent(&.{ "check", "tests/cases/ac_quantified.bpa" });

    // distributivity: ac_quantified with a cited distributivity lemma
    // pre-normalizes (distributes) each side before the AC bubble-sort
    ctx.okSilent(&.{ "check", "tests/cases/distribute.bpa" });

    // `polynomial(theory)`: nonlinear identities canonicalize, emitting kernel
    // steps (no accelerated tactic) via distribute → sort monomials → sort sum → fold.
    ctx.okSilent(&.{ "check", "tests/cases/polynomial.bpa" });

    // sides with different expansions → located error, exit 1 (not accelerated)
    ctx.fail(&.{ "check", "tests/cases/polynomial_bad.bpa" }, "tests/cases/polynomial_bad.bpa:18:9: error: polynomial: sides expand differently: 'add(mul(b, b), add(mul(b, a), add(mul(b, a), mul(a, a))))' vs 'add(mul(b, b), mul(a, a))'\n");

    // `polynomial` expands sub/neg (definitionOfSubtraction + neg-folds push neg
    // to the leaves), cancels additive inverses (t + neg(t) → 0), and folds
    // numeral coefficients (q+q → 2·q, 2q+2q → 4q) — strict cert + --fast parity.
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_neg.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_inverse.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_coeff.bpa" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_neg.bpa" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_inverse.bpa" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_coeff.bpa" });

    // polynomial(field): the accelerant over a FIELD theory (bare ONE constant,
    // not the ℤ succ-tower). Guards field.bpa's ring-lemma shims + swaps resolving
    // by bare name in field's scope, and the additive-inverse cancellation of the
    // bare ONE atom (ONE + neg(ONE) → 0). Strict cert + --fast parity.
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_field.bpa" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_field.bpa" });
    // a wrong coefficient (q+q claimed = 3·q) is still rejected: q+q expands to
    // add(q, q), 3·q to add(q, add(q, q)) — real repeated-addition arithmetic.
    ctx.fail(&.{ "check", "tests/cases/polynomial_coeff_bad.bpa" }, "tests/cases/polynomial_coeff_bad.bpa:15:9: error: polynomial: sides expand differently: 'add(q, q)' vs 'add(q, add(q, q))'\n");

    // `ext(theory)`: the extensionality tactic, one tactic over two models —
    // reduce an equation to its pointwise obligation via the theory's
    // extensionality lemma, unfold the operators, close the residue. SET model
    // (propositional residue → tautology); emits kernel steps.
    ctx.okSilent(&.{ "check", "tests/cases/extensionality_set.bpa" });
    // FUNCTION model (equational residue → rewrite join) — same `ext` tactic.
    ctx.okSilent(&.{ "check", "tests/cases/extensionality_function.bpa" });
    // a FALSE set identity: the pointwise residue has a countermodel, so ext
    // declines with a located error (exit 1) — never accepts a false equation.
    ctx.fail(&.{ "check", "tests/cases/extensionality_bad.bpa" }, "tests/cases/extensionality_bad.bpa:18:12: error: extensionality: could not close the pointwise obligation propositionally (is the identity true?)\n");

    // `model`: structure reuse. The source theory (a carrier + op + left-unit +
    // one proven theorem) is modeled by a concrete sort, and its theorem
    // transfers, remapped through the model.
    ctx.okSilent(&.{ "check", "tests/cases/model_source.bpa" });

    // --fast trusts the transfer wholesale (remap the source theorem, α-match the
    // goal, taint accelerated: model) — checks nothing about the source proof.
    ctx.ok(&.{ "check", "--fast", "tests/cases/model_transfer.bpa" },
        \\OK: 13 declarations, 3 theorems proven (1 accelerated: model)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );
    // default (strict) MATERIALIZES the remapped source proof as a synthetic
    // kernel-checked theorem (suppressed from the count) and cites it — so it
    // passes with NO taint. The transfer is genuinely kernel-verified.
    ctx.okSilent(&.{ "check", "tests/cases/model_transfer.bpa" });

    // DEPENDENCY WALK: transferring a source theorem whose proof cites ANOTHER
    // source theorem forces strict materialization to recurse into it (memoized —
    // the shared dependency materializes once across both cites). Kernel-checked.
    ctx.okSilent(&.{ "check", "tests/cases/model_recurse.bpa" });
    ctx.ok(&.{ "check", "--fast", "tests/cases/model_recurse.bpa" },
        \\OK: 14 declarations, 4 theorems proven (2 accelerated: model)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // MATERIALIZATION CITATION RULE: a materialized model proof may cite another
    // materialized theorem; a substitution-INVARIANT theorem/axiom (as-is, walk
    // ends); or a substituted axiom mapped (to a theorem OR an axiom). It may NOT
    // cite a fact the substitution AFFECTS but the model doesn't map.
    // OK exercises invariant-theorem + invariant-axiom + axiom→theorem + axiom→axiom:
    ctx.okSilent(&.{ "check", "tests/cases/model_cite_ok.bpa" });
    // BAD leaves an affected axiom (opUnitRight, cited by the transferred proof)
    // unmapped → rejected, naming it.
    ctx.fail(&.{ "check", "tests/cases/model_cite_bad.bpa" }, "tests/cases/model_cite_bad.bpa:33:27: error: model materialization cites axiom 'opUnitRight', which the substitution affects but the model does not map; add a mapping for it\n");
    // a model maps only the source theory's AXIOMS; mapping a source THEOREM (which
    // materializes through the mapped axioms) is misuse and rejected at that mapping.
    ctx.fail(&.{ "check", "tests/cases/model_maps_theorem_bad.bpa" }, "tests/cases/model_maps_theorem_bad.bpa:19:3: error: model maps only axioms; 'src.leftUnit' is a theorem — it materializes through the mapped axioms, so drop this mapping\n");

    // a transparent (`define`d) symbol cannot be a model mapping source/target — it
    // rides along on the primitives in its body (which the model maps); nominally
    // remapping its NAME would ignore the definition (definition-blind, unsound).
    ctx.fail(&.{ "check", "tests/cases/model_define_source_bad.bpa" }, "tests/cases/model_define_source_bad.bpa:21:3: error: 'TWICE' is a transparent (`define`d) symbol — it rides along on the primitives in its body and cannot be a model mapping source; map those primitives instead\n");

    // …but a define'd TARGET is legitimate: mapping a source symbol ONTO a defined
    // target EXPRESSION works — the target expands to its body during transfer, so
    // `source.UNIT: DOUBLED` yields combine(ZED, ZED) in the materialized theorem.
    ctx.okSilent(&.{ "check", "tests/cases/model_define_target.bpa" });

    // GUARDED model (`model … where <pred>`): the transfer is RELATIVIZED — every
    // carrier ∀ gains `guard(x) ->` — and strict materialization discharges the
    // guard obligation at each forall_elim over a guarded universal (recursing on
    // the instantiation term: constant → base closure fact; eigenvariable → the
    // in-scope `assume guard(a)`; composite → a closure fact + recursion). Fully
    // kernel-checked, no taint.
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_source.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded.bpa" });
    // clean-error boundary: a guarded transfer whose proof instantiates at a term
    // with no closure fact in scope fails with an actionable message (the graceful
    // fallback point for future author-supplied obligations).
    ctx.fail(&.{ "check", "tests/cases/model_guarded_noclose.bpa" }, "tests/cases/model_guarded_noclose.bpa:31:27: error: guarded model 'ThingModel' cannot discharge the closure obligation 'good(ZED)' — supply an axiom or theorem establishing it, in scope where model 'ThingModel' is declared\n");
    // BOUNDARY fixtures (all now handled): a guarded transfer of a proof that
    // unpacks an existential witness surfaces `guard(w)` from the relativized
    // `∃x; guard(x) and P(x)` conjunct (and re-guards a matching `exists_intro`);
    // a case split re-emits or_elim + arm hypotheses. (Sources check fine too.)
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_witness_source.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_witness.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_case_source.bpa" });
    // case split (or_elim + hypothesis) now materializes guardedly.
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_case.bpa" });
    // SAME-FILE guarded model: the source theory and the model share one file (the
    // paradigm subgroup case — H ⊆ G on one carrier). Mapping sources are bare
    // (unqualified) names resolved locally; no import/two-file split required.
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_samefile.bpa" });
    // AUTO-WEAKENING: a source axiom that holds unconditionally on the carrier,
    // mapped to ITSELF, has its relativized obligation (`inH(a) -> P(a)`)
    // synthesized by the materializer as a free weakening — no hand-written
    // relativized copy. (∀a;P(a) ⊢ ∀a; guard(a)->P(a).)
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_weaken_source.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_weaken.bpa" });
    // MULTI-BINDER auto-weakening: an unconditional axiom over N carrier binders
    // (here 2), mapped to itself, weakened by nested fix/assume with one chained
    // forall_elim at the core. Needed for group axioms like opAssoc (3 binders).
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_weaken_multi_source.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_weaken_multi.bpa" });
    // the paradigm case end to end: a SUBGROUP modeling its own group's carrier —
    // same-file guarded model + auto-weakening (opIdentityLeft mapped to itself) +
    // inH(E) proved by contradiction from the definitional subgroup axioms.
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_subgroup.bpa" });
    // THE MODEL STACK end to end over std/group + std/subgroup:
    //  - a subgroup inH of a group; the 8-theorem group corpus transfers onto H
    //    through HSubGroup→HGroup (each `group.X` discharged via a `@`-projection
    //    mapping value `HSubGroup@subgroup.X`).
    //  - K < H < G: a subgroup inK OF the subgroup H; the same stack (KSubGroup→
    //    KGroup) transfers three group theorems onto the sub-subgroup K. Composes
    //    on existing machinery (flattened single-guard K = Grp where inK, inK ⊆ inH).
    // Exercises the DIRECT-MAPPED-axiom transfer (group.opAssoc, an axiom, discharged
    // through a `@`-projection → cite the mapped discharge, not materialize a proof).
    ctx.okSilent(&.{ "check", "tests/cases/model_subgroup_transfer.bpa" });

    // SCHEMA TRANSFER through a guarded model: a source induction SCHEMA
    // (elemInduction) is discharged by a local guard-relativized schema
    // (goodInduction), α-checked at the model decl against the remapped source;
    // `[using model(...) source.elemInduction]` then instantiates the discharge.
    ctx.okSilent(&.{ "check", "tests/cases/model_schema_source.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_schema.bpa" });
    // RED: a schema source must be discharged by a SCHEMA (matching predicate
    // parameter); a plain axiom cannot, and the model decl rejects it.
    ctx.fail(&.{ "check", "tests/cases/model_schema_bad.bpa" }, "tests/cases/model_schema_bad.bpa:20:27: error: 'notASchema' discharges a schema, so it must itself be a schema (with a matching predicate parameter)\n");

    // MODEL SYNTAX: `:` interprets a sort/symbol, `<-` discharges an axiom
    // obligation. The happy path uses both; the two rejection paths are hard errors.
    ctx.okSilent(&.{ "check", "tests/cases/model_obligation_arrow.bpa" });
    // `:` on an axiom obligation → error, directing to `<-`.
    ctx.fail(&.{ "check", "tests/cases/model_axiom_colon_bad.bpa" }, "tests/cases/model_axiom_colon_bad.bpa:17:3: error: 'source.opUnitLeft' is an axiom obligation, not a sort/symbol — discharge it with `<-` (`source.opUnitLeft <- <local fact>`), not `:`\n");
    // `<-` on a sort/symbol → error, directing to `:`.
    ctx.fail(&.{ "check", "tests/cases/model_symbol_arrow_bad.bpa" }, "tests/cases/model_symbol_arrow_bad.bpa:15:3: error: 'source.op' is a sort or symbol, not an axiom — map it with `:` (`source.op: <target>`), not `<-`\n");

    // ACCELERANT-THROUGH-GUARDED-MODEL boundary (RED characterization, one per
    // accelerant). Transferring a source theorem whose proof USES an accelerant
    // through a GUARDED model currently fails: the accelerant builds its synthetic
    // theorem at elaboration in the SOURCE space, blind to the model, so guarded
    // re-emission (which inserts `assume guard(a)` blocks) escapes an eigenvariable
    // from the synthetic theorem's citation. These pin the current failure; each
    // flips to a passing check once accelerants emit model-mangled synthetics.
    // (Counters #NN/$NN are stable per-file elaboration-order IDs.)
    // SCHEMA WELL-FORMEDNESS: a schema theorem's proof body is verified at
    // DECLARATION in strict mode (instantiated at opaque parameters), so a
    // malformed step (here a 4-ref or_elim — the kernel's or_elim is binary) is
    // rejected up front. In --fast the body stays lazy (checked only at real
    // instantiations), so the same file is accepted. See agents/GUIDE.md.
    ctx.fail(&.{ "check", "tests/cases/schema_wellformed_bad.bpa" }, "tests/cases/schema_wellformed_bad.bpa:81:13: error: 'or_elim' expects 3 reference(s), got 4\n");
    ctx.ok(&.{ "check", "--fast", "tests/cases/schema_wellformed_bad.bpa" },
        \\OK: 11 declarations, 1 theorems proven
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );
    // the positive counterpart: a WELL-FORMED schema (proper `case` split)
    // passes the strict declaration-time check — the new pass must not reject
    // legitimate schemas.
    ctx.okSilent(&.{ "check", "tests/cases/schema_wellformed_ok.bpa" });

    // ACCELERANT-SYNTHETIC transfer through a GUARDED model: the accelerant emits a
    // CONTEXT-FREE synthetic theorem in source space; the guarded materializer now
    // re-emits its citation cluster GUARD-BLIND (matching the unguarded synthetic)
    // and, when the whole proof is one such cluster concluding a carrier universal,
    // weakens that conclusion to the relativized statement. All seven transfer GREEN.
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_simplify.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_assoc.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_assoc_commut.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_tautology.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_polynomial.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_arithmetic.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_extensionality.bpa" });

    // PREDICATED SORT `sort H = G where inH` — binder positions: ∀/∃
    // inject the guard (implies/and), `fix h: H` carries it on the block (surfaced
    // by `[by predicate <lbl>]`, made the forall_intro antecedent), `unpack h: H`
    // gets it from the ∃'s conjunct. Pure sugar over the carrier; kernel-checked.
    ctx.okSilent(&.{ "check", "tests/cases/predicated_sort_binders.bpa" });
    // PREDICATED SORT — func RESULT closure: `func op2(a: H, b: H): H`
    // surfaces `inH(op2(x,y))` at each use, so `f(op2(h,h))` composes (the
    // subgroup-closure pattern). Gated by the arg-obligations; equivalent to an
    // explicit closure axiom. Kernel-checked.
    ctx.okSilent(&.{ "check", "tests/cases/predicated_sort_closure.bpa" });
    // PREDICATED SORT chain: C = B where inC over B = A where inB — carrierOf walks
    // to the root A, qualifiers accumulate, so ∀c: C desugars to
    // ∀c: A; inB(c) -> inC(c) -> …. (Also a Zig unit test in env.zig.)
    ctx.okSilent(&.{ "check", "tests/cases/predicated_sort_chain.bpa" });

    // SOUNDNESS: even under --fast, the remapped source theorem must α-match the
    // goal — a flipped-equation goal is rejected (you can't prove what the source
    // theorem doesn't say).
    ctx.fail(&.{ "check", "--fast", "tests/cases/model_bad.bpa" },
        \\tests/cases/model_bad.bpa:24:9: error: model transfer of 'source.opUnitLeftTwice' does not match the goal:
        \\  transferred: forall a: Thing; combine(ZED, combine(ZED, a)) = combine(ZED, a)
        \\  goal:        forall a: Thing; combine(ZED, a) = combine(ZED, combine(ZED, a))
        \\
    );

    // the polynomial tactic on a thin theory (no ring lemmas): it EMITS the certificate citing
    // the well-known lemmas by name (no produce-time lookup); the generated schema's ProveTask
    // then can't resolve them, failing "reference not found" at the `polynomial` step.
    ctx.fail(&.{ "check", "tests/cases/polynomial_oracle.bpa" }, "tests/cases/polynomial_oracle.bpa:22:12: error: reference not found: 'mulAddDistribRight'\n");

    ctx.ok(&.{ "check", "--fast", "tests/cases/polynomial_oracle.bpa" },
        \\OK: 6 declarations, 1 theorems proven (1 accelerated: polynomial)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // Regression: the lemma-free accelerated tactic normalizer distributes a wide-sum 4th
    // power (256 monomials); building each product reallocates the term pool,
    // which pool.args aliases — the old code read a dangling arg slice and
    // panicked. Must check clean under --fast (never crash).
    ctx.ok(&.{ "check", "--fast", "tests/cases/polynomial_oob.bpa" },
        \\OK: 6 declarations, 1 theorems proven (1 accelerated: polynomial)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // ac on different multisets reports the mismatch (emits kernel steps, not accelerated)
    ctx.fail(&.{ "check", "tests/cases/ac_bad.bpa" }, "tests/cases/ac_bad.bpa:18:17: error: assoc_commut: sides have different summands: 'add(b, add(a, a))' vs 'add(b, a)'\n");

    // assoc_commut(assoc, comm, swap): the explicit-triple form on a CUSTOM
    // operator (emits kernel steps — the triple is kernel-checked).
    ctx.okSilent(&.{ "check", "tests/cases/assoc_commut_custom.bpa" });

    // no partials: 1 or 2 args is an error (either bare or exactly three). (Column 12: the
    // rule word sits after `[using `.)
    ctx.fail(&.{ "check", "tests/cases/assoc_commut_bad_arity.bpa" }, "tests/cases/assoc_commut_bad_arity.bpa:12:12: error: assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got 2\n");

    // the bare assoc_commut form on a thin theory (no AC lemmas): it EMITS the certificate
    // citing the well-known AC triple by name (no produce-time lookup); the generated schema's
    // ProveTask can't resolve them, failing "reference not found" at the `assoc_commut` step.
    // (--fast is SUSPENDED during the demand rebuild — strict-only, so it errors identically.)
    ctx.fail(&.{ "check", "tests/cases/assoc_commut_oracle.bpa" }, "tests/cases/assoc_commut_oracle.bpa:16:12: error: reference not found: 'addIsAssociative'\n");
    ctx.fail(&.{ "check", "--fast", "tests/cases/assoc_commut_oracle.bpa" }, "tests/cases/assoc_commut_oracle.bpa:16:12: error: reference not found: 'addIsAssociative'\n");

    // `assoc(assocLemma)`: associativity-only reorder on a CUSTOM operator
    // (no add/mul assumption). Emits kernel steps.
    ctx.okSilent(&.{ "check", "tests/cases/assoc.bpa" });

    // sides differ by more than associativity (operands permuted) → error
    ctx.fail(&.{ "check", "tests/cases/assoc_bad.bpa" }, "tests/cases/assoc_bad.bpa:11:12: error: assoc: sides differ by more than associativity: 'op(a, b)' vs 'op(b, a)'\n");

    // the required-arg contract: bare `assoc` is an error
    ctx.fail(&.{ "check", "tests/cases/assoc_missing_arg.bpa" }, "tests/cases/assoc_missing_arg.bpa:10:12: error: assoc requires an associativity lemma: assoc(<assocLemma>); got 0 argument(s)\n");

    // the assoc tactic certifies by default. (The --fast accelerated verdict is SUSPENDED —
    // strict-only during the rebuild — so --fast just re-certifies, no acceleration banner.)
    ctx.okSilent(&.{ "check", "tests/cases/assoc_oracle.bpa" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/assoc_oracle.bpa" });

    // simplify_quantified: peel forall over an equation, emits kernel steps
    ctx.okSilent(&.{ "check", "tests/cases/simplify_quantified.bpa" });

    // simplify_quantified on a bare equation redirects to simplify
    ctx.fail(&.{ "check", "tests/cases/simplify_quantified_bad.bpa" }, "tests/cases/simplify_quantified_bad.bpa:12:12: error: simplify_quantified expects a quantified goal; did you mean simplify?\n");

    // plain simplify on a quantified goal redirects to simplify_quantified
    ctx.fail(&.{ "check", "tests/cases/simplify_on_quantified.bpa" }, "tests/cases/simplify_on_quantified.bpa:12:12: error: simplify proves equations; did you mean simplify_quantified?\n");

    // symmetry: y = x from x = y in one step, emits kernel steps
    ctx.okSilent(&.{ "check", "tests/cases/symmetry.bpa" });

    // Milestone B2: tautology emits certificates — kernel-checked steps,
    // emits kernel steps, not accelerated (the accelerated path remains as the over-budget fallback)
    ctx.okSilent(&.{ "check", "tests/cases/tautology.bpa" });

    // certificates check with every step kernel-checked by default (no accelerated tactic)
    ctx.okSilent(&.{ "check", "tests/cases/tautology.bpa" });

    // non-consequence: the diagnostic carries the countermodel
    ctx.fail(&.{ "check", "tests/cases/tautology_bad.bpa" }, "tests/cases/tautology_bad.bpa:10:12: error: tautology: not a propositional consequence; countermodel: p := true, q := false\n");

    // the atom cap is a hard, honest limit
    ctx.fail(&.{ "check", "tests/cases/tautology_cap.bpa" }, "tests/cases/tautology_cap.bpa:25:12: error: tautology: 17 distinct atoms exceeds the limit of 16\n");

    // `iff` surface sugar: `P iff Q` desugars to `(P -> Q) and (Q -> P)` (never
    // reaches the kernel). iff_intro/iff_elim_forward/iff_elim_backward are thin
    // renames of the `and` rules; crucially `tautology` DECIDES iff goals and
    // CONSUMES iff hypotheses for free (it sees the desugared conjunction) — the
    // property the set/collection membership-axiom corpus relies on.
    ctx.okSilent(&.{ "check", "tests/cases/iff.bpa" });

    // SOUNDNESS negative: an iff must not license an unrelated conclusion —
    // tautology rejects `A iff B, A ⊢ C` with a countermodel that respects the iff.
    ctx.fail(&.{ "check", "tests/cases/iff_bad.bpa" }, "tests/cases/iff_bad.bpa:19:25: error: tautology: not a propositional consequence; countermodel: A := true, B := true, C := false\n");

    // GUARD: the biconditional shape `(X -> Y) and (Y -> X)` is canonically an
    // iff — `and_intro` is forbidden from producing it (must use `iff_intro`)…
    ctx.fail(&.{ "check", "tests/cases/iff_and_intro_bad.bpa" }, "tests/cases/iff_and_intro_bad.bpa:15:43: error: this goal is a biconditional '(X -> Y) and (Y -> X)' — use `iff_intro` (which is the same rule, named for what it proves)\n");

    // …and conversely `iff_intro` requires that shape — a plain conjunction is rejected.
    ctx.fail(&.{ "check", "tests/cases/iff_intro_bad.bpa" }, "tests/cases/iff_intro_bad.bpa:14:29: error: iff_intro's goal must be a biconditional (from `P iff Q`); this goal is not of the form '(X -> Y) and (Y -> X)' — did you mean `and_intro`?\n");

    // `iff_rewrite`: the propositional analogue of `=`-rewrite. From `P iff Q`,
    // replace the sub-proposition P by Q at any position (subformula congruence,
    // under connectives AND quantifiers), reusing the `=`-rewrite walker. A
    // kernel-checked rule (no --fast taint), sound because iff is a congruence.
    ctx.okSilent(&.{ "check", "tests/cases/iff_rewrite.bpa" });

    // it is SOUND: the claim must be reachable by replacing P with Q (or Q with P
    // — iff_rewrite is bidirectional) — an unrelated claim is rejected in BOTH.
    ctx.fail(&.{ "check", "tests/cases/iff_rewrite_bad.bpa" }, "tests/cases/iff_rewrite_bad.bpa:17:12: error: iff_rewrite cannot derive 'R' from 'P' using '(P -> Q) and (Q -> P)' (tried both orientations)\n");

    // …and its first argument must be a biconditional, not a plain implication.
    ctx.fail(&.{ "check", "tests/cases/iff_rewrite_notbicond.bpa" }, "tests/cases/iff_rewrite_notbicond.bpa:14:26: error: iff_rewrite expects a biconditional '(P -> Q) and (Q -> P)', got 'P -> Q'\n");

    // BIDIRECTIONAL rewrite: an equation / biconditional cited in the "wrong"
    // orientation for the goal still rewrites — no preceding `symmetry` needed.
    // The kernel tries lhs->rhs then rhs->lhs (sound: equality/iff are symmetric).
    ctx.okSilent(&.{ "check", "tests/cases/rewrite_reverse.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/iff_rewrite_reverse.bpa" });
    // …but a claim reachable in NEITHER orientation is still rejected (the change
    // is a superset of acceptance, not a hole).
    ctx.fail(&.{ "check", "tests/cases/rewrite_bad.bpa" }, "tests/cases/rewrite_bad.bpa:23:4: error: rewrite cannot derive 'B = D' from 'A = C' using 'A = B' (tried both orientations)\n");

    // Milestone C: arithmetic accelerated tactic — Presburger quantifier elimination
    ctx.ok(&.{ "check", "--fast", "tests/cases/arithmetic.bpa" },
        \\OK: 10 declarations, 4 theorems proven (4 accelerated: arithmetic)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // pure-ℤ: the engine ranges over all integers (no implicit nonnegativity)
    // and recognizes neg/sub/prev, so ℤ linear identities — including sub/neg
    // cancellations outside a ℕ fragment — decide. (--fast gate: the bare
    // fixture has no ring lemmas in scope to certify with; strict certification
    // is exercised over the real integer theory in the std corpus.)
    ctx.ok(&.{ "check", "--fast", "tests/cases/arithmetic_integer.bpa" },
        \\OK: 17 declarations, 8 theorems proven (8 accelerated: arithmetic)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // false statement: the diagnostic carries countermodel values
    ctx.fail(&.{ "check", "tests/cases/arithmetic_bad.bpa" }, "tests/cases/arithmetic_bad.bpa:17:17: error: arithmetic: false at a := 0, b := 0\n");

    // a relation opaque only because it hides a nonlinear term is
    // reported honestly as outside the fragment, not as a false countermodel
    ctx.fail(&.{ "check", "tests/cases/arithmetic_frag.bpa" }, "tests/cases/arithmetic_frag.bpa:15:9: error: arithmetic: 'mul(a, b)' is outside linear arithmetic\n");

    // Milestone D: the SMT combination — mixed goals, one accelerated-tactic name
    ctx.ok(&.{ "check", "--fast", "tests/cases/smt.bpa" },
        \\OK: 9 declarations, 2 theorems proven (2 accelerated: arithmetic)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // Milestone C2b: universal linear goals replay as kernel-checked certificates
    // (sorted-sum normalization + synthesized order witnesses)
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert2.bpa" });

    // Farkas: difference-logic infeasibility (combine several order
    // hypotheses into a transitivity cycle) certifies purely under the
    // DEFAULT, via `arithmetic(<theory>)` resolving the order lemmas
    // against the named module — no local aliasing of the vocabulary.
    ctx.okSilent(&.{ "check", "tests/cases/farkas.bpa" });

    // Farkas extensions: order composition (a<b -> b<c -> a<c, no cycle)
    // and the infeasibility cap (contradictory order hyps prove an
    // arbitrary conclusion via lessThanIrreflexive + absurd).
    ctx.okSilent(&.{ "check", "tests/cases/farkas_ext.bpa" });

    // Farkas coefficient scaling: a hypothesis scaled by a literal
    // via multiplicationPreservesOrder before the infeasibility fold.
    ctx.okSilent(&.{ "check", "tests/cases/farkas_scale.bpa" });

    // Farkas sum path: sum two order hypotheses over distinct
    // variables via additionPreservesOrder + commutativity + transitivity.
    ctx.okSilent(&.{ "check", "tests/cases/farkas_sum.bpa" });

    // Milestone C2a: ground goals replay as kernel-checked simplify certificates
    // over the well-known peano axioms — the default check accepts them
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert.bpa" });

    // additive-inverse cancellation across a separated summand: `add(a, sub(b,a))
    // = b` normalizes to a {a, b, neg(a)} multiset that reduces to {b} — the
    // equation certifier must cancel a with neg(a) (a `neg`-leaf tower).
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert_neg_cancel.bpa" });

    // numeral summand: `add(ONE, sub(b, ONE)) = b` — the ONE / neg(ONE) inverse
    // pair must cancel even though ONE is a `succ(ZERO)` tower sitting as an inner
    // summand (not the top-level succ prefix). parseTower folds the numeral into
    // the tower's constant offset so the pair meets and cancels.
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert_numeral_leaf.bpa" });

    // diagnostic: the SAME goal with `addLeftSwap` omitted from scope must report
    // the specific missing rewrite lemma ("theory lacks lemma 'addLeftSwap'"), not
    // the generic "form not in certification scope" (which reads as "wrong shape"
    // and hides the one-alias fix). Guards the equation certifier's decline reason.
    ctx.fail(
        &.{ "check", "tests/cases/arithmetic_missing_lemma_diagnostic.bpa" },
        "tests/cases/arithmetic_missing_lemma_diagnostic.bpa:37:17: error: 'arithmetic' is valid but no certifier could prove it here:\n" ++
            "  - equation/order/exists: theory lacks lemma 'addLeftSwap'\n" ++
            "  - mixed-skeleton: form not in certification scope\n" ++
            "  - farkas: theory lacks symbol 'less_than'\n" ++
            "  - cooper: form not in certification scope\n" ++
            "use --fast to accept the accelerated verdict\n",
    );

    // opaque compound leaves: `add(f(x), sub(g(y), f(x))) = g(y)` — foreign
    // apps f(x)/g(y) ride the sorted-tower join as atoms and the f(x)/neg(f(x))
    // pair cancels (bubbled to the tail so addNeg matches an innermost subterm).
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert_opaque_leaf.bpa" });

    // Cooper-replay layer 2 (witness direction): a `forall x; exists y; …`
    // goal with a period-1 Cooper trace elaborates fully — the cooper link
    // picks a boundary witness and emits exists_intro over an or-intro arm.
    ctx.okSilent(&.{ "check", "tests/cases/cooper_witness.bpa" });

    // Cooper-replay layer 3 (periodicity direction): a period-2 (parity) ∀∃
    // goal elaborates fully via a SYNTHESIZED induction — the cooper link builds
    // predicate P(k), proves base P(ZERO) and step P(k)->P(succ(k)) (unpacking
    // the IH witness and shifting it per parity arm), then instantiates the
    // `induction` schema. This is `evenOrOdd` (add-form), fully accelerated-free.
    ctx.okSilent(&.{ "check", "tests/cases/cooper_parity.bpa" });

    // The cooper link's DECLARED BOUNDARY: a multi-fixed-variable ∀∀∃
    // (`forall a, b; exists c; …`) is decided valid by Presburger but declines
    // — cooperInduction synthesizes an induction on a SINGLE variable. Without
    // a fallback, default mode is a hard error listing every link's decline
    // (the "solvable by arithmetic, not yet certifiable" gap)...
    ctx.fail(&.{ "check", "tests/cases/cooper_gap_raw.bpa" },
        \\tests/cases/cooper_gap_raw.bpa:25:9: error: 'arithmetic' is valid but no certifier could prove it here:
        \\  - equation/order/exists: form not in certification scope
        \\  - mixed-skeleton: form not in certification scope
        \\  - farkas: theory lacks symbol 'less_than'
        \\  - cooper: form not in certification scope
        \\use --fast to accept the accelerated verdict
        \\
    );
    // ...and --fast accepts the accelerated verdict, marking the theorem accelerated.
    ctx.ok(&.{ "check", "--fast", "tests/cases/cooper_gap_raw.bpa" },
        \\OK: 15 declarations, 1 theorems proven (1 accelerated: arithmetic)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );
    // ...and `[using arithmetic fallback(<thm>)]` closes the gap fully proven in default
    // mode: the chain declines, so the cited manual theorem (which reduces the
    // ∀∀∃ to the cooper-certified single-variable evenOrOddArith) stands as the
    // certificate — no --fast, no acceleration.
    ctx.okSilent(&.{ "check", "tests/cases/cooper_gap.bpa" });

    // negative ℤ witness: `exists y; x = succ(y)` certifies STRICT with y = prev(x)
    // (built as a prev-tower, discharged via succPrev) — a witness the ℕ-only
    // succ-tower builder could not construct.
    ctx.okSilent(&.{ "check", "tests/cases/cooper_negative_witness.bpa" });

    // Case D: a `fallback(<thm>)` on a goal the arithmetic CERTIFIER CHAIN can
    // discharge itself is REDUNDANT — strict `check` rejects it. (Distinct from
    // cooper_gap, where the certifier DECLINES so the fallback is legitimate.)
    ctx.fail(&.{ "check", "tests/cases/arithmetic_fallback_redundant_bad.bpa" }, "tests/cases/arithmetic_fallback_redundant_bad.bpa:31:29: error: 'arithmetic' certifies this goal on its own — the fallback 'twoTimesTwoManual' is unnecessary; drop `fallback(twoTimesTwoManual)`\n");
    // `--fast` suppresses it structurally (the certifier chain never runs).
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/arithmetic_fallback_redundant_bad.bpa" });
    // `--draft` suppresses it (WIP: don't nag about redundant fallbacks yet).
    ctx.okSilent(&.{ "check", "--draft", "tests/cases/arithmetic_fallback_redundant_bad.bpa" });

    // a `fallback(<axiom-or-hole>)` is accepted (not only theorems): the goal has
    // an opaque subterm the certifier can't discharge, so the arithmetic step
    // falls back to a `hole` (an axiom-kind statement). The proof rests on the
    // hole → rejected strict, accepted under --draft with the hole disclosed.
    ctx.okSilent(&.{ "check", "--draft", "tests/cases/arithmetic_fallback_axiom.bpa" });

    // a `fallback(<forall-theorem>)` on a SPECIALIZED goal (an instance of the
    // theorem, not alpha-equal): the matcher peels the ∀ prefix (inferring the
    // witnesses by matching the conclusion against the goal) and discharges any
    // leading `->` antecedents from the step's refs, emitting a kernel-certified
    // forall_elim+modus_ponens chain. Verifies STRICT (the fallback targets are
    // axiom-proven, no holes) — so the emitted specialization really re-checks.
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_fallback_specialize.bpa" });

    // linear-equation-combination certifier: an equation goal that follows by
    // CANCELLING an equality PREMISE (sub(a,r) = mul(b,q) from the premise
    // add(mul(b,q),r) = a) over opaque leaves. The rewrite-normalizer can't fire
    // the premise as a rewrite, but the goal is a linear combination of it: the
    // certifier proves the identity add(P_l,G_l)=add(P_r,G_r), rewrites the
    // premise, and cancels — a kernel-checked chain. Verifies STRICT.
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_linear_equation_premise.bpa" });

    // arithmetic × SCHEMA: Case D fires from inside a schema body too — the
    // declaration-time wellformedness self-check (instantiate at opaque params,
    // run the proof) exercises arithmeticJustification, so a redundant `fallback`
    // in a schema's proof is rejected. `--fast`/`--draft` suppress it as usual.
    ctx.fail(&.{ "check", "tests/cases/schema_arithmetic_fallback_bad.bpa" }, "tests/cases/schema_arithmetic_fallback_bad.bpa:30:29: error: 'arithmetic' certifies this goal on its own — the fallback 'twoTwo' is unnecessary; drop `fallback(twoTwo)`\n");
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/schema_arithmetic_fallback_bad.bpa" });
    ctx.okSilent(&.{ "check", "--draft", "tests/cases/schema_arithmetic_fallback_bad.bpa" });

    // arithmetic over a reified SCHEMA PARAMETER: the schema's opaque
    // wellformedness self-check reifies the value-param `k` as an opaque symbol
    // arithmetic can't treat as a Nat variable — a known, planned-but-unsupported
    // case. The message names the user's parameter (not the internal symbol) and
    // says it's unsupported-but-planned. (`--fast` skips the self-check, so it
    // wouldn't hit this — not gated here.)
    ctx.fail(&.{ "check", "tests/cases/schema_arithmetic_param_bad.bpa" }, "tests/cases/schema_arithmetic_param_bad.bpa:20:9: error: arithmetic cannot yet decide this goal over the schema parameter 'k' (reified opaque while the schema's proof is checked). Certifying an arithmetic step over a schema parameter is currently unsupported but planned; use --fast to accept the accelerated verdict\n");

    // Milestone D2: mixed skeletons replay as kernel-checked certificates
    ctx.okSilent(&.{ "check", "tests/cases/smt_cert.bpa" });

    // mixed countermodel: arithmetic values plus opaque truth values
    ctx.fail(&.{ "check", "tests/cases/smt_bad.bpa" }, "tests/cases/smt_bad.bpa:12:9: error: arithmetic: false at a := 0, p := false\n");

    // instantiating strongInduction re-checks its full stored proof
    ctx.okSilent(&.{ "check", "tests/cases/strong_induction.bpa" });
}
