//! Integration gates — the automation tactics and their fixtures: simplify, ac / assoc / distribute, polynomial, tautology, arithmetic / Presburger, Farkas, and their `_bad` diagnostics.
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
    // `by cite`: the KIND-AGNOSTIC fact citation (cites an axiom OR a theorem; the kernel
    // picks its arm by the resolved kind). The word generated accelerant certs emit.
    ctx.okSilent(&.{ "check", "tests/cases/cite.b4m" });

    // Milestone A: simplify — certificate-producing rewrite tactic
    ctx.okSilent(&.{ "check", "tests/cases/simplify.b4m" });

    // simplify always emits kernel steps (never accelerates): the default check accepts it
    ctx.okSilent(&.{ "check", "tests/cases/simplify.b4m" });

    // unjoinable normal forms: the diagnostic shows both, copy-pasteable
    ctx.fail(&.{ "check", "tests/cases/simplify_bad.b4m" }, "tests/cases/simplify_bad.b4m:14:16: error: simplify: normal forms differ: 'add(n, ZERO)' vs 'n'\n");

    // cycling rules hit the hard rewrite cap instead of hanging
    ctx.fail(&.{ "check", "tests/cases/simplify_loop.b4m" }, "tests/cases/simplify_loop.b4m:13:12: error: simplify: rewrite limit reached (looping rule set?)\n");

    // ac: associative-commutative sum reordering over opaque atoms, emits kernel steps
    ctx.okSilent(&.{ "check", "tests/cases/ac.b4m" });

    // ac over multiplication: same bubble-sort machinery, mul lemma triple
    // (mulIsAssociative/mulIsCommutative/mulLeftSwap), emits kernel steps
    ctx.okSilent(&.{ "check", "tests/cases/ac_mul.b4m" });

    // ac_quantified: peel the forall prefix then run the ac core (add + mul)
    ctx.okSilent(&.{ "check", "tests/cases/ac_quantified.b4m" });

    // distributivity: ac_quantified with a cited distributivity lemma
    // pre-normalizes (distributes) each side before the AC bubble-sort
    ctx.okSilent(&.{ "check", "tests/cases/distribute.b4m" });

    // `polynomial(theory)`: nonlinear identities canonicalize, emitting kernel
    // steps (no accelerated tactic) via distribute → sort monomials → sort sum → fold.
    ctx.okSilent(&.{ "check", "tests/cases/polynomial.b4m" });

    // sides with different expansions → located error, exit 1 (not accelerated)
    ctx.fail(&.{ "check", "tests/cases/polynomial_bad.b4m" }, "tests/cases/polynomial_bad.b4m:18:12: error: polynomial: sides expand differently: 'add(mul(a, a), add(mul(a, b), add(mul(a, b), mul(b, b))))' vs 'add(mul(a, a), mul(b, b))'\n");

    // `polynomial` expands sub/neg (definitionOfSubtraction + neg-folds push neg
    // to the leaves), cancels additive inverses (t + neg(t) → 0), and folds
    // numeral coefficients (q+q → 2·q, 2q+2q → 4q) — strict cert + --fast parity.
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_neg.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_inverse.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_coeff.b4m" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_neg.b4m" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_inverse.b4m" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_coeff.b4m" });
    // a ring identity in ONE operator is still a polynomial identity: an ADD-ONLY goal
    // (neg-push, regroup, cancellation to ZERO — no mul anywhere) and a MUL-ONLY goal (a
    // single monomial: neg-push through mul, regroup — no add anywhere). The op reader must
    // not demand both operators be present; the rules/phases needing the absent one are
    // simply not applicable.
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_add_only.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_mul_only.b4m" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_add_only.b4m" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_mul_only.b4m" });
    // a CROSS-TERM inverse pair (`a·b + neg(b·a)`) cancels: the monomial inside `neg(…)` is
    // factor-sorted like any other (its sort trace lifted through the neg context).
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_cross_term.b4m" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_cross_term.b4m" });

    // a cited premise the CERTIFIER never uses (its rewrite rule never fires) must not become
    // a schema antecedent: the generated schema would carry a restated hypothesis nothing
    // cites, tripping its own use-all-facts pass ("unused fact: step 'prem-N'"). The producer
    // drops it from the antecedents AND from the call-site discharge list, in lockstep.
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_unused_premise.b4m" });
    // the additive canonicalizer sorts + inverse-cancels UNDER a succ tower (premise combination).
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_sub_from_add.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/simplify_unused_premise.b4m" });

    // a schema instantiated at a lambda CAPTURING an enclosing `fix b`: the schema's own
    // accelerant steps then run over a body mentioning a free `b` belonging to the
    // INSTANTIATING file. Every accelerant that abstracts free fvars must carry the
    // caller-scope binding (Synthetic.fvar_binds — only `specialize` did), or the
    // re-elaborated synthetic fails "unknown identifier 'b'" against the schema's file.
    ctx.okSilent(&.{ "check", "tests/cases/schema_inherited_fvar.b4m" });

    // polynomial(field): the accelerant over a FIELD theory (bare ONE constant,
    // not the ℤ succ-tower). Guards field.b4m's ring-lemma shims + swaps resolving
    // by bare name in field's scope, and the additive-inverse cancellation of the
    // bare ONE atom (ONE + neg(ONE) → 0). Strict cert + --fast parity.
    ctx.okSilent(&.{ "check", "tests/cases/polynomial_field.b4m" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/polynomial_field.b4m" });
    // a wrong coefficient (q+q claimed = 3·q) is still rejected: q+q expands to
    // add(q, q), 3·q to add(q, add(q, q)) — real repeated-addition arithmetic.
    ctx.fail(&.{ "check", "tests/cases/polynomial_coeff_bad.b4m" }, "tests/cases/polynomial_coeff_bad.b4m:15:12: error: polynomial: sides expand differently: 'add(q, q)' vs 'add(q, add(q, q))'\n");

    // `ext(theory)`: the extensionality tactic, one tactic over two models —
    // reduce an equation to its pointwise obligation via the theory's
    // extensionality lemma, unfold the operators, close the residue. SET model
    // (propositional residue → tautology); emits kernel steps.
    ctx.okSilent(&.{ "check", "tests/cases/extensionality_set.b4m" });
    // FUNCTION model (equational residue → rewrite join) — same `ext` tactic.
    ctx.okSilent(&.{ "check", "tests/cases/extensionality_function.b4m" });
    // a FALSE set identity: the pointwise residue has a countermodel, so ext
    // declines with a located error (exit 1) — never accepts a false equation.
    ctx.fail(&.{ "check", "tests/cases/extensionality_bad.b4m" }, "tests/cases/extensionality_bad.b4m:18:12: error: extensionality: could not close the pointwise obligation propositionally (is the identity true?)\n");

    // `model`: structure reuse. The source theory (a carrier + op + left-unit +
    // one proven theorem) is modeled by a concrete sort, and its theorem
    // transfers, remapped through the model.
    ctx.okSilent(&.{ "check", "tests/cases/model_source.b4m" });

    // --fast trusts the transfer wholesale (remap the source theorem, α-match the
    // goal, taint accelerated: model) — checks nothing about the source proof.
    ctx.ok(&.{ "check", "--fast", "tests/cases/model_transfer.b4m" },
        \\OK: 14 declarations, 1 theorems proven
        \\  — NOT FULLY VERIFIED: 1 theorem(s) accelerated (admitted, not proved): model
        \\
    );
    // default (strict) MATERIALIZES the remapped source proof as a synthetic
    // kernel-checked theorem (suppressed from the count) and cites it — so it
    // passes with NO taint. The transfer is genuinely kernel-verified.
    ctx.okSilent(&.{ "check", "tests/cases/model_transfer.b4m" });

    // DEPENDENCY WALK: transferring a source theorem whose proof cites ANOTHER
    // source theorem forces strict materialization to recurse into it (memoized —
    // the shared dependency materializes once across both cites). Kernel-checked.
    ctx.okSilent(&.{ "check", "tests/cases/model_recurse.b4m" });
    // `--fast-only model` ADMITS the transfer (its statement α-matches the claim; the source
    // proof is NOT re-materialized), disclosed via the NOT-FULLY-VERIFIED banner. Scoped to
    // `model` so the banner lists just that word.
    ctx.ok(&.{ "check", "--fast-only", "model", "tests/cases/model_recurse.b4m" },
        \\OK: 15 declarations, 2 theorems proven
        \\  — NOT FULLY VERIFIED: 2 theorem(s) accelerated (admitted, not proved): model
        \\
    );

    // MATERIALIZATION CITATION RULE: a materialized model proof may cite another
    // materialized theorem; a substitution-INVARIANT theorem/axiom (as-is, walk
    // ends); or a substituted axiom mapped (to a theorem OR an axiom). It may NOT
    // cite a fact the substitution AFFECTS but the model doesn't map.
    // OK exercises invariant-theorem + invariant-axiom + axiom→theorem + axiom→axiom:
    ctx.okSilent(&.{ "check", "tests/cases/model_cite_ok.b4m" });
    // BAD leaves an affected axiom (opUnitRight, cited by the transferred proof) unmapped →
    // rejected. In the demand path an unmapped source axiom stays the SOURCE axiom under the
    // transfer (applyModel = identity), so its formula fails to match the transferred step's
    // relativized claim — the rejection surfaces at that source citation.
    ctx.fail(&.{ "check", "tests/cases/model_cite_bad.b4m" }, "tests/cases/model_cite_source.b4m:43:8: error: ThingModel@unitCollapsesAndMarks: step claims 'forall b: Thing; combine(b, NEUTRAL) = b' but the axiom derives 'forall a: Sort; op(a, UNIT) = a'\n");
    // a model maps only the source theory's AXIOMS; mapping a source THEOREM (which
    // materializes through the mapped axioms) is misuse and rejected at that mapping.
    ctx.fail(&.{ "check", "tests/cases/model_maps_theorem_bad.b4m" }, "tests/cases/model_maps_theorem_bad.b4m:22:3: error: model maps only axioms; 'src.leftUnit' is a theorem — it materializes through the mapped axioms, so drop this mapping\n");

    // a transparent (`define`d) symbol cannot be a model mapping source/target — it
    // rides along on the primitives in its body (which the model maps); nominally
    // remapping its NAME would ignore the definition (definition-blind, unsound).
    ctx.fail(&.{ "check", "tests/cases/model_define_source_bad.b4m" }, "tests/cases/model_define_source_bad.b4m:19:3: error: 'source.TWICE' is a transparent (`define`d) symbol — it rides along on the primitives in its body and cannot be a model mapping source; map those primitives instead\n");

    // …but a define'd TARGET is legitimate: mapping a source symbol ONTO a defined
    // target EXPRESSION works — the target expands to its body during transfer, so
    // `source.UNIT: DOUBLED` yields combine(ZED, ZED) in the materialized theorem.
    ctx.okSilent(&.{ "check", "tests/cases/model_define_target.b4m" });

    // GUARDED model (`model … where <pred>`): the transfer is RELATIVIZED — every
    // carrier ∀ gains `guard(x) ->` — and strict materialization discharges the
    // guard obligation at each forall_elim over a guarded universal (recursing on
    // the instantiation term: constant → base closure fact; eigenvariable → the
    // in-scope `assume guard(a)`; composite → a closure fact + recursion). Fully
    // kernel-checked, no taint.
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_source.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded.b4m" });
    // clean-error boundary: a guarded transfer whose proof instantiates at a term
    // with no closure fact in scope fails with an actionable message (the graceful
    // fallback point for future author-supplied obligations).
    // (demand path: no discharger nominated for good(ZED), so the transferred proof's
    // forall_elim(ZED) leaks the guard and the step fails to match its claim — a sound rejection.)
    ctx.fail(&.{ "check", "tests/cases/model_guarded_noclose.b4m" }, "tests/cases/model_guarded_source.b4m:20:4: error: ThingModel@opUnitAtUnit: step claims 'combine(ZED, ZED) = ZED' but forall_elim derives 'good(ZED) -> combine(ZED, ZED) = ZED'\n");
    // BOUNDARY fixtures (all now handled): a guarded transfer of a proof that
    // unpacks an existential witness surfaces `guard(w)` from the relativized
    // `∃x; guard(x) and P(x)` conjunct (and re-guards a matching `exists_intro`);
    // a case split re-emits or_elim + arm hypotheses. (Sources check fine too.)
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_witness_source.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_witness.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_case_source.b4m" });
    // case split (or_elim + hypothesis) now materializes guardedly.
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_case.b4m" });
    // SAME-FILE guarded model: the source theory and the model share one file (the
    // paradigm subgroup case — H ⊆ G on one carrier). Mapping sources are bare
    // (unqualified) names resolved locally; no import/two-file split required.
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_samefile.b4m" });
    // AUTO-WEAKENING: a source axiom that holds unconditionally on the carrier,
    // mapped to ITSELF, has its relativized obligation (`inH(a) -> P(a)`)
    // synthesized by the materializer as a free weakening — no hand-written
    // relativized copy. (∀a;P(a) ⊢ ∀a; guard(a)->P(a).)
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_weaken_source.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_weaken.b4m" });
    // MULTI-BINDER auto-weakening: an unconditional axiom over N carrier binders
    // (here 2), mapped to itself, weakened by nested fix/assume with one chained
    // forall_elim at the core. Needed for group axioms like opAssoc (3 binders).
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_weaken_multi_source.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_weaken_multi.b4m" });
    // the paradigm case end to end: a SUBGROUP modeling its own group's carrier —
    // same-file guarded model + auto-weakening (opIdentityLeft mapped to itself) +
    // inH(E) proved by contradiction from the definitional subgroup axioms.
    ctx.okSilent(&.{ "check", "tests/cases/model_guarded_subgroup.b4m" });
    // THE MODEL STACK end to end over std/group + std/subgroup:
    //  - a subgroup inH of a group; the 8-theorem group corpus transfers onto H
    //    through HSubGroup→HGroup (each `group.X` discharged via a `@`-projection
    //    mapping value `HSubGroup@subgroup.X`).
    //  - K < H < G: a subgroup inK OF the subgroup H; the same stack (KSubGroup→
    //    KGroup) transfers three group theorems onto the sub-subgroup K. Composes
    //    on existing machinery (flattened single-guard K = Grp where inK, inK ⊆ inH).
    // Exercises the DIRECT-MAPPED-axiom transfer (group.opAssoc, an axiom, discharged
    // through a `@`-projection → cite the mapped discharge, not materialize a proof).
    ctx.okSilent(&.{ "check", "tests/cases/model_subgroup_transfer.b4m" });
    // A MODEL IS AN OVERLAY OVER THE WHOLE UNIVERSE, not scoped to one file (user ruling
    // 2026-09-26): the block names entities from THREE namespaces (top's, mid's and base's
    // aliases — the same entities by origin), and transferring top.unitFourth remaps the
    // BORROWED theorems down a two-hop alias chain (top.unitThrice → mid, whose proof cites
    // mid.unitTwice → base): each alias binds, under the model, to the transferred copy
    // keyed on the ORIGIN file, re-proved there. Regression: an alias used to bind to the
    // universe origin, handing the transferred proof base's untransferred `op(U, U) = U`
    // against a target-sort claim (found modeling std/group/sequence onto Perm).
    ctx.okSilent(&.{ "check", "tests/cases/model_alias_borrowed.b4m" });
    // ... and the overlay's COMPLETENESS condition: a model that maps the symbols but leaves
    // base's axiom undischarged is REJECTED when the transfer reaches it two hops down —
    // the unmapped axiom stays in source terms and fails to match the relativized claim.
    ctx.fail(&.{ "check", "tests/cases/model_alias_borrowed_bad.b4m" }, "tests/cases/model_alias_borrowed_base.b4m:9:4: error: Incomplete@unitTwice: step claims 'forall a: T; add(Z, a) = a' but the axiom derives 'forall a: S; op(U, a) = a'\n");

    // SCHEMA TRANSFER through a guarded model: a source induction SCHEMA (elemInduction) is
    // discharged by a local guard-relativized schema (goodInduction); a local schema cites it
    // `[using model(...) source.elemInduction]`, and INSTANTIATING that schema makes the step
    // the discharging schema's instance at the same argument (kernel-checked against the
    // claim). A transferred schema is an instantiation in disguise, so it stays strict under
    // `--fast model` (the summary reports no trusted word used).
    ctx.okSilent(&.{ "check", "tests/cases/model_schema_source.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_schema.b4m" });
    ctx.ok(&.{ "check", "--fast-only", "model", "tests/cases/model_schema.b4m" },
        \\OK: 14 declarations, 2 theorems proven
        \\  — (--fast set given, but no step used a trusted word — fully verified)
        \\
    );
    // RED: the transferring schema claims MORE than the discharging schema's instance gives
    // (the unguarded conclusion) — rejected as a claim/instance mismatch at the transfer step.
    ctx.fail(&.{ "check", "tests/cases/model_schema_claim_bad.b4m" },
        \\tests/cases/model_schema_claim_bad.b4m:42:12: error: the claim does not match the instance's conclusion:
        \\  claim:      good(ZED) -> (forall k: Number; good(k) -> good(k) -> good(next(k))) -> forall n: Number; good(n)
        \\  instance:   good(ZED) -> (forall k: Number; good(k) -> good(k) -> good(next(k))) -> forall n: Number; good(n) -> good(n)
        \\
    );
    // RED: a schema source must be discharged by a SCHEMA (matching predicate
    // parameter); a plain axiom cannot, and the model decl rejects it.
    ctx.fail(&.{ "check", "tests/cases/model_schema_bad.b4m" }, "tests/cases/model_schema_bad.b4m:20:27: error: 'notASchema' discharges a schema, so it must itself be a schema (with a matching predicate parameter)\n");

    // MODEL SYNTAX: `:` interprets a sort/symbol, `<-` discharges an axiom
    // obligation. The happy path uses both; the two rejection paths are hard errors.
    ctx.okSilent(&.{ "check", "tests/cases/model_obligation_arrow.b4m" });
    // `:` on an axiom obligation → error, directing to `<-`.
    ctx.fail(&.{ "check", "tests/cases/model_axiom_colon_bad.b4m" }, "tests/cases/model_axiom_colon_bad.b4m:21:3: error: 'source.opUnitLeft' is an axiom obligation, not a sort/symbol — discharge it with `<-` (`source.opUnitLeft <- <local fact>`), not `:`\n");
    // `<-` on a sort/symbol → error, directing to `:`.
    ctx.fail(&.{ "check", "tests/cases/model_symbol_arrow_bad.b4m" }, "tests/cases/model_symbol_arrow_bad.b4m:19:3: error: 'source.op' is a sort or symbol, not an axiom — map it with `:` (`source.op: <target>`), not `<-`\n");

    // ACCELERANT-THROUGH-GUARDED-MODEL boundary (RED characterization, one per
    // accelerant). Transferring a source theorem whose proof USES an accelerant
    // through a GUARDED model currently fails: the accelerant builds its synthetic
    // theorem at elaboration in the SOURCE space, blind to the model, so guarded
    // re-emission (which inserts `assume guard(a)` blocks) escapes an eigenvariable
    // from the synthetic theorem's citation. These pin the current failure; each
    // flips to a passing check once accelerants emit model-mangled synthetics.
    // (Counters #NN/$NN are stable per-file elaboration-order IDs.)
    // UNINSTANTIATED SCHEMA IS UNCHECKED (#93): this schema's body has a malformed step (a 4-ref
    // or_elim — the kernel's or_elim is binary), but the schema is NEVER instantiated. There is no
    // decl-time check anymore (a schema needn't be a universal; the per-instance proof is the only
    // gate), so the demand engine never checks this dead schema — the file passes. Consistent with
    // "uncited code isn't checked"; a future --library mode would catch it. Both modes pass (no
    // step is admitted → --fast adds only the "no trusted word used" note).
    ctx.ok(&.{ "check", "tests/cases/schema_wellformed_bad.b4m" },
        \\OK: 11 declarations, 1 theorems proven
        \\
    );
    ctx.ok(&.{ "check", "--fast", "tests/cases/schema_wellformed_bad.b4m" },
        \\OK: 11 declarations, 1 theorems proven
        \\  — (--fast set given, but no step used a trusted word — fully verified)
        \\
    );
    // the positive counterpart: a WELL-FORMED schema (proper `case` split)
    // passes the strict declaration-time check — the new pass must not reject
    // legitimate schemas.
    ctx.okSilent(&.{ "check", "tests/cases/schema_wellformed_ok.b4m" });

    // ACCELERANT-SYNTHETIC transfer through a GUARDED model: the accelerant emits a
    // CONTEXT-FREE synthetic theorem in source space; the guarded materializer now
    // re-emits its citation cluster GUARD-BLIND (matching the unguarded synthetic)
    // and, when the whole proof is one such cluster concluding a carrier universal,
    // weakens that conclusion to the relativized statement. All seven transfer GREEN.
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_simplify.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_assoc.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_assoc_commut.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_tautology.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_polynomial.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_arithmetic.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/model_accel_extensionality.b4m" });

    // PREDICATED SORT `sort H = G where inH` — binder positions: ∀/∃
    // inject the guard (implies/and), `fix h: H` carries it on the block (surfaced
    // by `[by predicate <lbl>]`, made the forall_intro antecedent), `unpack h: H`
    // gets it from the ∃'s conjunct. Pure sugar over the carrier; kernel-checked.
    ctx.okSilent(&.{ "check", "tests/cases/predicated_sort_binders.b4m" });
    // PREDICATED SORT — func RESULT closure: `func op2(a: H, b: H): H`
    // surfaces `inH(op2(x,y))` at each use, so `f(op2(h,h))` composes (the
    // subgroup-closure pattern). Gated by the arg-obligations; equivalent to an
    // explicit closure axiom. Kernel-checked.
    ctx.okSilent(&.{ "check", "tests/cases/predicated_sort_closure.b4m" });
    // PREDICATED SORT chain: C = B where inC over B = A where inB — carrierOf walks
    // to the root A, qualifiers accumulate into the CANONICAL conjoined guard, so
    // ∀c: C desugars to ∀c: A; (inC(c) and inB(c)) -> ….
    ctx.okSilent(&.{ "check", "tests/cases/predicated_sort_chain.b4m" });
    // H ∩ K ≤ G (the 13e acceptance stress test): a MULTI-GUARD model — the intersection
    // as `Grp where inH and inK`, base facts via the parens list, per-predicate closures
    // via the `-|` comma list, auto-weakening over the conjoined guard, and composite-
    // witness discharge recursing through BOTH closures to the fix guard's conjuncts.
    ctx.okSilent(&.{ "check", "tests/cases/model_intersection.b4m" });

    // SOUNDNESS: even under --fast, the remapped source theorem must α-match the
    // goal — a flipped-equation goal is rejected (you can't prove what the source
    // theorem doesn't say).
    ctx.fail(&.{ "check", "--fast", "tests/cases/model_bad.b4m" },
        \\tests/cases/model_bad.b4m:24:12: error: the claim does not match the model transfer of 'source.opUnitLeftTwice':
        \\  claim:      forall a: Thing; combine(ZED, a) = combine(ZED, combine(ZED, a))
        \\  transfer:   forall a: Thing; combine(ZED, combine(ZED, a)) = combine(ZED, a)
        \\
    );

    // the polynomial tactic on a thin theory (no ring lemmas): it EMITS the certificate citing
    // the well-known lemmas by name (no produce-time lookup); the generated schema's ProveTask
    // then can't resolve them, failing "reference not found" at the `polynomial` step.
    ctx.fail(&.{ "check", "tests/cases/polynomial_oracle.b4m" }, "tests/cases/polynomial_oracle.b4m:22:12: error: the generated proof of this step cites 'mulAddDistribRight', which is not in scope here; alias it from the theory that states it (`theorem mulAddDistribRight = <module>.mulAddDistribRight`)\n");

    ctx.ok(&.{ "check", "--fast", "tests/cases/polynomial_oracle.b4m" },
        \\OK: 6 declarations, 1 theorems proven
        \\  — NOT FULLY VERIFIED: 1 theorem(s) accelerated (admitted, not proved): polynomial_quantified
        \\
    );

    // Regression: the lemma-free accelerated tactic normalizer distributes a wide-sum 4th
    // power (256 monomials); building each product reallocates the term pool,
    // which pool.args aliases — the old code read a dangling arg slice and
    // panicked. Must check clean under --fast (never crash).
    ctx.ok(&.{ "check", "--fast", "tests/cases/polynomial_oob.b4m" },
        \\OK: 6 declarations, 1 theorems proven
        \\  — NOT FULLY VERIFIED: 1 theorem(s) accelerated (admitted, not proved): polynomial_quantified
        \\
    );

    // ac on different multisets reports the mismatch (emits kernel steps, not accelerated)
    ctx.fail(&.{ "check", "tests/cases/ac_bad.b4m" }, "tests/cases/ac_bad.b4m:18:20: error: assoc_commut: sides have different summands: 'add(b, add(a, a))' vs 'add(b, a)'\n");

    // assoc_commut(assoc, comm, swap): the explicit-triple form on a CUSTOM
    // operator (emits kernel steps — the triple is kernel-checked).
    ctx.okSilent(&.{ "check", "tests/cases/assoc_commut_custom.b4m" });

    // no partials: 1 or 2 args is an error (either bare or exactly three). (Column 12: the
    // rule word sits after `[using `.)
    ctx.fail(&.{ "check", "tests/cases/assoc_commut_bad_arity.b4m" }, "tests/cases/assoc_commut_bad_arity.b4m:12:12: error: assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got 2\n");

    // the bare assoc_commut form on a thin theory (no AC lemmas): it EMITS the certificate
    // citing the well-known AC triple by name (no produce-time lookup); the generated schema's
    // ProveTask can't resolve them, failing "reference not found" at the `assoc_commut` step.
    // (--fast is SUSPENDED during the demand rebuild — strict-only, so it errors identically.)
    ctx.fail(&.{ "check", "tests/cases/assoc_commut_oracle.b4m" }, "tests/cases/assoc_commut_oracle.b4m:16:12: error: the generated proof of this step cites 'addIsAssociative', which is not in scope here; alias it from the theory that states it (`theorem addIsAssociative = <module>.addIsAssociative`)\n");
    // `--fast-only assoc_commut_all` ADMITS the step: `assoc_commut` accepts it on its own fast
    // check and never RESOLVES the cited lemma, so the strict-only "reference not found" is not
    // raised. Trusting the accelerant means accepting its steps unproved — the missing lemma
    // surfaces only in a strict run. Disclosed via the banner.
    ctx.ok(&.{ "check", "--fast-only", "assoc_commut_all", "tests/cases/assoc_commut_oracle.b4m" },
        \\OK: 4 declarations, 1 theorems proven
        \\  — NOT FULLY VERIFIED: 1 theorem(s) accelerated (admitted, not proved): assoc_commut_quantified
        \\
    );

    // `assoc(assocLemma)`: associativity-only reorder on a CUSTOM operator
    // (no add/mul assumption). Emits kernel steps.
    ctx.okSilent(&.{ "check", "tests/cases/assoc.b4m" });

    // sides differ by more than associativity (operands permuted) → error
    ctx.fail(&.{ "check", "tests/cases/assoc_bad.b4m" }, "tests/cases/assoc_bad.b4m:11:12: error: assoc: sides differ by more than associativity: 'op(a, b)' vs 'op(b, a)'\n");

    // the required-arg contract: bare `assoc` is an error
    ctx.fail(&.{ "check", "tests/cases/assoc_missing_arg.b4m" }, "tests/cases/assoc_missing_arg.b4m:10:12: error: assoc requires an associativity lemma: assoc(<assocLemma>); got 0 argument(s)\n");

    // the assoc tactic certifies by default. (The --fast accelerated verdict is SUSPENDED —
    // strict-only during the rebuild — so --fast just re-certifies, no acceleration banner.)
    ctx.okSilent(&.{ "check", "tests/cases/assoc_oracle.b4m" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/assoc_oracle.b4m" });

    // simplify_quantified: peel forall over an equation, emits kernel steps
    ctx.okSilent(&.{ "check", "tests/cases/simplify_quantified.b4m" });

    // simplify_quantified on a bare equation redirects to simplify
    ctx.fail(&.{ "check", "tests/cases/simplify_quantified_bad.b4m" }, "tests/cases/simplify_quantified_bad.b4m:12:12: error: simplify_quantified expects a quantified goal; did you mean simplify?\n");

    // plain simplify on a quantified goal redirects to simplify_quantified
    ctx.fail(&.{ "check", "tests/cases/simplify_on_quantified.b4m" }, "tests/cases/simplify_on_quantified.b4m:12:12: error: simplify proves equations; did you mean simplify_quantified?\n");

    // symmetry: y = x from x = y in one step, emits kernel steps
    ctx.okSilent(&.{ "check", "tests/cases/symmetry.b4m" });

    // Milestone B2: tautology emits certificates — kernel-checked steps,
    // emits kernel steps, not accelerated (the accelerated path remains as the over-budget fallback)
    ctx.okSilent(&.{ "check", "tests/cases/tautology.b4m" });

    // certificates check with every step kernel-checked by default (no accelerated tactic)
    ctx.okSilent(&.{ "check", "tests/cases/tautology.b4m" });

    // non-consequence: the diagnostic carries the countermodel
    ctx.fail(&.{ "check", "tests/cases/tautology_bad.b4m" }, "tests/cases/tautology_bad.b4m:10:12: error: tautology: not a propositional consequence; countermodel: p := true, q := false\n");

    // the atom cap is a hard, honest limit
    ctx.fail(&.{ "check", "tests/cases/tautology_cap.b4m" }, "tests/cases/tautology_cap.b4m:25:12: error: tautology: 17 distinct atoms exceeds the limit of 16\n");

    // `iff` surface sugar: `P iff Q` desugars to `(P -> Q) and (Q -> P)` (never
    // reaches the kernel). iff_intro/iff_elim_forward/iff_elim_backward are thin
    // renames of the `and` rules; crucially `tautology` DECIDES iff goals and
    // CONSUMES iff hypotheses for free (it sees the desugared conjunction) — the
    // property the set/collection membership-axiom corpus relies on.
    ctx.okSilent(&.{ "check", "tests/cases/iff.b4m" });

    // SOUNDNESS negative: an iff must not license an unrelated conclusion —
    // tautology rejects `A iff B, A ⊢ C` with a countermodel that respects the iff.
    ctx.fail(&.{ "check", "tests/cases/iff_bad.b4m" }, "tests/cases/iff_bad.b4m:19:25: error: tautology: not a propositional consequence; countermodel: A := true, B := true, C := false\n");

    // GUARD: the biconditional shape `(X -> Y) and (Y -> X)` is canonically an
    // iff — `and_intro` is forbidden from producing it (must use `iff_intro`)…
    ctx.fail(&.{ "check", "tests/cases/iff_and_intro_bad.b4m" }, "tests/cases/iff_and_intro_bad.b4m:15:43: error: this goal is a biconditional '(X -> Y) and (Y -> X)' — use `iff_intro` (which is the same rule, named for what it proves)\n");

    // …and conversely `iff_intro` requires that shape — a plain conjunction is rejected.
    ctx.fail(&.{ "check", "tests/cases/iff_intro_bad.b4m" }, "tests/cases/iff_intro_bad.b4m:14:29: error: iff_intro's goal must be a biconditional (from `P iff Q`); this goal is not of the form '(X -> Y) and (Y -> X)' — did you mean `and_intro`?\n");

    // `iff_rewrite`: the propositional analogue of `=`-rewrite. From `P iff Q`,
    // replace the sub-proposition P by Q at any position (subformula congruence,
    // under connectives AND quantifiers), reusing the `=`-rewrite walker. A
    // kernel-checked rule (no --fast taint), sound because iff is a congruence.
    ctx.okSilent(&.{ "check", "tests/cases/iff_rewrite.b4m" });

    // it is SOUND: the claim must be reachable by replacing P with Q (or Q with P
    // — iff_rewrite is bidirectional) — an unrelated claim is rejected in BOTH.
    ctx.fail(&.{ "check", "tests/cases/iff_rewrite_bad.b4m" }, "tests/cases/iff_rewrite_bad.b4m:17:12: error: iff_rewrite cannot derive 'R' from 'P' using '(P -> Q) and (Q -> P)' (tried both orientations)\n");

    // …and its first argument must be a biconditional, not a plain implication.
    ctx.fail(&.{ "check", "tests/cases/iff_rewrite_notbicond.b4m" }, "tests/cases/iff_rewrite_notbicond.b4m:14:26: error: iff_rewrite expects a biconditional '(P -> Q) and (Q -> P)', got 'P -> Q'\n");

    // BIDIRECTIONAL rewrite: an equation / biconditional cited in the "wrong"
    // orientation for the goal still rewrites — no preceding `symmetry` needed.
    // The kernel tries lhs->rhs then rhs->lhs (sound: equality/iff are symmetric).
    ctx.okSilent(&.{ "check", "tests/cases/rewrite_reverse.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/iff_rewrite_reverse.b4m" });
    // …but a claim reachable in NEITHER orientation is still rejected (the change
    // is a superset of acceptance, not a hole).
    ctx.fail(&.{ "check", "tests/cases/rewrite_bad.b4m" }, "tests/cases/rewrite_bad.b4m:23:4: error: rewrite cannot derive 'B = D' from 'A = C' using 'A = B' (tried both orientations)\n");

    // Milestone C: arithmetic accelerated tactic — Presburger quantifier elimination
    ctx.ok(&.{ "check", "--fast", "tests/cases/arithmetic.b4m" },
        \\OK: 10 declarations, 4 theorems proven
        \\  — NOT FULLY VERIFIED: 4 theorem(s) accelerated (admitted, not proved): arithmetic
        \\
    );

    // pure-ℤ: the engine ranges over all integers (no implicit nonnegativity)
    // and recognizes neg/sub/prev, so ℤ linear identities — including sub/neg
    // cancellations outside a ℕ fragment — decide. (--fast gate: the bare
    // fixture has no ring lemmas in scope to certify with; strict certification
    // is exercised over the real integer theory in the std corpus.)
    ctx.ok(&.{ "check", "--fast", "tests/cases/arithmetic_integer.b4m" },
        \\OK: 17 declarations, 8 theorems proven
        \\  — NOT FULLY VERIFIED: 8 theorem(s) accelerated (admitted, not proved): arithmetic
        \\
    );

    // false statement: the diagnostic carries countermodel values
    ctx.fail(&.{ "check", "tests/cases/arithmetic_bad.b4m" }, "tests/cases/arithmetic_bad.b4m:17:20: error: arithmetic: false at a := 0, b := 0\n");

    // a relation opaque only because it hides a nonlinear term is
    // reported honestly as outside the fragment, not as a false countermodel
    ctx.fail(&.{ "check", "tests/cases/arithmetic_frag.b4m" }, "tests/cases/arithmetic_frag.b4m:15:12: error: the generated proof of this step cites 'mulIsCommutative', which is not in scope here; alias it from the theory that states it (`theorem mulIsCommutative = <module>.mulIsCommutative`)\n");

    // Milestone D: the SMT combination — mixed goals, one accelerated-tactic name
    ctx.ok(&.{ "check", "--fast", "tests/cases/smt.b4m" },
        \\OK: 9 declarations, 2 theorems proven
        \\  — NOT FULLY VERIFIED: 2 theorem(s) accelerated (admitted, not proved): arithmetic
        \\
    );

    // Milestone C2b: universal linear goals replay as kernel-checked certificates
    // (sorted-sum normalization + synthesized order witnesses)
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert2.b4m" });

    // Farkas: difference-logic infeasibility (combine several order
    // hypotheses into a transitivity cycle) certifies purely under the
    // DEFAULT, via `arithmetic(<theory>)` resolving the order lemmas
    // against the named module — no local aliasing of the vocabulary.
    ctx.okSilent(&.{ "check", "tests/cases/farkas.b4m" });

    // Farkas extensions: order composition (a<b -> b<c -> a<c, no cycle)
    // and the infeasibility cap (contradictory order hyps prove an
    // arbitrary conclusion via lessThanIrreflexive + absurd).
    ctx.okSilent(&.{ "check", "tests/cases/farkas_ext.b4m" });

    // Farkas coefficient scaling: a hypothesis scaled by a literal
    // via multiplicationPreservesOrder before the infeasibility fold.
    ctx.okSilent(&.{ "check", "tests/cases/farkas_scale.b4m" });

    // Farkas sum path: sum two order hypotheses over distinct
    // variables via additionPreservesOrder + commutativity + transitivity.
    ctx.okSilent(&.{ "check", "tests/cases/farkas_sum.b4m" });

    // Milestone C2a: ground goals replay as kernel-checked simplify certificates
    // over the well-known peano axioms — the default check accepts them
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert.b4m" });

    // additive-inverse cancellation across a separated summand: `add(a, sub(b,a))
    // = b` normalizes to a {a, b, neg(a)} multiset that reduces to {b} — the
    // equation certifier must cancel a with neg(a) (a `neg`-leaf tower).
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert_neg_cancel.b4m" });

    // numeral summand: `add(ONE, sub(b, ONE)) = b` — the ONE / neg(ONE) inverse
    // pair must cancel even though ONE is a `succ(ZERO)` tower sitting as an inner
    // summand (not the top-level succ prefix). parseTower folds the numeral into
    // the tower's constant offset so the pair meets and cancels.
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert_numeral_leaf.b4m" });

    // diagnostic: the SAME goal with `addLeftSwap` omitted from scope must report
    // the specific missing rewrite lemma ("theory lacks lemma 'addLeftSwap'"), not
    // the generic "form not in certification scope" (which reads as "wrong shape"
    // and hides the one-alias fix). Guards the equation certifier's decline reason.
    ctx.fail(
        &.{ "check", "tests/cases/arithmetic_missing_lemma_diagnostic.b4m" },
        "tests/cases/arithmetic_missing_lemma_diagnostic.b4m:37:20: error: the generated proof of this step cites 'addLeftSwap', which is not in scope here; alias it from the theory that states it (`theorem addLeftSwap = <module>.addLeftSwap`)\n",
    );

    // opaque compound leaves: `add(f(x), sub(g(y), f(x))) = g(y)` — foreign
    // apps f(x)/g(y) ride the sorted-tower join as atoms and the f(x)/neg(f(x))
    // pair cancels (bubbled to the tail so addNeg matches an innermost subterm).
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_cert_opaque_leaf.b4m" });

    // Cooper-replay layer 2 (witness direction): a `forall x; exists y; …`
    // goal with a period-1 Cooper trace elaborates fully — the cooper link
    // picks a boundary witness and emits exists_intro over an or-intro arm.
    ctx.okSilent(&.{ "check", "tests/cases/cooper_witness.b4m" });

    // Cooper-replay layer 3 (periodicity direction): a period-2 (parity) ∀∃
    // goal elaborates fully via a SYNTHESIZED induction — the cooper link builds
    // predicate P(k), proves base P(ZERO) and step P(k)->P(succ(k)) (unpacking
    // the IH witness and shifting it per parity arm), then instantiates the
    // `induction` schema. This is `evenOrOdd` (add-form), fully accelerated-free.
    ctx.okSilent(&.{ "check", "tests/cases/cooper_parity.b4m" });

    // The cooper link's DECLARED BOUNDARY: a multi-fixed-variable ∀∀∃
    // (`forall a, b; exists c; …`) is decided valid by Presburger but declines
    // — cooperInduction synthesizes an induction on a SINGLE variable. Without
    // a fallback, default mode is a hard error listing every link's decline
    // (the "solvable by arithmetic, not yet certifiable" gap)...
    ctx.fail(&.{ "check", "tests/cases/cooper_gap_raw.b4m" },
        \\tests/cases/cooper_gap_raw.b4m:25:12: error: 'arithmetic' is valid but no certifier could prove it here:
        \\  - equation/order/exists: form not in certification scope
        \\  - mixed-skeleton: form not in certification scope
        \\  - farkas: theory lacks symbol 'less_than'
        \\  - cooper: form not in certification scope
        \\use --fast to accept the accelerated verdict
        \\
    );
    // ...and --fast accepts the accelerated verdict, marking the theorem accelerated.
    ctx.ok(&.{ "check", "--fast", "tests/cases/cooper_gap_raw.b4m" },
        \\OK: 15 declarations, 1 theorems proven
        \\  — NOT FULLY VERIFIED: 1 theorem(s) accelerated (admitted, not proved): arithmetic
        \\
    );
    // ...and `[using arithmetic fallback(<thm>)]` closes the gap fully proven in default
    // mode: the chain declines, so the cited manual theorem (which reduces the
    // ∀∀∃ to the cooper-certified single-variable evenOrOddArith) stands as the
    // certificate — no --fast, no acceleration.
    ctx.okSilent(&.{ "check", "tests/cases/cooper_gap.b4m" });

    // negative ℤ witness: `exists y; x = succ(y)` certifies STRICT with y = prev(x)
    // (built as a prev-tower, discharged via succPrev) — a witness the ℕ-only
    // succ-tower builder could not construct.
    ctx.okSilent(&.{ "check", "tests/cases/cooper_negative_witness.b4m" });

    // Case D: a `fallback(<thm>)` on a goal the arithmetic CERTIFIER CHAIN can
    // discharge itself is REDUNDANT — strict `check` rejects it. (Distinct from
    // cooper_gap, where the certifier DECLINES so the fallback is legitimate.)
    ctx.fail(&.{ "check", "tests/cases/arithmetic_fallback_redundant_bad.b4m" }, "tests/cases/arithmetic_fallback_redundant_bad.b4m:31:32: error: 'arithmetic' certifies this goal on its own — the fallback 'twoTimesTwoManual' is unnecessary; drop `fallback(twoTimesTwoManual)`\n");
    // `--fast` suppresses it structurally (the certifier chain never runs).
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/arithmetic_fallback_redundant_bad.b4m" });
    // `--draft` suppresses it (WIP: don't nag about redundant fallbacks yet).
    ctx.okSilent(&.{ "check", "--draft", "tests/cases/arithmetic_fallback_redundant_bad.b4m" });

    // a `fallback(<axiom-or-hole>)` is accepted (not only theorems): the goal has
    // an opaque subterm the certifier can't discharge, so the arithmetic step
    // falls back to a `hole` (an axiom-kind statement). The proof rests on the
    // hole → rejected strict, accepted under --draft with the hole disclosed.
    ctx.okSilent(&.{ "check", "--draft", "tests/cases/arithmetic_fallback_axiom.b4m" });

    // a `fallback(<forall-theorem>)` on a SPECIALIZED goal (an instance of the
    // theorem, not alpha-equal): the matcher peels the ∀ prefix (inferring the
    // witnesses by matching the conclusion against the goal) and discharges any
    // leading `->` antecedents from the step's refs, emitting a kernel-certified
    // forall_elim+modus_ponens chain. Verifies STRICT (the fallback targets are
    // axiom-proven, no holes) — so the emitted specialization really re-checks.
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_fallback_specialize.b4m" });

    // linear-equation-combination certifier: an equation goal that follows by
    // CANCELLING an equality PREMISE (sub(a,r) = mul(b,q) from the premise
    // add(mul(b,q),r) = a) over opaque leaves. The rewrite-normalizer can't fire
    // the premise as a rewrite, but the goal is a linear combination of it: the
    // certifier proves the identity add(P_l,G_l)=add(P_r,G_r), rewrites the
    // premise, and cancels — a kernel-checked chain. Verifies STRICT.
    ctx.okSilent(&.{ "check", "tests/cases/arithmetic_linear_equation_premise.b4m" });

    // arithmetic × SCHEMA: Case D fires from inside a schema body too — the
    // declaration-time wellformedness self-check (instantiate at opaque params,
    // run the proof) exercises arithmeticJustification, so a redundant `fallback`
    // in a schema's proof is rejected. `--fast`/`--draft` suppress it as usual.
    ctx.fail(&.{ "check", "tests/cases/schema_arithmetic_fallback_bad.b4m" }, "tests/cases/schema_arithmetic_fallback_bad.b4m:30:32: error: 'arithmetic' certifies this goal on its own — the fallback 'twoTwo' is unnecessary; drop `fallback(twoTwo)`\n");
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/schema_arithmetic_fallback_bad.b4m" });
    ctx.okSilent(&.{ "check", "--draft", "tests/cases/schema_arithmetic_fallback_bad.b4m" });

    // arithmetic over a SCHEMA VALUE PARAMETER: the demand engine checks a schema per
    // instance at the citer's actual arguments (no opaque-param self-check), so `k` is an
    // ordinary term there and the step certifies. (The eager engine rejected this — "cannot
    // yet decide this goal over the schema parameter 'k'" — an artifact of its opaque
    // reification; the fixture keeps its historical name.)
    ctx.okSilent(&.{ "check", "tests/cases/schema_arithmetic_param_bad.b4m" });

    // Milestone D2: mixed skeletons replay as kernel-checked certificates
    ctx.okSilent(&.{ "check", "tests/cases/smt_cert.b4m" });

    // mixed countermodel: arithmetic values plus opaque truth values
    ctx.fail(&.{ "check", "tests/cases/smt_bad.b4m" }, "tests/cases/smt_bad.b4m:12:12: error: arithmetic: false at a := 0, p := false\n");

    // instantiating strongInduction re-checks its full stored proof
    ctx.okSilent(&.{ "check", "tests/cases/strong_induction.b4m" });
}
