//! Integration gates — command-line contract: usage, flags, error diagnostics, and the fmt --check exemplars, plus kernel-mechanic fixtures (define, div guards, not_intro, forward refs, case/shadow rules).
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

    // No arguments -> usage on stderr, exit 1.
    const no_args = b.addRunArtifact(exe);
    no_args.has_side_effects = true;
    no_args.expectStdErrEqual(
        "usage: 2b4m check [--fast | --fast-only W… | --fast-except W…] [--draft] [--axioms] [--library] [--trace-facts] [--chaos[=SEED]] [-j<n>] [--io-threads=<n>] [--sync-io] [--io-delay=<us>] <file.b4m | dir> [theorem]\n" ++
            "       2b4m fmt [--check] <file.b4m|.md>\n" ++
            "       2b4m lint <file.b4m|.md>\n" ++
            "       2b4m debug accelerant <file> <line | theorem step-label>\n" ++
            "       2b4m debug taint <file> [theorem]\n" ++
            "       2b4m query outline <file.b4m> [theorem]\n" ++
            "       2b4m query claims <file.b4m> [theorem]\n" ++
            "       2b4m query theorem <file.b4m> <theorem> [--sig]\n" ++
            "       2b4m query whereis <file.b4m> <identifier>\n" ++
            "       2b4m query search <file.b4m|dir> <query>\n" ++
            "       2b4m query uses <file.b4m> [theorem]\n",
    );
    no_args.expectExitCode(1);
    test_step.dependOn(&no_args.step);

    // fmt --check: the exemplars are canonically formatted. The `.md` entries
    // exercise the literate path (formatLiterate reflows the ```2b4m blocks and
    // leaves prose verbatim); the rest are plain `.b4m` sources.
    for ([_][]const u8{ "examples/peano.b4m", "examples/peano-pure.b4m", "examples/peano-imports.b4m", "examples/gauss.b4m", "examples/gauss-pure.b4m", "examples/euclid.b4m", "examples/euclid-compute.b4m", "examples/incorrect.b4m", "examples/sqrt2.b4m", "std/peano.b4m", "std/peano/order.b4m", "std/peano/subtraction.b4m", "std/peano/divides.b4m", "std/peano/parity.b4m", "std/group.b4m", "std/group/power.b4m", "std/group/sequence.b4m", "std/ring.b4m", "std/field.b4m", "std/field/order.b4m", "std/rational.b4m", "std/real.b4m", "std/complex.b4m", "std/set.b4m", "std/collection.b4m", "std/function.b4m", "std/function/invertible.b4m", "std/set/finite.b4m", "std/permutation.b4m", "std/integer.b4m", "std/integer/order.b4m", "std/integer/wellordering.b4m", "std/integer/divides.b4m", "std/sequence.b4m", "std/integer/sequence.b4m", "std/integer/product.b4m", "std/integer/sum.b4m", "std/primes.b4m", "std/integer/examples.b4m", "std/real/examples.b4m", "std/rational/examples.b4m", "std/sequence/examples.b4m", "std/collection/examples.b4m", "std/equivalence/examples.b4m", "std/function/examples.b4m", "std/complex/examples.b4m", "std/ring/examples.b4m", "std/field/examples.b4m", "std/peano/examples.b4m", "std/divisibility.b4m", "std/element.b4m", "std/relation.b4m", "std/equivalence.b4m", "aata/3.1-integers-mod-n.md", "aata/3.1-integers-mod-n-exercises.md", "aata/3.2-groups.md", "aata/3.2-groups-exercises.md", "aata/3.3-subgroups.md", "aata/3.3-subgroups-exercises.md", "aata/1.2.1-sets.md", "aata/1.2.1-sets-exercises.md", "aata/1.2.2-functions.md", "aata/1.2.2-functions-exercises.md", "aata/1.2.3-relations.md", "aata/1.2.3-relations-exercises.md", "aata/1.2.3-partitions.md", "aata/2.1-induction.md", "aata/2.1-induction-exercises.md", "aata/2.2-division-algorithm.md", "aata/2.2-division-algorithm-exercises.md", "aata/2.3-primes.md", "aata/2.3-primes-exercises.md", "tests/cases/kebab_label_ok.b4m", "tests/cases/schema_eta.b4m", "tests/cases/schema_binary_param.b4m", "tests/cases/schema_wellformed_ok.b4m", "tests/cases/schema_wellformed_bad.b4m", "tests/cases/choice_description.b4m", "tests/cases/model_accel_simplify.b4m", "tests/cases/model_accel_assoc.b4m", "tests/cases/model_accel_assoc_commut.b4m", "tests/cases/model_accel_tautology.b4m", "tests/cases/model_accel_polynomial.b4m", "tests/cases/model_accel_arithmetic.b4m", "tests/cases/model_accel_extensionality.b4m", "tests/cases/model_schema_source.b4m", "tests/cases/model_schema.b4m", "tests/cases/model_schema_bad.b4m", "tests/cases/model_schema_claim_bad.b4m", "tests/cases/case_split.b4m", "tests/cases/fix_sibling_reuse.b4m", "tests/cases/outline.b4m", "tests/cases/query_claims_schema.b4m", "tests/cases/model_obligation_arrow.b4m", "tests/cases/model_axiom_colon_bad.b4m", "tests/cases/model_symbol_arrow_bad.b4m", "tests/cases/schema_accelerant_polynomial.b4m", "tests/cases/arithmetic_fallback_redundant_bad.b4m", "tests/cases/arithmetic_fallback_specialize.b4m", "tests/cases/arithmetic_linear_equation_premise.b4m", "tests/cases/specialize_local.b4m", "tests/cases/specialize_local_bad.b4m", "tests/cases/schema_arithmetic_fallback_bad.b4m", "tests/cases/schema_arithmetic_param_bad.b4m", "tests/cases/assoc_commut_custom.b4m", "tests/cases/assoc_commut_bad_arity.b4m", "tests/cases/assoc_commut_oracle.b4m", "tests/cases/polynomial_oracle.b4m", "tests/cases/polynomial_neg.b4m", "tests/cases/polynomial_inverse.b4m", "tests/cases/polynomial_coeff.b4m", "tests/cases/polynomial_coeff_bad.b4m", "tests/cases/polynomial_field.b4m", "tests/cases/search_target.b4m", "tests/cases/assoc.b4m", "tests/cases/assoc_bad.b4m", "tests/cases/assoc_missing_arg.b4m", "tests/cases/assoc_oracle.b4m", "tests/cases/axiom_as_step_bad.b4m", "tests/cases/single_theorem.b4m", "tests/cases/axioms_report.b4m", "tests/cases/integer_seq_both_folds.b4m", "tests/cases/dir_ok/base.b4m", "tests/cases/dir_ok/sub/uses_base.b4m", "tests/cases/dir_ok/literate.md", "tests/cases/dir_bad/fine.b4m", "tests/cases/dir_bad/broken.b4m", "tests/cases/dir_library_bad/spare.b4m", "tests/cases/import_axiom_taint/lib.b4m", "tests/cases/import_axiom_taint/user.b4m" }) |path| {
        const fmt_check = b.addRunArtifact(exe);
        fmt_check.has_side_effects = true;
        fmt_check.setCwd(b.path("."));
        fmt_check.addArgs(&.{ "fmt", "--check", path });
        fmt_check.expectStdErrEqual("");
        fmt_check.expectExitCode(0);
        test_step.dependOn(&fmt_check.step);
    }

    // lint: canonical binder order. The fixture's `bad` axiom reverses
    // first-appearance order; lint flags it (exit 1) and leaves `good` alone.
    ctx.fail(
        &.{ "lint", "tests/cases/lint_binder_order.b4m" },
        "tests/cases/lint_binder_order.b4m:11:12: error: non-canonical binder order: 'forall b, a' should be 'forall a, b' (first-appearance order in the body)\n",
    );

    // Nonexistent file -> clean diagnostic on stderr, exit 1.
    ctx.fail(&.{ "check", "nosuchfile.b4m" }, "error: cannot open 'nosuchfile.b4m': file not found\n");

    // Existing, valid file -> parses and checks with no diagnostics. It is
    // comments-only (no theorem declarations), so it has nothing to prove —
    // exit 0 (a file that proves zero theorems is a clean success).
    const ok = b.addRunArtifact(exe);
    ok.has_side_effects = true;
    ok.addArg("check");
    ok.addFileArg(b.path("tests/cases/smoke.b4m"));
    ok.expectStdErrEqual("");
    ok.expectExitCode(0);
    test_step.dependOn(&ok.step);

    // Syntax error -> exact diagnostic with line:col on stderr, exit 1.
    // cwd pinned to build root so the relative path in the diagnostic is stable.
    ctx.fail(&.{ "check", "tests/cases/syntax_err.b4m" }, "tests/cases/syntax_err.b4m:4:11: error: expected ':', got 'forall'\n");

    // M2: full declaration surface elaborates cleanly. A decls-only file has no
    // theorem declarations, so it has nothing to prove — exit 0 (a file that
    // proves zero theorems is a clean success).
    const decls = b.addRunArtifact(exe);
    decls.has_side_effects = true;
    decls.setCwd(b.path("."));
    decls.addArgs(&.{ "check", "tests/cases/pa_decls.b4m" });
    decls.expectStdErrEqual("");
    decls.expectExitCode(0);
    test_step.dependOn(&decls.step);

    // M2: sort errors are caught at elaboration with a precise location. A root-file AXIOM is
    // now elaborated for well-formedness too (its statement's guard/refined obligations are the
    // point — see div_nested), so the ill-typed `bad` axiom reports at its OWN site (7:17) in
    // addition to the theorem that also cites the shape (9:35). Both are genuine, at the right
    // locations; errors print sorted by source position.
    ctx.fail(&.{ "check", "tests/cases/sort_mismatch.b4m" },
        \\tests/cases/sort_mismatch.b4m:7:17: error: expected sort 'Nat', got 'Prop'
        \\tests/cases/sort_mismatch.b4m:9:35: error: expected sort 'Nat', got 'Prop'
        \\
    );

    // M3: proofs that must check
    ctx.okSilent(&.{ "check", "tests/cases/modus_ponens.b4m" });
    // DEFINITION BLOCKS: a pred/func declaration carrying its defining clauses. Pins all
    // three forms — a predicate (one clause, cited bare), a multi-clause function (cited by
    // zero-indexed arm), and Erlang-style `when` guards — plus that the emitted axioms are
    // real, kernel-checked facts (the theorems instantiate them).
    ctx.okSilent(&.{ "check", "tests/cases/definition_blocks.b4m" });
    ctx.okSilent(&.{ "fmt", "--check", "tests/cases/definition_blocks.b4m" });
    // `--axioms` discloses a definition clause DIFFERENTLY from an assumption: a definition
    // introduces a symbol (doubting it is not coherent), an assumption constrains a
    // primitive, and only the second is something a reader should weigh. Reported under the
    // SYMBOL and its clause — never the mangled publication name.
    ctx.ok(&.{ "check", "tests/cases/definition_blocks.b4m", "--axioms" },
        \\OK: 15 declarations, 3 theorems proven
        \\  — rests on 3 axiom(s):
        \\      isZero (clause 0)  (tests/cases/definition_blocks.b4m:10)  — DEFINITION
        \\      add (clause 0)  (tests/cases/definition_blocks.b4m:14)  — DEFINITION
        \\      add (clause 1)  (tests/cases/definition_blocks.b4m:14)  — DEFINITION
        \\
    );
    ctx.okSilent(&.{ "check", "tests/cases/imp_chain.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/forall_swap.b4m" });

    // M3: broken siblings with exact diagnostics
    ctx.fail(&.{ "check", "tests/cases/modus_ponens_bad.b4m" }, "tests/cases/modus_ponens_bad.b4m:16:22: error: modus_ponens expects an implication, got 'p'\n");

    // citing an axiom where a proof STEP is required: the diagnostic must
    // point at the fix (materialize it as a step first), not report a bare
    // "unknown reference".
    ctx.fail(&.{ "check", "tests/cases/axiom_as_step_bad.b4m" }, "tests/cases/axiom_as_step_bad.b4m:14:24: error: 'pall' is a fact, not a proof step; introduce it as a step first with `[by cite pall]`, then reference that step\n");

    ctx.fail(&.{ "check", "tests/cases/fix_shadow_bad.b4m" }, "tests/cases/fix_shadow_bad.b4m:10:13: error: 'a' shadows an enclosing variable; choose a fresh name\n");

    // M6: --help
    const help = b.addRunArtifact(exe);
    help.has_side_effects = true;
    help.addArg("--help");
    help.expectExitCode(0);
    test_step.dependOn(&help.step);

    // M4: ill-sorted schema argument dies at the use site
    ctx.fail(&.{ "check", "tests/cases/induction_bad_sort.b4m" }, "tests/cases/induction_bad_sort.b4m:14:51: error: expected sort 'Prop', got 'Nat'\n");

    // proof-carrying schema `zeroLike(t): t = ZERO` whose body only survives the t := ZERO
    // instance. A schema NEED NOT be a true universal (a narrow one is bad form, not wrong, #93);
    // there is NO decl-time check. Soundness is the PER-INSTANCE proof: the bad instantiation
    // `zeroLike(succ ZERO)` is proved and FAILS at the body's reflexivity step (`succ(ZERO)=ZERO`).
    // `instantiation` is NOT admit-trustable, so `--fast` behaves IDENTICALLY to strict here (the
    // bad instance is always proved — admitting it shape-only would be unsound).
    ctx.fail(&.{ "check", "tests/cases/schema_per_instance.b4m" },
        \\tests/cases/schema_per_instance.b4m:10:4: error: reflexivity requires a claim of the form 't = t', got 'succ(ZERO) = ZERO'
        \\
    );
    ctx.fail(&.{ "check", "--fast", "tests/cases/schema_per_instance.b4m" },
        \\tests/cases/schema_per_instance.b4m:10:4: error: reflexivity requires a claim of the form 't = t', got 'succ(ZERO) = ZERO'
        \\
    );

    // forward label references: a step may cite a later-defined label
    ctx.okSilent(&.{ "check", "tests/cases/forward_ref.b4m" });

    // mutually-citing steps form a justification cycle, reported by name
    ctx.fail(&.{ "check", "tests/cases/forward_ref_cycle.b4m" }, "tests/cases/forward_ref_cycle.b4m:10:4: error: cyclic justification: a -> b -> a\n");

    // a self-instantiating schema is a named cycle, not a blunt depth cap. The
    // strict declaration-time opaque check catches it first (its body instantiates
    // itself); the later real instantiation site reports it again.
    ctx.fail(&.{ "check", "tests/cases/schema_cycle.b4m" },
        \\tests/cases/schema_cycle.b4m:11:26: error: cyclic schema instantiation of 'loopy'
        \\
    );

    // a deep but terminating instantiation chain (10 distinct schemas) is
    // accepted — the old inst_depth cap wrongly rejected it
    ctx.okSilent(&.{ "check", "tests/cases/schema_deep_ok.b4m" });

    // kebab-case is rejected in a declaration-name position (parser)
    ctx.fail(&.{ "check", "tests/cases/kebab_decl_bad.b4m" }, "tests/cases/kebab_decl_bad.b4m:6:6: error: expected 'identifier', got 'foo-bar'\n");

    // kebab-case IS allowed for proof labels and [by ...] references
    ctx.okSilent(&.{ "check", "tests/cases/kebab_label_ok.b4m" });

    // eta-sugar: a schema Nat->Prop param accepts a bare predicate name
    ctx.okSilent(&.{ "check", "tests/cases/schema_eta.b4m" });

    // N-ary schema params: a RELATIONAL (2-arg) `Element -> Element -> Prop` param,
    // instantiated by a bare binary predicate (eta) and a 2-binder lambda, applied
    // to two args in the body (each application beta-reduces both binders).
    ctx.okSilent(&.{ "check", "tests/cases/schema_binary_param.b4m" });

    // definite description (the tame ι) as an axiom-schema over a relational param:
    // a proven total+single-valued graph is realized by a function (`exists g`).
    ctx.okSilent(&.{ "check", "tests/cases/choice_description.b4m" });

    // the `case` construct: a 3-way disjunction split checks with every step kernel-checked
    ctx.okSilent(&.{ "check", "tests/cases/case_split.b4m" });

    // a `case` arm assuming the wrong disjunct is a located error
    ctx.fail(&.{ "check", "tests/cases/case_bad_arm.b4m" }, "tests/cases/case_bad_arm.b4m:19:8: error: or_elim: subproof must assume 'p(Z)'\n");

    // forall_elim at several arguments emits the chain in one written step
    ctx.okSilent(&.{ "check", "tests/cases/forall_elim_multi.b4m" });

    // no-shadowing rule: disjoint sibling subproofs may reuse a fix var
    ctx.okSilent(&.{ "check", "tests/cases/fix_sibling_reuse.b4m" });

    // no-shadowing rule for labels: an inner label shadowing an enclosing
    // one is an error (disjoint sibling reuse stays fine)
    ctx.fail(&.{ "check", "tests/cases/label_shadow_bad.b4m" }, "tests/cases/label_shadow_bad.b4m:17:8: error: label 'base' shadows an enclosing label; choose a fresh name\n");

    // the forward manifest is checked: promised theorems must exist
    ctx.fail(&.{ "check", "tests/cases/forward_bad.b4m" },
        \\tests/cases/forward_bad.b4m:3:10: error: forwarded theorem 'missingTheorem' is never defined
        \\tests/cases/forward_bad.b4m:4:10: error: 'onlyAxiom' is forwarded as a theorem but defined as an axiom
        \\
    );

    // `define` abbreviations expand transparently; certificates unaffected
    ctx.okSilent(&.{ "check", "tests/cases/define.b4m" });

    // `define` expansion is CAPTURE-AVOIDING: a nested define call whose inner
    // formal name collides with an outer define's argument must not capture it
    // (`outer(n, x)` = `mul(n, x)`, NOT `mul(x, x)`).
    ctx.okSilent(&.{ "check", "tests/cases/define_no_capture.b4m" });

    // a PARAMETERIZED, Prop-valued `define` — a transparent (macro) predicate.
    // `even(n)` expands to its body at elaboration (the kernel never sees `even`),
    // so a proof that needs the body gets it for free — no unfold/cite step.
    ctx.okSilent(&.{ "check", "tests/cases/define_pred.b4m" });

    // a `define`d pred is ACCEPTED as a `where` guard: the sort decl's walk EXPANDS it
    // (define lifecycle) into an anonymous guard TERM qualifier. Both the named-sort
    // `sort H = G where D` site (a `fix x: H` carries the expanded guard) …
    ctx.okSilent(&.{ "check", "tests/cases/define_where_guard.b4m" });

    // … and the anonymous inline-`where` site (`x: G where D` in a binder), which the
    // expansion pass desugars to `forall x: G; D(x) -> …` with the call expanded.
    ctx.okSilent(&.{ "check", "tests/cases/define_where_guard_inline.b4m" });

    // defines share the declaration namespace
    ctx.fail(&.{ "check", "tests/cases/define_bad.b4m" }, "tests/cases/define_bad.b4m:5:8: error: duplicate declaration of 'TWO'\n");

    // a define's PARAMS TAKE NO SORT: a define is a macro whose args arrive already
    // elaborated, so the body's own elaboration types every use of them — a declared param
    // sort is a second, redundant source that can only agree or spuriously disagree. A parse
    // error, so --draft does not relax it.
    ctx.fail(&.{ "check", "tests/cases/define_param_sort_bad.b4m" }, "tests/cases/define_param_sort_bad.b4m:7:16: error: define parameters take no sort — a define is a macro whose sorts are inferred from its body\n");

    // a define that ONLY FORWARDS an opaque symbol (`define lt(a, b) = ordering.less_than(a, b)`)
    // is an alias written as a macro — the name gets the wrong kind (define, not pred), so
    // downstream `pred lt = this.lt` aliases refuse it. Rejected unless --draft (diagnosed at
    // the define's FIRST USE — a define is only ever met by expansion); the diagnostic spells
    // the alias form. A PERMUTED forward (`gt(a, b) = less_than(b, a)`) is
    // a genuine macro and is accepted.
    ctx.fail(&.{ "check", "tests/cases/define_alias_bad.b4m" }, "tests/cases/define_alias_bad.b4m:7:35: error: define 'lt' only forwards 'ordering.less_than' — it is an alias, not a macro; write `pred lt = ordering.less_than` (--draft allows)\n");
    ctx.okSilent(&.{ "check", "--draft", "tests/cases/define_alias_bad.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/define_forward_permuted_ok.b4m" });

    // a define whose body calls an ALIAS to a REMOTE define: expanding the outer define
    // resolves the callee in the outer define's home file, where it is an alias, and
    // following that alias needs the alias's own import fetched. While that demand is
    // outstanding the pass must report PENDING (suspend + retry), not fall through and
    // demand the name as an IDENTIFIER — a define is never one, so the demand would hit
    // FetchTask's misuse arm against another file's offsets (it crashed, pre-fix).
    ctx.okSilent(&.{ "check", "tests/cases/define_alias_nested.b4m" });

    // the same PENDING window at a binder GUARD: an inline `where` whose guard aliases a
    // remote define, inside another define's body. A pending guard must be left as written
    // (the pass re-runs), never symbolized — symbolizing demands a define as an identifier.
    ctx.okSilent(&.{ "check", "tests/cases/define_guard_nested.b4m" });

    // ALIAS-COLLAPSE (Foundation C): an IDENT alias (sort/const/func/pred) binds to the
    // target's origin Index, so a local proof matches a source axiom cited across the alias
    // boundary (the collapsed sorts are one Index — no mismatch).
    ctx.okSilent(&.{ "check", "tests/cases/alias_ident.b4m" });
    // a FACT alias re-exports a proven fact by origin; citing the local name resolves to it.
    ctx.okSilent(&.{ "check", "tests/cases/alias_fact.b4m" });

    // `specialize THM(args) hyps…` applies a forall-theorem (∀-elim + modus_ponens
    // chain, emitted + kernel-checked) in one step. Positive: single/multi-arg,
    // multi-hyp, no-hyp all check strict.
    ctx.okSilent(&.{ "check", "tests/cases/specialize.b4m" });
    // args + hyps interleave by formula structure (the guarded-induction shape
    // `forall k; guard(k) -> forall s,t; …` applied in one step).
    ctx.okSilent(&.{ "check", "tests/cases/specialize_interleave.b4m" });
    // the head may be a LOCAL STEP LABEL (a `forall`-shaped assumed/derived fact),
    // not only a declared theorem/axiom — applied with no cite step + no taint.
    ctx.okSilent(&.{ "check", "tests/cases/specialize_local.b4m" });
    // …but a local head whose formula is NOT universally quantified is rejected
    // with the same "not universally quantified" diagnostic (now via a step head).
    ctx.fail(&.{ "check", "tests/cases/specialize_local_bad.b4m" }, "tests/cases/specialize_local_bad.b4m:19:16: error: specialize: head is not universally quantified enough for 1 argument(s)\n");

    // `chain`: prove A = Z from cited equations used in any direction +
    // congruence (union-find + BFS, emits a rewrite/symmetry certificate).
    // Positive (transitivity, congruence, combined); negative (no path).
    ctx.okSilent(&.{ "check", "tests/cases/chain.b4m" });
    ctx.fail(&.{ "check", "tests/cases/chain_bad.b4m" }, "tests/cases/chain_bad.b4m:11:21: error: chain: cannot connect 'a' to 'z' from the cited equations\n");
    // over-args (∀ prefix exhausted), extra hyp with no antecedent, and a schema
    // (redirect to instantiate) each fail cleanly.
    ctx.fail(&.{ "check", "tests/cases/specialize_overargs_bad.b4m" }, "tests/cases/specialize_overargs_bad.b4m:7:23: error: specialize: head is not universally quantified enough for 2 argument(s)\n");
    ctx.fail(&.{ "check", "tests/cases/specialize_nohyp_bad.b4m" }, "tests/cases/specialize_nohyp_bad.b4m:12:50: error: schema instance 'p(ZERO)' has no antecedent left for this premise\n");
    ctx.fail(&.{ "check", "tests/cases/specialize_schema_bad.b4m" }, "tests/cases/specialize_schema_bad.b4m:7:45: error: 'sch' is a schema; use `[using instantiation sch(...)]`, not a fact citation\n");

    // the outline fixture is itself a valid proof
    ctx.okSilent(&.{ "check", "tests/cases/outline.b4m" });

    // the search fixture is itself a valid proof
    ctx.okSilent(&.{ "check", "tests/cases/search_target.b4m" });

    // an error in an embedded proof maps to the .md's OWN line number
    // (prose-masking preserves line offsets).
    ctx.fail(&.{ "check", "tests/cases/literate_bad.md" }, "tests/cases/literate_bad.md:16:4: error: reflexivity requires a claim of the form 't = t', got 'A = B'\n");

    // M5: guards discharged by hypothesis and by matching lemma
    ctx.okSilent(&.{ "check", "tests/cases/div_ok.b4m" });

    // M5: unguarded division is rejected with the exact obligation — at the PROOF STEP that
    // writes the term (a statement is a claim and owes nothing; user ruling 2026-09-13).
    ctx.fail(&.{ "check", "tests/cases/div_bad.b4m" },
        \\tests/cases/div_bad.b4m:10:5: error: unproved obligation: 'ZERO != ZERO'
        \\tests/cases/div_bad.b4m:10:22: error: unproved obligation: 'ZERO != ZERO'
        \\
    );

    // M5: nested guarded applications report every obligation (at the step citing the axiom).
    ctx.fail(&.{ "check", "tests/cases/div_nested.b4m" },
        \\tests/cases/div_nested.b4m:11:5: error: unproved obligation: 'div(ZERO, ZERO) != ZERO'
        \\tests/cases/div_nested.b4m:11:15: error: unproved obligation: 'ZERO != ZERO'
        \\
    );

    // Review fix: not_intro may only cite steps available at the END of
    // the cited subproof, not inside deeper nested assumptions
    ctx.fail(&.{ "check", "tests/cases/not_intro_nested_bad.b4m" }, "tests/cases/not_intro_nested_bad.b4m:24:21: error: not_intro: 's1' is not accessible at the conclusion of the cited subproof\n");

    // Review fix: a block whose only content is a nested subproof has no
    // conclusion to discharge (was: kernel panic)
    ctx.fail(&.{ "check", "tests/cases/no_conclusion_bad.b4m" }, "tests/cases/no_conclusion_bad.b4m:18:23: error: subproof 'b' has no concluding step of its own\n");

    // `hole`: an aspirational axiom-shaped placeholder. Default mode REJECTS a
    // file that rests on one, enumerating each hole with its location and the
    // theorems that depend on it.
    ctx.fail(&.{ "check", "tests/cases/hole.b4m" },
        \\error: 1 hole(s) remain (default mode rejects holes; use --draft while filling them):
        \\  - zeroIsEven  (tests/cases/hole.b4m:10)  — rested on by: restsOnHole
        \\
    );
    // --draft allows holes (exit 0) with a loud disclosure banner naming them.
    ctx.ok(&.{ "check", "--draft", "tests/cases/hole.b4m" },
        \\OK: 6 declarations, 1 theorems proven
        \\  — DRAFT — 1 hole(s) unfilled (aspirational; the result is conditional on them): zeroIsEven; re-run `2b4m check` (no --draft) once filled.
        \\
    );
    // holes are ORTHOGONAL to acceleration: --fast alone still rejects them.
    ctx.fail(&.{ "check", "--fast", "tests/cases/hole.b4m" },
        \\error: 1 hole(s) remain (default mode rejects holes; use --draft while filling them):
        \\  - zeroIsEven  (tests/cases/hole.b4m:10)  — rested on by: restsOnHole
        \\
    );
    // holes propagate transitively across imports: a theorem citing a
    // hole-tainted theorem inherits the hole (blast radius shows both).
    ctx.fail(&.{ "check", "tests/cases/hole_transitive.b4m" },
        \\error: 1 hole(s) remain (default mode rejects holes; use --draft while filling them):
        \\  - zeroIsEven  (tests/cases/hole.b4m:10)  — rested on by: restsOnHole, transitiveHole
        \\
    );

    // USE-ALL-FACTS: a proof with a DEAD step — one whose result is never cited by
    // any later step nor the conclusion — is rejected (a proof must use every fact
    // it introduces).
    ctx.fail(&.{ "check", "tests/cases/use_all_facts_bad.b4m" },
        \\tests/cases/use_all_facts_bad.b4m:12:4: error: unused fact: step 'unused' is never used — no later step or the conclusion cites it (a proof must use every fact it introduces; use --draft while filling in a proof)
        \\
    );
    // --draft disables the check (a WIP proof may have not-yet-wired facts).
    ctx.okSilent(&.{ "check", "--draft", "tests/cases/use_all_facts_bad.b4m" });
    // a proof that USES every fact passes — including facts consumed through
    // non-citation edges: an `unpack` block's existential source, a step that
    // discharges a guarded application's proof obligation (a TCC), and a step fed
    // only as an accelerant (`tautology`) premise.
    ctx.okSilent(&.{ "check", "tests/cases/use_all_facts_ok.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/use_all_facts_unpack_ok.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/use_all_facts_tcc_ok.b4m" });
    ctx.okSilent(&.{ "check", "tests/cases/use_all_facts_accel_chain_ok.b4m" });

    // OBLIGATION DISCHARGE BY IDENTITY (no content search): a guarded application's required
    // proposition must be KNOWN where it is used — taught by an enclosing assume, a prior step,
    // a binder at the refined sort, or a refined result — and is looked up by identity (a
    // compound subject written twice is one term in the hash-consed pool).
    ctx.okSilent(&.{ "check", "tests/cases/tcc_teach.b4m" });
    // a define'd guard and the same guard spelled out as `requires` are ONE proposition; a
    // teaching written either way discharges either.
    ctx.okSilent(&.{ "check", "tests/cases/tcc_teach_define_vs_spelled.b4m" });
    // a GENERATED theorem states its preconditions: an accelerant's synthetic restates the
    // caller's guarded terms, so their obligations become its leading antecedents, discharged
    // at the call site from what the citing proof knows (consuming the teaching step).
    ctx.okSilent(&.{ "check", "tests/cases/tcc_synthetic.b4m" });
    // a schema instantiated at a lambda capturing the caller's `n` while its own proof fixes an
    // `n`: an accelerant step inside mentions both; the synthetic's args name each fvar by its
    // exact hygienic name, so two eigenvariables that display alike are never confused.
    ctx.okSilent(&.{ "check", "tests/cases/schema_lambda_capture.b4m" });
    // SINGLE-THEOREM CHECK: `2b4m check <file> <theorem>` proves only the named theorem (and
    // what it cites) — `good` alone is clean while `broken` (and so the whole file) fails;
    // the theorem follows the file, after any trust words. The entry racks the ParseTask and
    // ONE ProveTask for the name, so a wrong name is that task's own diagnostic.
    ctx.ok(&.{ "check", "tests/cases/single_theorem.b4m", "good" }, "OK: 5 declarations, 1 theorems proven\n");
    ctx.fail(&.{ "check", "tests/cases/single_theorem.b4m", "broken" }, "tests/cases/single_theorem.b4m:16:4: error: step claims 'q' but the axiom derives 'p'\n");
    ctx.fail(&.{ "check", "tests/cases/single_theorem.b4m" }, "tests/cases/single_theorem.b4m:16:4: error: step claims 'q' but the axiom derives 'p'\n");
    ctx.fail(&.{ "check", "tests/cases/single_theorem.b4m", "nosuch" }, "tests/cases/single_theorem.b4m:1:1: error: reference not found: 'nosuch'\n");
    // naming an AXIOM racks its (statement-elaborating) task: nothing is proved, nothing fails.
    ctx.ok(&.{ "check", "tests/cases/single_theorem.b4m", "pq" }, "OK: 5 declarations, 0 theorems proven\n");
    ctx.ok(&.{ "check", "--fast-only", "tautology", "tests/cases/single_theorem.b4m", "good" },
        \\OK: 5 declarations, 1 theorems proven
        \\  — (--fast set given, but no step used a trusted word — fully verified)
        \\
    );
    // (the count tracks std/peano.b4m's declarations, forwarding section included — a
    // single-theorem check still reads the whole imported file's decls.)
    ctx.ok(&.{ "check", "examples/gauss.b4m", "gaussSum" }, "OK: 120 declarations, 1 theorems proven\n");
    // `--axioms`: what a proof BOTTOMS OUT IN, per theorem — `direct` cites one axiom,
    // `viaLemma` inherits a second through the theorem it cites. A HOLE is an axiom to the
    // kernel, so it is listed and MARKED — and only reachable under --draft, since default
    // mode rejects a hole-bearing run before the report.
    ctx.ok(&.{ "check", "tests/cases/axioms_report.b4m", "direct", "--axioms" },
        \\OK: 9 declarations, 1 theorems proven
        \\  — rests on 1 axiom(s):
        \\      pZero  (tests/cases/axioms_report.b4m:10)
        \\
    );
    ctx.ok(&.{ "check", "tests/cases/axioms_report.b4m", "viaLemma", "--axioms" },
        \\OK: 9 declarations, 1 theorems proven
        \\  — rests on 2 axiom(s):
        \\      pZero  (tests/cases/axioms_report.b4m:10)
        \\      pImpliesQ  (tests/cases/axioms_report.b4m:11)
        \\
    );
    ctx.fail(&.{ "check", "tests/cases/hole.b4m", "restsOnHole", "--axioms" },
        \\error: 1 hole(s) remain (default mode rejects holes; use --draft while filling them):
        \\  - zeroIsEven  (tests/cases/hole.b4m:10)  — rested on by: restsOnHole
        \\
    );
    ctx.ok(&.{ "check", "tests/cases/hole.b4m", "restsOnHole", "--axioms", "--draft" },
        \\OK: 6 declarations, 1 theorems proven
        \\  — rests on 1 axiom(s):
        \\      zeroIsEven  (tests/cases/hole.b4m:10)  — HOLE
        \\  — DRAFT — 1 hole(s) unfilled (aspirational; the result is conditional on them): zeroIsEven; re-run `2b4m check` (no --draft) once filled.
        \\
    );
    // DIRECTORY CHECK: every .b4m and .md under the directory, recursively, in ONE engine pass
    // (base.b4m is both a root and sub/uses_base.b4m's import — proved once); a prose .md is a
    // root that parses to nothing; a literate .md counts like any file; one aggregate line.
    ctx.ok(&.{ "check", "tests/cases/dir_ok" }, "OK: 4 files, 13 declarations, 3 theorems proven\n");
    ctx.ok(&.{ "check", "tests/cases/dir_ok", "--axioms" },
        \\OK: 4 files, 13 declarations, 3 theorems proven
        \\  — rests on 2 axiom(s):
        \\      zeroEven  (tests/cases/dir_ok/base.b4m:5)
        \\      pHolds  (tests/cases/dir_ok/literate.md:7)
        \\
    );
    ctx.fail(&.{ "check", "tests/cases/dir_bad" }, "tests/cases/dir_bad/broken.b4m:7:4: error: step claims 'q' but the axiom derives 'p'\n");
    ctx.fail(&.{ "check", "tests/cases/dir_ok", "zeroIsEven" }, "error: a theorem selects within one file; 'tests/cases/dir_ok' is a directory\n");
    // `--library` (a directory): an axiom declared in the directory that no theorem in it
    // rests on FAILS the check; a directory whose every axiom is reached passes; a file is
    // not a library.
    ctx.ok(&.{ "check", "tests/cases/dir_ok", "--library" }, "OK: 4 files, 13 declarations, 3 theorems proven\n");
    ctx.fail(&.{ "check", "tests/cases/dir_library_bad", "--library" },
        \\error: 1 unused axiom(s) — no theorem in the library rests on them:
        \\  - spare  (tests/cases/dir_library_bad/spare.b4m:6)
        \\
    );
    ctx.fail(&.{ "check", "tests/cases/single_theorem.b4m", "--library" }, "error: --library checks a directory (a library is its whole file set); 'tests/cases/single_theorem.b4m' is a file\n");
    // an axiom cited through `[using import(I) ax]` is rested on exactly as through
    // `[by cite I.ax]`: it appears in the citer's `--axioms` report and counts as used for
    // `--library` (regression: the import path once skipped the taint bookkeeping).
    ctx.ok(&.{ "check", "tests/cases/import_axiom_taint/user.b4m", "--axioms" },
        \\OK: 9 declarations, 1 theorems proven
        \\  — rests on 1 axiom(s):
        \\      pZero  (tests/cases/import_axiom_taint/lib.b4m:8)
        \\
    );
    ctx.ok(&.{ "check", "tests/cases/import_axiom_taint", "--library" }, "OK: 2 files, 9 declarations, 1 theorems proven\n");
    // an UNCITED axiom never discharges — the author states it as a step first.
    ctx.fail(&.{ "check", "tests/cases/tcc_uncited_bad.b4m" },
        \\tests/cases/tcc_uncited_bad.b4m:15:11: error: unproved obligation: 'inH(UNIT)'
        \\tests/cases/tcc_uncited_bad.b4m:15:25: error: unproved obligation: 'inH(UNIT)'
        \\
    );
    // knowledge is block-scoped: taught inside an assume, gone after it closes.
    ctx.fail(&.{ "check", "tests/cases/tcc_scope_bad.b4m" },
        \\tests/cases/tcc_scope_bad.b4m:22:11: error: unproved obligation: 'inH(UNIT)'
        \\tests/cases/tcc_scope_bad.b4m:22:25: error: unproved obligation: 'inH(UNIT)'
        \\
    );
    // REGRESSION: a schema `instantiate` step re-enters checkProofSteps (to
    // re-verify the schema body under recheck_schemas), which must NOT wipe the
    // outer proof's accelerant-premise reachability roots. Under --fast the
    // accelerant emits no kernel citation edge, so the root is the only record of
    // an accelerant premise's use; clobbering it falsely flags the premise dead.
    // Must pass under BOTH strict and --fast.
    ctx.okSilent(&.{ "check", "tests/cases/use_all_facts_fast_schema_ok.b4m" });
    ctx.okSilent(&.{ "check", "--fast", "tests/cases/use_all_facts_fast_schema_ok.b4m" });
}
