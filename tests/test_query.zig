//! Integration gates — the `2b4m query` subcommands (outline, theorem, whereis, search, uses, accelerated).
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
    // `query outline <file> <theorem>`: the proof skeleton — bare labels,
    // with a header on each block opener (fix / assume / unpack / case).
    ctx.ok(&.{ "query", "outline", "tests/cases/cli/outline.b4m", "everyoneIsQ" },
        \\theorem everyoneIsQ
        \\  generalize-n  fix n
        \\    cases
        \\    p-or-q
        \\    conclusion-inner  case p-or-q
        \\      from-p  assume p(n)
        \\        p-holds
        \\        p-gives-q
        \\        p-gives-q-at-n
        \\        q-from-p
        \\      from-q  assume q(n)
        \\        q-holds
        \\  conclusion
        \\
    );

    // no theorem argument: outline every proof in the file (here, the one)
    ctx.ok(&.{ "query", "outline", "tests/cases/cli/outline.b4m" },
        \\theorem everyoneIsQ
        \\  generalize-n  fix n
        \\    cases
        \\    p-or-q
        \\    conclusion-inner  case p-or-q
        \\      from-p  assume p(n)
        \\        p-holds
        \\        p-gives-q
        \\        p-gives-q-at-n
        \\        q-from-p
        \\      from-q  assume q(n)
        \\        q-holds
        \\  conclusion
        \\
    );

    // a missing theorem is a located error on stderr (exit 1)
    ctx.fail(&.{ "query", "outline", "tests/cases/cli/outline.b4m", "noSuchThing" }, "error: no theorem 'noSuchThing' in this file\n");

    // `query claims <file> <theorem>`: the SAME skeleton as outline, but each
    // step shows its CLAIM FORMULA instead of its label (block openers keep their
    // fix / assume / case headers). Same proof as the outline gate above.
    ctx.ok(&.{ "query", "claims", "tests/cases/cli/outline.b4m", "everyoneIsQ" },
        \\theorem everyoneIsQ
        \\  fix n
        \\    forall m: Nat; p(m) or q(m)
        \\    p(n) or q(n)
        \\    case p-or-q
        \\      assume p(n)
        \\        p(n)
        \\        forall m: Nat; p(m) -> q(m)
        \\        p(n) -> q(n)
        \\        q(n)
        \\      assume q(n)
        \\        q(n)
        \\  forall n: Nat; q(n)
        \\
    );

    // `query claims` on a proof-carrying SCHEMA (`theorem name(param): …`): it is
    // rendered like any proof (labeled `schema`), with the claim formulas of the
    // steps inside its `fix` block — proving `claims` handles schematic theorems.
    ctx.ok(&.{ "query", "claims", "tests/cases/cli/query_claims_schema.b4m", "everythingP" },
        \\schema everythingP
        \\  fix n
        \\    forall m: Nat; P(m)
        \\    P(n)
        \\  forall n: Nat; P(n)
        \\
    );

    // a NULLARY predicate renders with its parens on BOTH sides of a connective —
    // `claims` reproduces the source token span, and a zero-argument call spans only
    // its callee, so the `()` must be taken explicitly (a paren-balance count cannot
    // see them: they sit outside the span).
    ctx.ok(&.{ "query", "claims", "tests/cases/syntax/nullary_pred_parens.b4m", "aNullaryPredChainsThroughModusPonens" },
        \\theorem aNullaryPredChainsThroughModusPonens
        \\  base() -> other()
        \\
    );

    // a missing theorem is the same located error as outline (exit 1).
    ctx.fail(&.{ "query", "claims", "tests/cases/cli/outline.b4m", "noSuchThing" }, "error: no theorem 'noSuchThing' in this file\n");

    // `query uses <file>`: per-proof rule tally + external citations. The
    // refs that are the proof's OWN labels are excluded from `cites`; the
    // axioms/theorems it pulls in are listed.
    ctx.ok(&.{ "query", "uses", "tests/cases/cli/outline.b4m" },
        \\theorem everyoneIsQ
        \\  rules: cite×2 apply_at×2 hypothesis×2 modus_ponens generalize
        \\  cites: either pImpliesQ
        \\
    );

    // REGRESSION: `query uses` on a file carrying definition-block well-formedness sections.
    // `query` parses without an interner, so every `StrId` is `.none` and every name compares
    // EQUAL — which made the section checks (built on name identity) read every call as a
    // self-call and report valid declarations as malformed recursions. `g` here is NOT
    // recursive, so any recursion complaint is the bug returning.
    ctx.ok(&.{ "query", "uses", "tests/cases/cli/query_definition_sections.b4m" },
        \\theorem gAtZero
        \\  rules: definition
        \\  cites: 0 g
        \\
    );

    // `--trace-facts` EXPANDS a schema instance's arguments beneath its hash. The name is a
    // hash of the arguments, so without this a reader can tell two instantiations apart but
    // cannot tell what either one IS. The preimage is in hand at the naming site, so it is
    // printed there — the cheap half of decoding `Schema{hash}`.
    {
        const r = ctx.run(&.{ "check", "--trace-facts", "std/peano.b4m", "addZeroRight" });
        r.expectStdErrMatch("prop := fun k => add(k, ZERO) = k");
        r.expectExitCode(0);
    }

    // `query instance <file> <hash>` — decode a `Schema{hash}` back into the instantiation it
    // names. ONE schema instantiated at TWO arguments gets two distinct hashes; each must
    // recover the argument actually written. That is the whole claim of the subcommand, and it
    // is the test SCHEMA-HASH-DECODE-PLAN.md asks for.
    //
    // The fixture's hashes are STABLE across runs (verified): a declared schema's hash covers
    // only its arguments, where an accelerant-minted name also covers the prover's hygienic
    // fvars and so varies with worker interleaving on a multi-theorem run.
    ctx.ok(&.{ "query", "instance", "tests/cases/schema/query_instance_twice.b4m", "7e823c3f835aa0a3" },
        \\atBoth{7e823c3f835aa0a3}
        \\  schema: atBoth
        \\  in:     ns#46
        \\  t := A
        \\
    );
    ctx.ok(&.{ "query", "instance", "tests/cases/schema/query_instance_twice.b4m", "8740d0f6455bceca" },
        \\atBoth{8740d0f6455bceca}
        \\  schema: atBoth
        \\  in:     ns#46
        \\  t := B
        \\
    );

    // The FULL `Schema{hash}` spelling, as a trace line prints it, resolves identically — a
    // reader pastes what they have rather than editing the braces off.
    ctx.ok(&.{ "query", "instance", "tests/cases/schema/query_instance_twice.b4m", "atBoth{7e823c3f835aa0a3}" },
        \\atBoth{7e823c3f835aa0a3}
        \\  schema: atBoth
        \\  in:     ns#46
        \\  t := A
        \\
    );

    // A hash from a DIFFERENT argument set does not resolve, and says so rather than guessing.
    // Honest degradation is the point: "no match" is itself information (a stale hash, or an
    // instance this run never demanded).
    {
        const r = ctx.run(&.{ "query", "instance", "tests/cases/schema/query_instance_twice.b4m", "deadbeefdeadbeef" });
        r.expectStdErrMatch("no instantiation in this run hashes to 'deadbeefdeadbeef'");
        r.expectExitCode(1);
    }

    // `debug taint <file>`: a proof with no accelerated tactic reports that
    // every step is kernel-checked.
    ctx.ok(&.{ "debug", "taint", "tests/cases/cli/outline.b4m" }, "no accelerated tactics — every step is kernel-checked\n");

    // `debug taint <file>`: accelerated tactics flagged at file:line:col with
    // the rule name — here both `assoc_quantified` and `assoc` (the quantified
    // variant runs the same accelerated core).
    ctx.ok(&.{ "debug", "taint", "tests/cases/tactics/assoc/assoc.b4m" },
        \\theorem reassoc1
        \\  tests/cases/tactics/assoc/assoc.b4m:24:12: assoc_quantified
        \\
        \\theorem reassoc2
        \\  tests/cases/tactics/assoc/assoc.b4m:33:12: assoc_quantified
        \\
        \\theorem reassoc3
        \\  tests/cases/tactics/assoc/assoc.b4m:50:28: assoc
        \\
    );

    // `query theorem <file> <name>`: the full source of the declaration,
    // verbatim — leading doc-comment through `qed`. Pinned to real std
    // (brittle by design: a std edit to this theorem should break here).
    const std_theorem_text =
        \\// Strategy: induction on n with prop(k) := add(k, ZERO) = k.
        \\// (addZeroLeft reduces ZERO on the LEFT; this is the mirror-image fact.)
        \\theorem addZeroRight: forall n: Nat; add(n, ZERO) = n
        \\proof
        \\  // base case: addZeroLeft specialized at b := ZERO
        \\  @base-case |
        \\    add(ZERO, ZERO) = ZERO
        \\    [using simplify addZeroLeft]
        \\
        \\  // inductive step: unfold add on succ(k), then rewrite with the IH
        \\  @induction-step |
        \\    fix k: Nat {
        \\      @given-inductive-hypothesis |
        \\        assume add(k, ZERO) = k {
        \\          @inductive-hypothesis |
        \\            add(k, ZERO) = k
        \\            [by hypothesis given-inductive-hypothesis]
        \\          @succ-case |
        \\            add(succ(k), ZERO) = succ(k)
        \\            [using simplify addSuccLeft inductive-hypothesis]
        \\        }
        \\      @induction-step-at-k |
        \\        add(k, ZERO) = k -> add(succ(k), ZERO) = succ(k)
        \\        [by discharge given-inductive-hypothesis]
        \\    }
        \\  @induction-step-for-all-k |
        \\    forall k: Nat; add(k, ZERO) = k -> add(succ(k), ZERO) = succ(k)
        \\    [by generalize induction-step]
        \\
        \\  @conclusion |
        \\    forall n: Nat; add(n, ZERO) = n
        \\    [using instantiation induction((fun k: Nat => add(k, ZERO) = k)) base-case induction-step-for-all-k]
        \\qed
        \\
    ;

    // The synthetic theorem `simplify` produced for the ground `[using simplify
    // addSuccLeft addZeroLeft]`, reprinted from the very ast.Decl the producer
    // registered: the cited axioms are `cite`d (not hoisted as premises), the
    // producer's own `freshNamed` labels render as kebab labels (`simplify-4`), the
    // `{hash}` name mangle is trimmed. Re-parseable 2b4m.
    const debug_accelerant_text =
        \\theorem simplify: add(succ(ZERO), succ(ZERO)) = succ(succ(ZERO))
        \\proof
        \\  @simplify-4 |
        \\    add(succ(ZERO), succ(ZERO)) = add(succ(ZERO), succ(ZERO))
        \\    [by reflexivity]
        \\  @simplify-5 |
        \\    forall b1: Nat; forall b2: Nat; add(succ(b1), b2) = succ(add(b1, b2))
        \\    [by cite addSuccLeft]
        \\  @simplify-6 |
        \\    forall b1: Nat; add(succ(ZERO), b1) = succ(add(ZERO, b1))
        \\    [by apply_at(ZERO) simplify-5]
        \\  @simplify-7 |
        \\    add(succ(ZERO), succ(ZERO)) = succ(add(ZERO, succ(ZERO)))
        \\    [by apply_at(succ(ZERO)) simplify-6]
        \\  @simplify-8 |
        \\    add(succ(ZERO), succ(ZERO)) = succ(add(ZERO, succ(ZERO)))
        \\    [by rewrite simplify-7 simplify-4]
        \\  @simplify-9 |
        \\    forall b1: Nat; add(ZERO, b1) = b1
        \\    [by cite addZeroLeft]
        \\  @simplify-10 |
        \\    add(ZERO, succ(ZERO)) = succ(ZERO)
        \\    [by apply_at(succ(ZERO)) simplify-9]
        \\  @simplify-11 |
        \\    add(succ(ZERO), succ(ZERO)) = succ(succ(ZERO))
        \\    [by rewrite simplify-10 simplify-8]
        \\qed
        \\
    ;

    ctx.ok(&.{ "query", "theorem", "std/peano.b4m", "addZeroRight" }, std_theorem_text);

    // `debug model <file> <Name>`: a model's mapping surface grouped by source theory, and
    // the CHECKLIST — what that theory declares which this model never mentions. This is the
    // up-front half of the PAINPOINTS.md model-discharge entry: an omitted discharge otherwise
    // surfaces as a sort mismatch inside the source theory's own proof, two files away.
    // The `_ok` fixture's surface is complete, so there is no unmapped/undischarged line.
    ctx.ok(&.{ "debug", "model", "tests/cases/model/composed/composed_ok.b4m" },
        \\model TopIsMid  (tests/cases/model/composed/composed_ok.b4m:18)
        \\
        \\  from middle  <<< tests/cases/model/composed/middle.b4m
        \\    Mid: Top
        \\    MZ: TZ
        \\    mop: top_op
        \\    mopUnitLeft <- topUnitLeft
        \\    mopAssoc <- topAssoc
        \\
    );

    // the same model with its `mopAssoc` discharge REMOVED — the omission the check reports
    // two layers down is named here as a one-line obligation.
    ctx.ok(&.{ "debug", "model", "tests/cases/model/composed/composed_missing_axiom_bad.b4m" },
        \\model TopIsMid  (tests/cases/model/composed/composed_missing_axiom_bad.b4m:14)
        \\
        \\  from middle  <<< tests/cases/model/composed/middle.b4m
        \\    Mid: Top
        \\    MZ: TZ
        \\    mop: top_op
        \\    mopUnitLeft <- topUnitLeft
        \\    — 1 undischarged (<-): mopAssoc
        \\
    );

    // the SYMBOL half of the same defect: an unmapped `:` entry, reported under its own
    // heading because the fix differs (a `:` mapping, not a `<-` discharge).
    ctx.ok(&.{ "debug", "model", "tests/cases/model/composed/composed_missing_symbol_bad.b4m" },
        \\model TopIsMid  (tests/cases/model/composed/composed_missing_symbol_bad.b4m:15)
        \\
        \\  from middle  <<< tests/cases/model/composed/middle.b4m
        \\    Mid: Top
        \\    MZ: TZ
        \\    mopUnitLeft <- topUnitLeft
        \\    mopAssoc <- topAssoc
        \\    — 1 unmapped (:): mop
        \\
    );

    // a GUARDED mapping prints the dischargers it nominates on the `:` line (a refined-sort
    // target takes `TGT(baseFact…)`, a closed operation `F -| closureFact…`) — those facts
    // are part of what the model owes, so a bare "[guarded]" flag would hide them. This
    // model's sources are UNQUALIFIED: it models a theory declared in its own file, so there
    // is no namespace to resolve and the surface is the file already parsed.
    ctx.ok(&.{ "debug", "model", "tests/cases/model/model_overlap_refinement.b4m" },
        \\model PartIsThing  (tests/cases/model/model_overlap_refinement.b4m:87)
        \\
        \\  from this file  (tests/cases/model/model_overlap_refinement.b4m)
        \\    Thing: Part
        \\    UNIT: UNIT   [guarded refined sort: punitIsInPart]
        \\    op: op   [guarded closed operation: partClosedUnderOp]
        \\    opUnitLeft <- opUnitLeft
        \\    opComm <- opComm
        \\
    );

    // a file with no model at all, and a name that is not a model in the file.
    ctx.ok(&.{ "debug", "model", "tests/cases/cli/outline.b4m" }, "tests/cases/cli/outline.b4m: no models\n");
    ctx.fail(&.{ "debug", "model", "tests/cases/model/composed/composed_ok.b4m", "NoSuchModel" }, "error: no model 'NoSuchModel' in tests/cases/model/composed/composed_ok.b4m\n");

    // `debug accelerant <file> <line>`: reprint, as valid 2b4m source, the
    // synthetic theorem the accelerant step on that line produced (statement +
    // proof). The ground `simplify` on line 15 of the fixture has no
    // eigenvariables or premises, so its synthetic theorem's statement is the
    // bare equation; the proof is the reflexivity+rewrite chain simplify built.
    // The reprint is re-parseable: appending it to the fixture's declarations checks clean.
    ctx.ok(&.{ "debug", "accelerant", "tests/cases/cli/debug_accelerant.b4m", "20" }, debug_accelerant_text);

    // `debug accelerant --model <Name>`: a step inside a theorem that is TRANSFERRED produces
    // one synthetic PER SPACE, and the model-space one is what the kernel actually re-checked.
    // Same step, same line, two different reprints: the universe space is in the SOURCE
    // vocabulary (`plus`/`Z`), the model space in the TARGET's (`tplus`/`TZ`). Before the
    // registry was keyed by space, only whichever was scheduled first was reachable.
    ctx.ok(&.{ "debug", "accelerant", "tests/cases/model/accel/model_accel_simplify.b4m", "29" },
        \\theorem simplify: plus(Z, Z) = Z
        \\proof
        \\  @simplify-3 |
        \\    plus(Z, Z) = plus(Z, Z)
        \\    [by reflexivity]
        \\  @simplify-4 |
        \\    forall b1: Src; plus(Z, b1) = b1
        \\    [by cite plusZeroLeft]
        \\  @simplify-5 |
        \\    plus(Z, Z) = Z
        \\    [by apply_at(Z) simplify-4]
        \\  @simplify-6 |
        \\    plus(Z, Z) = Z
        \\    [by rewrite simplify-5 simplify-3]
        \\qed
        \\
    );
    ctx.ok(&.{ "debug", "accelerant", "tests/cases/model/accel/model_accel_simplify.b4m", "29", "--model", "SrcIsGood" },
        \\theorem simplify: tplus(TZ, TZ) = TZ
        \\proof
        \\  @simplify-3 |
        \\    tplus(TZ, TZ) = tplus(TZ, TZ)
        \\    [by reflexivity]
        \\  @simplify-4 |
        \\    forall b1: Tgt; tplus(TZ, b1) = b1
        \\    [by cite plusZeroLeft]
        \\  @simplify-5 |
        \\    tplus(TZ, TZ) = TZ
        \\    [by apply_at(TZ) simplify-4]
        \\  @simplify-6 |
        \\    tplus(TZ, TZ) = TZ
        \\    [by rewrite simplify-5 simplify-3]
        \\qed
        \\
    );

    // the GUARDED half: a transfer onto a refined sort RELATIVIZES, so the model-space
    // synthetic carries a guard premise per binder (`good(p1) ->`). An inspection that
    // printed the unrelativized statement would misreport what was checked.
    ctx.okSilent(&.{ "debug", "accelerant", "tests/cases/model/accel/model_accel_simplify.b4m", "41", "--model", "SrcIsGood" });

    // asking for a space the step did not produce LISTS the ones it did — a reader who gets
    // the tower wrong cannot otherwise discover the right one.
    ctx.fail(&.{ "debug", "accelerant", "tests/cases/cli/debug_accelerant.b4m", "20", "--model", "NoSuchModel" }, "error: no model 'NoSuchModel' in this file\n");

    // `debug accelerant` resolves a step inside a proof-carrying SCHEMA (not just plain
    // theorems) and reprints its accelerant synthetic — the schema's INSTANCE proof (the
    // only gate; there is no decl-time self-check) produced it. Exit 0 = the selector
    // found the schema step and reprinted.
    ctx.okSilent(&.{ "debug", "accelerant", "tests/cases/schema/schema_accelerant_polynomial.b4m", "polySchema", "poly-step" });

    // `debug accelerant` on an `arithmetic … fallback(<thm>)` step (certifiers
    // DECLINED, so the manual theorem is the proof): there is no synthetic to
    // reprint — say so and NAME the fallback, not the generic "no accelerant here".
    ctx.fail(&.{ "debug", "accelerant", "tests/cases/tactics/cooper/cooper_gap.b4m", "sumParity", "conclusion" }, "error: proof by fallback: this `arithmetic` step is discharged by the manual theorem 'provedHere' (the certifiers declined), so there is no accelerant synthetic to reprint\n");

    // `debug accelerant` on a file whose check FAILS passes the check's own located
    // diagnostic through (root path as given on the command line), rather than reprinting
    // anything — here a redundant `fallback(...)` the certifier didn't need.
    ctx.fail(&.{ "debug", "accelerant", "tests/cases/tactics/arithmetic/arithmetic_fallback_redundant_bad.b4m", "twoTimesTwoRedundant", "conclusion" }, "tests/cases/tactics/arithmetic/arithmetic_fallback_redundant_bad.b4m:35:32: error: 'arithmetic' certifies this goal on its own — the fallback 'twoTimesTwoManual' is unnecessary; drop `fallback(twoTimesTwoManual)`\n");

    // an ALIAS (`theorem addZeroRight = peano.addZeroRight` in subtraction)
    // resolves across files to the real proof — identical output.
    ctx.ok(&.{ "query", "theorem", "std/peano/subtraction.b4m", "addZeroRight" }, std_theorem_text);

    // a missing theorem: located error, exit 1
    ctx.fail(&.{ "query", "theorem", "std/peano.b4m", "noSuchThing" }, "error: no theorem 'noSuchThing' in this file\n");

    // `--sig`: just the statement, wrap-collapsed to one line, alias-
    // followed. `induction` wraps across two lines in the source.
    ctx.ok(&.{ "query", "theorem", "std/peano.b4m", "induction", "--sig" }, "axiom induction(prop(Nat)): prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)\n");

    // `query whereis <file> <ident>`: trace an alias across files to its
    // origin. Pinned to real std (brittle by design). `sub` is a func
    // aliased in parity from subtraction.
    ctx.ok(&.{ "query", "whereis", "std/peano/parity.b4m", "sub" },
        \\sub
        \\  std/peano/parity.b4m:19:  oper sub = subtraction.sub
        \\  std/peano/subtraction.b4m:58:  oper sub(a: Nat, b: Nat) => Nat requires ordering.less_or_equal(b, a)  [origin]
        \\
    );

    // an import namespace resolves to the imported file as its origin.
    ctx.ok(&.{ "query", "whereis", "std/peano/parity.b4m", "peano_divides" },
        \\peano_divides
        \\  std/peano/parity.b4m:9:  theory peano_divides <<< "std/peano/divides.b4m"
        \\  std/peano/divides.b4m  [origin: imported file]
        \\
    );

    // an unknown identifier: located error, exit 1
    ctx.fail(&.{ "query", "whereis", "std/peano.b4m", "noSuchName" },
        \\noSuchName
        \\  error: no declaration named 'noSuchName' in std/peano.b4m
        \\
    );

    // `query search <file> <query>`: fuzzy match over theorem/axiom names +
    // statements. Both "cancel"-named decls match; ranked, one-line sigs.
    ctx.ok(&.{ "query", "search", "tests/cases/cli/search_target.b4m", "cancel" },
        \\tests/cases/cli/search_target.b4m:13:  axiom cancelAxiom: forall c, a, b: Nat; add(c, a) = add(c, b) -> a = b
        \\tests/cases/cli/search_target.b4m:19:  theorem addCancelLeft: forall c, a, b: Nat; add(c, a) = add(c, b) -> a = b
        \\
    );

    // no match: message + exit 1
    ctx.fail(&.{ "query", "search", "tests/cases/cli/search_target.b4m", "zzznope" }, "no theorem or axiom matching 'zzznope'\n");

    // `query search <dir>` RECURSES. `sub/uses_base.b4m` appears only if the walk
    // descends — a single-level `iterate()` saw just the top-level files, which made
    // `query search std <term>` blind to `std/group/`, `std/permutation/`, … (most of the
    // library) while the same term found hits in those subdirectories directly. GUIDE
    // advertises "every `.b4m` under it — corpus discovery", so that scope was the one
    // scope that could not see the corpus.
    ctx.ok(&.{ "query", "search", "tests/cases/cli/directory-mode/ok", "even" },
        \\tests/cases/cli/directory-mode/ok/base.b4m:5:  axiom zeroEven: even(ZERO)
        \\tests/cases/cli/directory-mode/ok/base.b4m:10:  theorem zeroIsEven: even(ZERO)
        \\tests/cases/cli/directory-mode/ok/sub/uses_base.b4m:10:  theorem stillEven: even(ZERO)
        \\
    );
}
