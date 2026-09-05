//! Integration gates — the `bpa query` subcommands (outline, theorem, whereis, search, uses, accelerated).
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
    // `query outline <file> <theorem>`: the proof skeleton — bare labels,
    // with a header on each block opener (fix / assume / unpack / case).
    ctx.ok(&.{ "query", "outline", "tests/cases/outline.bpa", "everyoneIsQ" },
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
    ctx.ok(&.{ "query", "outline", "tests/cases/outline.bpa" },
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
    ctx.fail(&.{ "query", "outline", "tests/cases/outline.bpa", "noSuchThing" }, "error: no theorem 'noSuchThing' in this file\n");

    // `query claims <file> <theorem>`: the SAME skeleton as outline, but each
    // step shows its CLAIM FORMULA instead of its label (block openers keep their
    // fix / assume / case headers). Same proof as the outline gate above.
    ctx.ok(&.{ "query", "claims", "tests/cases/outline.bpa", "everyoneIsQ" },
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
    ctx.ok(&.{ "query", "claims", "tests/cases/query_claims_schema.bpa", "everythingP" },
        \\schema everythingP
        \\  fix n
        \\    forall m: Nat; P(m)
        \\    P(n)
        \\  forall n: Nat; P(n)
        \\
    );

    // a missing theorem is the same located error as outline (exit 1).
    ctx.fail(&.{ "query", "claims", "tests/cases/outline.bpa", "noSuchThing" }, "error: no theorem 'noSuchThing' in this file\n");

    // `query uses <file>`: per-proof rule tally + external citations. The
    // refs that are the proof's OWN labels are excluded from `cites`; the
    // axioms/theorems it pulls in are listed.
    ctx.ok(&.{ "query", "uses", "tests/cases/outline.bpa" },
        \\theorem everyoneIsQ
        \\  rules: axiom×2 forall_elim×2 hypothesis×2 modus_ponens forall_intro
        \\  cites: either pImpliesQ
        \\
    );

    // `debug taint <file>`: a proof with no accelerated tactic reports that
    // every step is kernel-checked.
    ctx.ok(&.{ "debug", "taint", "tests/cases/outline.bpa" }, "no accelerated tactics — every step is kernel-checked\n");

    // `debug taint <file>`: accelerated tactics flagged at file:line:col with
    // the rule name — here both `assoc_quantified` and `assoc` (the quantified
    // variant runs the same accelerated core).
    ctx.ok(&.{ "debug", "taint", "tests/cases/assoc.bpa" },
        \\theorem reassoc1
        \\  tests/cases/assoc.bpa:19:12: assoc_quantified
        \\
        \\theorem reassoc2
        \\  tests/cases/assoc.bpa:28:12: assoc_quantified
        \\
        \\theorem reassoc3
        \\  tests/cases/assoc.bpa:45:28: assoc
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
        \\        [by implies_intro given-inductive-hypothesis]
        \\    }
        \\  @induction-step-for-all-k |
        \\    forall k: Nat; add(k, ZERO) = k -> add(succ(k), ZERO) = succ(k)
        \\    [by forall_intro induction-step]
        \\
        \\  @conclusion |
        \\    forall n: Nat; add(n, ZERO) = n
        \\    [using instantiation induction((fun k: Nat => add(k, ZERO) = k)) base-case induction-step-for-all-k]
        \\qed
        \\
    ;

    // The synthetic theorem `simplify` produced for the ground `[using simplify
    // addSuccLeft addZeroLeft]`: context-free (both cited axioms closed as
    // premises), proof = assume both, then the reflexivity+forall_elim+rewrite
    // certificate, closed by implies_intro. Fresh legal labels (s*/b*) so the
    // reprint is valid bpa — it round-trips through `bpa check`.
    const debug_accelerant_text =
        \\theorem simplify: (forall a: Nat; forall b: Nat; add(succ(a), b) = succ(add(a, b))) -> (forall b: Nat; add(ZERO, b) = b) -> add(succ(ZERO), succ(ZERO)) = succ(succ(ZERO))
        \\proof
        \\  @b2 |
        \\    assume forall a: Nat; forall b: Nat; add(succ(a), b) = succ(add(a, b)) {
        \\    @s1 |
        \\      forall a: Nat; forall b: Nat; add(succ(a), b) = succ(add(a, b))
        \\      [by hypothesis b2]
        \\    @b3 |
        \\      assume forall b: Nat; add(ZERO, b) = b {
        \\      @s2 |
        \\        forall b: Nat; add(ZERO, b) = b
        \\        [by hypothesis b3]
        \\      @s3 |
        \\        add(succ(ZERO), succ(ZERO)) = add(succ(ZERO), succ(ZERO))
        \\        [by reflexivity]
        \\      @s4 |
        \\        forall b: Nat; add(succ(ZERO), b) = succ(add(ZERO, b))
        \\        [by forall_elim(ZERO) s1]
        \\      @s5 |
        \\        add(succ(ZERO), succ(ZERO)) = succ(add(ZERO, succ(ZERO)))
        \\        [by forall_elim(succ(ZERO)) s4]
        \\      @s6 |
        \\        add(succ(ZERO), succ(ZERO)) = succ(add(ZERO, succ(ZERO)))
        \\        [by rewrite s5 s3]
        \\      @s7 |
        \\        add(ZERO, succ(ZERO)) = succ(ZERO)
        \\        [by forall_elim(succ(ZERO)) s2]
        \\      @s8 |
        \\        add(succ(ZERO), succ(ZERO)) = succ(succ(ZERO))
        \\        [by rewrite s7 s6]
        \\      }
        \\    @s9 |
        \\      (forall b: Nat; add(ZERO, b) = b) -> add(succ(ZERO), succ(ZERO)) = succ(succ(ZERO))
        \\      [by implies_intro b3]
        \\    }
        \\  @s10 |
        \\    (forall a: Nat; forall b: Nat; add(succ(a), b) = succ(add(a, b))) -> (forall b: Nat; add(ZERO, b) = b) -> add(succ(ZERO), succ(ZERO)) = succ(succ(ZERO))
        \\    [by implies_intro b2]
        \\qed
        \\
    ;

    ctx.ok(&.{ "query", "theorem", "std/peano.bpa", "addZeroRight" }, std_theorem_text);

    // `debug accelerant <file> <line>`: reprint, as valid bpa source, the
    // synthetic theorem the accelerant step on that line produced (statement +
    // proof). The ground `simplify` on line 15 of the fixture has no
    // eigenvariables or premises, so its synthetic theorem's statement is the
    // bare equation; the proof is the reflexivity+rewrite chain simplify built.
    // (RED: locked to the renderer's real output once GREEN.)
    ctx.ok(&.{ "debug", "accelerant", "tests/cases/debug_accelerant.bpa", "15" }, debug_accelerant_text);

    // `debug accelerant` resolves a step inside a proof-carrying SCHEMA (not just
    // plain theorems) and reprints its accelerant synthetic — the opaque-param
    // wellformedness self-check already emitted it. Exit 0 = the selector found
    // the schema step and reprinted (regression guard for the `.schema` arm in
    // declSteps/declName).
    ctx.okSilent(&.{ "debug", "accelerant", "tests/cases/schema_accelerant_polynomial.bpa", "polySchema", "poly-step" });

    // `debug accelerant` on an `arithmetic … fallback(<thm>)` step (certifiers
    // DECLINED, so the manual theorem is the proof): there is no synthetic to
    // reprint — say so and NAME the fallback, not the generic "no accelerant here".
    ctx.fail(&.{ "debug", "accelerant", "tests/cases/cooper_gap.bpa", "sumParity", "conclusion" }, "error: proof by fallback: this `arithmetic` step is discharged by the manual theorem 'provedHere' (the certifiers declined), so there is no accelerant synthetic to reprint\n");

    // `debug accelerant` on an arithmetic step over a reified SCHEMA PARAMETER
    // passes through the same "unsupported but planned" message (naming the
    // parameter) that `bpa check` gives — no internal-symbol leak.
    ctx.fail(&.{ "debug", "accelerant", "tests/cases/schema_arithmetic_param_bad.bpa", "valArith", "arith-step" }, "tests/cases/schema_arithmetic_param_bad.bpa:20:9: error: arithmetic cannot yet decide this goal over the schema parameter 'k' (reified opaque while the schema's proof is checked). Certifying an arithmetic step over a schema parameter is currently unsupported but planned; use --fast to accept the accelerated verdict\n");

    // an ALIAS (`theorem addZeroRight = peano.addZeroRight` in subtraction)
    // resolves across files to the real proof — identical output.
    ctx.ok(&.{ "query", "theorem", "std/peano-subtraction.bpa", "addZeroRight" }, std_theorem_text);

    // a missing theorem: located error, exit 1
    ctx.fail(&.{ "query", "theorem", "std/peano.bpa", "noSuchThing" }, "error: no theorem 'noSuchThing' in this file\n");

    // `--sig`: just the statement, wrap-collapsed to one line, alias-
    // followed. `induction` wraps across two lines in the source.
    ctx.ok(&.{ "query", "theorem", "std/peano.bpa", "induction", "--sig" }, "axiom induction(prop: Nat -> Prop): prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)\n");

    // `query whereis <file> <ident>`: trace an alias across files to its
    // origin. Pinned to real std (brittle by design). `sub` is a func
    // aliased in parity from subtraction.
    ctx.ok(&.{ "query", "whereis", "std/peano-parity.bpa", "sub" },
        \\sub
        \\  std/peano-parity.bpa:19:  func sub = subtraction.sub
        \\  std/peano-subtraction.bpa:38:  func sub(a: Nat, b: Nat): Nat  [origin]
        \\
    );

    // an import namespace resolves to the imported file as its origin.
    ctx.ok(&.{ "query", "whereis", "std/peano-parity.bpa", "peano_divides" },
        \\peano_divides
        \\  std/peano-parity.bpa:10:  import peano_divides <<< "std/peano-divides.bpa"
        \\  std/peano-divides.bpa  [origin: imported file]
        \\
    );

    // an unknown identifier: located error, exit 1
    ctx.fail(&.{ "query", "whereis", "std/peano.bpa", "noSuchName" },
        \\noSuchName
        \\  error: no declaration named 'noSuchName' in std/peano.bpa
        \\
    );

    // `query search <file> <query>`: fuzzy match over theorem/axiom names +
    // statements. Both "cancel"-named decls match; ranked, one-line sigs.
    ctx.ok(&.{ "query", "search", "tests/cases/search_target.bpa", "cancel" },
        \\tests/cases/search_target.bpa:13:  axiom cancelAxiom: forall c, a, b: Nat; add(c, a) = add(c, b) -> a = b
        \\tests/cases/search_target.bpa:16:  theorem addCancelLeft: forall c, a, b: Nat; add(c, a) = add(c, b) -> a = b
        \\
    );

    // no match: message + exit 1
    ctx.fail(&.{ "query", "search", "tests/cases/search_target.bpa", "zzznope" }, "no theorem or axiom matching 'zzznope'\n");
}
