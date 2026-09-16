//! DIRECTORY SWEEPS: the whole corpus checked as ONE engine pass, the way `bpa check <dir>`
//! runs it. A sweep proves what per-file gates cannot: every file is a root of the SAME
//! run, so the demand order — the run queue is a stack — is the one a real sweep produces,
//! and order-dependent bugs surface here and nowhere else. The transferred-copy race
//! (a citer's read pass finding a model-transferred theorem claimed-but-unfinished and
//! proceeding to cite the untransferred copy) was RED here and GREEN everywhere else.
const std = @import("std");
const Ctx = @import("Ctx.zig");

pub fn addTests(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    test_step: *std.Build.Step,
) void {
    const ctx = Ctx.init(b, exe, test_step);

    // the standard library as one pass, and as a LIBRARY (every axiom demonstrated).
    ctx.okSilent(&.{ "check", "std" });
    ctx.okSilent(&.{ "check", "std", "--library" });
    // the textbook as one pass (its files are consumers; --library is not its obligation).
    ctx.okSilent(&.{ "check", "aata" });

    // the transferred-copy race in miniature: two re-proofs under one model both need the
    // ONE transferred copy of a theorem their proofs cite; whichever demands it second must
    // WAIT for it, not fall through to the untransferred copy. Order-dependent — this small
    // shape happens to pass either way, so the std sweep above is the gate that catches a
    // regression; this documents the shape and keeps the path exercised.
    ctx.okSilent(&.{ "check", "tests/cases/transfer_race" });
    for ([_][]const u8{ "tests/cases/transfer_race/base.bpa", "tests/cases/transfer_race/theory.bpa", "tests/cases/transfer_race/concrete.bpa" }) |path| {
        ctx.okSilent(&.{ "fmt", "--check", path });
    }

    // `--trace-facts` runs to completion and leaves the verdict alone. Its text carries task
    // numbers, so the stdout verdict is pinned exactly and the stderr trace only by its
    // footer (a checked run must state SOME expectation for a stream it writes to).
    const traced = ctx.run(&.{ "check", "--trace-facts", "tests/cases/single_theorem.bpa", "good" });
    traced.expectStdOutEqual("OK: 5 declarations, 1 theorems proven\n");
    traced.expectStdErrMatch("--- end trace ---\n");
    traced.expectExitCode(0);

    // DETERMINISM: output is a function of (tree, roots), NEVER of scheduling. `--chaos=N`
    // shuffles which runnable task the engine pulls, so pinning ONE golden across several
    // seeds asserts exactly that contract — a report that leaks task order fails here.
    //
    // This fixture is what caught it: four holes reached by four SEPARATE proofs were
    // disclosed in `holes_reached` APPEND order, i.e. whatever order those proofs ran in, so
    // the list came out differently under most seeds. The report sorts by declaration site
    // now. (agents/debug-guide.md shows the wider by-hand sweep over a directory; the corpus
    // is deterministic under chaos today, and this keeps the cheapest witness in the suite.)
    const holes_report =
        \\OK: 12 declarations, 4 theorems proven
        \\  — rests on 4 axiom(s):
        \\      holeAlpha  (tests/cases/holes_many.bpa:18)  — HOLE
        \\      holeBravo  (tests/cases/holes_many.bpa:19)  — HOLE
        \\      holeCharlie  (tests/cases/holes_many.bpa:20)  — HOLE
        \\      holeDelta  (tests/cases/holes_many.bpa:21)  — HOLE
        \\  — DRAFT — 4 hole(s) unfilled (aspirational; the result is conditional on them): holeAlpha holeBravo holeCharlie holeDelta; re-run `bpa check` (no --draft) once filled.
        \\
    ;
    ctx.ok(&.{ "check", "tests/cases/holes_many.bpa", "--draft", "--axioms" }, holes_report);
    for ([_][]const u8{ "--chaos=1", "--chaos=7", "--chaos=42", "--chaos=99" }) |seed| {
        ctx.ok(&.{ "check", seed, "tests/cases/holes_many.bpa", "--draft", "--axioms" }, holes_report);
    }
    ctx.okSilent(&.{ "fmt", "--check", "tests/cases/holes_many.bpa" });
}
