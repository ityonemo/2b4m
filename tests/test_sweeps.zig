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
}
