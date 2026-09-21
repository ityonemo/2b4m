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

    // FILE READS are off-worker by default (Engine/Loader.zig), so every gate above runs the
    // async path. These pin the two OTHER paths so they stay exercised: `--sync-io` is the
    // inline read on the demanding worker (the opt-out and the bisection baseline), and a
    // one-thread ceiling makes the pool REFUSE most submissions, which must fall back to the
    // inline read rather than fail or wedge. A directory sweep, so the reads overlap.
    // A model TRANSFER re-proves a source theorem under the overlay, so its claims are in
    // TARGET terms while any fact the model does not map stays in SOURCE terms. A rejection
    // therefore compares two vocabularies, reported at a line in the SOURCE file — which read
    // as a remapping BUG until the `Model@theorem` prefix made the transfer visible. Pin it.
    ctx.fail(&.{ "check", "tests/cases/model_transfer_label/transfer.bpa" },
        \\tests/cases/model_transfer_label/source.bpa:12:4: error: M@srcPlain: step claims 'forall x: Grp; op(x, E) = x' but the axiom derives 'forall x: SrcVal; scomb(x, SRCE) = x'
        \\
    );

    ctx.okSilent(&.{ "check", "tests/cases/transfer_race", "--sync-io" });
    ctx.okSilent(&.{ "check", "tests/cases/transfer_race", "--io-threads=1" });
    // `--io-delay` is honoured on every path (the ring spends it as a linked timeout whose
    // expiry must not break the chain — it did, once); a small delay so the gate stays quick.
    ctx.okSilent(&.{ "check", "tests/cases/transfer_race", "--io-delay=1000" });
    ctx.okSilent(&.{ "check", "tests/cases/transfer_race", "--io-delay=1000", "--io-threads=2" });
    // ...and a missing import is diagnosed identically whichever thread met the error (the
    // pool thread records it as data; the resumed task diagnoses at the import token).
    const import_missing_diag =
        \\tests/cases/imports/missing_import.bpa:4:18: error: cannot open 'tests/cases/imports/nope.bpa': file not found
        \\tests/cases/imports/missing_import.bpa:10:26: error: reference not found: 'reflexive'
        \\
    ;
    ctx.fail(&.{ "check", "tests/cases/imports/missing_import.bpa", "--sync-io" }, import_missing_diag);
    ctx.fail(&.{ "check", "tests/cases/imports/missing_import.bpa", "--io-threads=1" }, import_missing_diag);

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

    // A CITATION CYCLE is a hard error naming every participant. Before this, the engine
    // parked both proofs, drained its queue and returned as if quiescent — `OK: 0 theorems
    // proven`, exit 0 — so a theorem that could never be proved read as success.
    ctx.fail(&.{ "check", "tests/cases/cycle_two.bpa" },
        \\tests/cases/cycle_two.bpa:13:9: error: 'first' is part of a citation cycle (first, second) — each proof waits on the next, so none can be proved
        \\tests/cases/cycle_two.bpa:20:9: error: 'second' is part of a citation cycle (first, second) — each proof waits on the next, so none can be proved
        \\
    );
    ctx.fail(&.{ "check", "tests/cases/cycle_three.bpa" },
        \\tests/cases/cycle_three.bpa:7:9: error: 'one' is part of a citation cycle (one, two, three) — each proof waits on the next, so none can be proved
        \\tests/cases/cycle_three.bpa:14:9: error: 'two' is part of a citation cycle (one, two, three) — each proof waits on the next, so none can be proved
        \\tests/cases/cycle_three.bpa:21:9: error: 'three' is part of a citation cycle (one, two, three) — each proof waits on the next, so none can be proved
        \\
    );
    // ...but cyclic FILE IMPORTS stay legal — only the PROOF graph must be acyclic.
    ctx.okSilent(&.{ "check", "tests/cases/imports/cycle_a.bpa" });
    for ([_][]const u8{ "tests/cases/cycle_two.bpa", "tests/cases/cycle_three.bpa" }) |path| {
        ctx.okSilent(&.{ "fmt", "--check", path });
    }
}
