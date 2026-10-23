//! DIRECTORY SWEEPS: the whole corpus checked as ONE engine pass, the way `2b4m check <dir>`
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
    for ([_][]const u8{ "tests/cases/transfer_race/base.b4m", "tests/cases/transfer_race/theory.b4m", "tests/cases/transfer_race/concrete.b4m" }) |path| {
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
    ctx.fail(&.{ "check", "tests/cases/model_transfer_label/transfer.b4m" },
        \\tests/cases/model_transfer_label/source.b4m:12:4: error: M@srcPlain: step claims 'forall x: Grp; op(x, E) = x' but the axiom derives 'forall x: SrcVal; scomb(x, SRCE) = x'
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
        \\tests/cases/imports/missing_import.b4m:4:18: error: cannot open 'tests/cases/imports/nope.b4m': file not found
        \\tests/cases/imports/missing_import.b4m:10:26: error: reference not found: 'reflexive'
        \\
    ;
    ctx.fail(&.{ "check", "tests/cases/imports/missing_import.b4m", "--sync-io" }, import_missing_diag);
    ctx.fail(&.{ "check", "tests/cases/imports/missing_import.b4m", "--io-threads=1" }, import_missing_diag);

    // `--trace-facts` runs to completion and leaves the verdict alone. Its text carries task
    // numbers, so the stdout verdict is pinned exactly and the stderr trace only by its
    // footer (a checked run must state SOME expectation for a stream it writes to).
    const traced = ctx.run(&.{ "check", "--trace-facts", "tests/cases/single_theorem.b4m", "good" });
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
        \\      holeAlpha  (tests/cases/holes_many.b4m:18)  — HOLE
        \\      holeBravo  (tests/cases/holes_many.b4m:19)  — HOLE
        \\      holeCharlie  (tests/cases/holes_many.b4m:20)  — HOLE
        \\      holeDelta  (tests/cases/holes_many.b4m:21)  — HOLE
        \\  — DRAFT — 4 hole(s) unfilled (aspirational; the result is conditional on them): holeAlpha holeBravo holeCharlie holeDelta; re-run `2b4m check` (no --draft) once filled.
        \\
    ;
    ctx.ok(&.{ "check", "tests/cases/holes_many.b4m", "--draft", "--axioms" }, holes_report);
    for ([_][]const u8{ "--chaos=1", "--chaos=7", "--chaos=42", "--chaos=99" }) |seed| {
        ctx.ok(&.{ "check", seed, "tests/cases/holes_many.b4m", "--draft", "--axioms" }, holes_report);
    }
    // …and A SEED MUST REPLAY. The sweep above pins the VERDICT across seeds, which is the
    // determinism contract, but it cannot see whether a given seed reproduces its own
    // SCHEDULE — and for a long time it did not: a seed only picks among the tasks that are
    // RUNNABLE, while the worker count and ASYNC READ COMPLETION decided which those were.
    // `--chaos` therefore now implies `-j1 --sync-io` (`Verify.effectiveWorkers` /
    // `effectiveSyncIo`). The witness is the `--trace-facts` CITATION COUNT: it counts work
    // the demand engine actually did, so a schedule that differs between runs moves it.
    // Pre-fix, `std/counted.b4m` at one seed gave 3857/3857/3875; the same run repeated
    // below must agree with itself. (`holes_many.b4m` is too small to vary — 99 citations at
    // every seed — which is exactly why the sweep above never caught this.)
    //
    // The fixture is a real witness because its count DOES move with the seed —
    // 2530/2418/2654/2374 at seeds 1/7/42/99 — so pinning one seed asserts replay rather
    // than merely asserting a constant. A regression that reintroduces async reads or extra
    // workers under chaos makes this flaky, which is the intended signal.
    for (0..3) |_| {
        const r = ctx.run(&.{ "check", "--chaos=7", "--trace-facts", "tests/cases/chaos_replay.b4m", "--axioms" });
        r.expectStdErrMatch("--- fact resolution trace (2418 citations) ---");
        r.expectExitCode(0);
    }
    ctx.okSilent(&.{ "fmt", "--check", "tests/cases/holes_many.b4m" });

    // A CITATION CYCLE is a hard error naming every participant. Before this, the engine
    // parked both proofs, drained its queue and returned as if quiescent — `OK: 0 theorems
    // proven`, exit 0 — so a theorem that could never be proved read as success.
    ctx.fail(&.{ "check", "tests/cases/cycle_two.b4m" },
        \\tests/cases/cycle_two.b4m:13:9: error: 'first' is part of a citation cycle (first, second) — each proof waits on the next, so none can be proved
        \\tests/cases/cycle_two.b4m:20:9: error: 'second' is part of a citation cycle (first, second) — each proof waits on the next, so none can be proved
        \\
    );
    ctx.fail(&.{ "check", "tests/cases/cycle_three.b4m" },
        \\tests/cases/cycle_three.b4m:7:9: error: 'one' is part of a citation cycle (one, two, three) — each proof waits on the next, so none can be proved
        \\tests/cases/cycle_three.b4m:14:9: error: 'two' is part of a citation cycle (one, two, three) — each proof waits on the next, so none can be proved
        \\tests/cases/cycle_three.b4m:21:9: error: 'three' is part of a citation cycle (one, two, three) — each proof waits on the next, so none can be proved
        \\
    );
    // ...but cyclic FILE IMPORTS stay legal — only the PROOF graph must be acyclic.
    ctx.okSilent(&.{ "check", "tests/cases/imports/cycle_a.b4m" });
    for ([_][]const u8{ "tests/cases/cycle_two.b4m", "tests/cases/cycle_three.b4m" }) |path| {
        ctx.okSilent(&.{ "fmt", "--check", path });
    }
}
