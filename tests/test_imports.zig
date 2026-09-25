//! Integration gates — multi-file checking: import resolution, the trust model, and the --fast trust flags (--fast / --fast-only / --fast-except).
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

    // directory boundaries: subdir import chaining to a parent-dir import
    ctx.okSilent(&.{ "check", "tests/cases/imports/chain.b4m" });

    // diamond imports + re-export: one lib, two hops, same entities
    ctx.okSilent(&.{ "check", "tests/cases/imports/diamond.b4m" });

    // guards travel across imports
    ctx.fail(&.{ "check", "tests/cases/imports/guarded_bad.b4m" }, "tests/cases/imports/guarded_bad.b4m:7:5: error: unproved obligation: 'Z != Z'\n");

    // a missing import file is a clean diagnostic at the import site
    // an import is READ by its own ParseTask when first cited into: the missing file is
    // reported at the import token that named it, and the citation then misses its fact.
    ctx.fail(&.{ "check", "tests/cases/imports/missing_import.b4m" },
        \\tests/cases/imports/missing_import.b4m:4:18: error: cannot open 'tests/cases/imports/nope.b4m': file not found
        \\tests/cases/imports/missing_import.b4m:10:26: error: reference not found: 'reflexive'
        \\
    );

    // a namespace name collides with a local declaration
    ctx.fail(&.{ "check", "tests/cases/imports/collide.b4m" }, "tests/cases/imports/collide.b4m:3:8: error: duplicate declaration of 'lib'\n");

    // `--fast-only import` trusts the import CITATION (admits the cross-file `using import`
    // step by α-matching the cited statement, no re-derivation here). peano-imports declares
    // ONE theorem (addStillCommutes); the demand engine counts only THIS file's theorems (the
    // 6 in the imported peano.b4m are dependencies, not this file's — the old eager engine's
    // transitive "7" was the whole dependency closure).
    ctx.ok(&.{ "check", "--fast-only", "import", "examples/peano-imports.b4m" },
        \\OK: 24 declarations, 1 theorems proven
        \\  — NOT FULLY VERIFIED: 1 theorem(s) accelerated (admitted, not proved): import
        \\
    );

    // --fast (trust everything) admits the same import step; the disclosure names the word.
    ctx.ok(&.{ "check", "--fast", "examples/peano-imports.b4m" },
        \\OK: 24 declarations, 1 theorems proven
        \\  — NOT FULLY VERIFIED: 1 theorem(s) accelerated (admitted, not proved): import
        \\
    );

    // trust semantics: importing an INCORRECT theorem is caught EVEN WITH `import` trusted.
    // The demand engine re-checks any imported theorem a proof actually demands (trusting the
    // `import` word admits the citation SHAPE, not the imported proof's content) — so the
    // broken library proof (`A = A` claimed as `A = B`) fails regardless of the flag. There is
    // no longer a blind "trust imported proofs" escape (the old --faster).
    ctx.fail(&.{ "check", "--fast-only", "import", "tests/cases/imports/trusts_broken.b4m" },
        \\tests/cases/imports/broken_lib.b4m:9:4: error: proof concludes 'A = A' but the theorem states 'A = B'
        \\
    );

    // ...and the DEFAULT (strict) catches it the same way.
    ctx.fail(&.{ "check", "tests/cases/imports/trusts_broken.b4m" },
        \\tests/cases/imports/broken_lib.b4m:9:4: error: proof concludes 'A = A' but the theorem states 'A = B'
        \\
    );

    // the three --fast modes are mutually exclusive.
    ctx.fail(&.{ "check", "--fast", "--fast-except", "import", "examples/peano-imports.b4m" }, "error: at most one of --fast / --fast-only / --fast-except\n");

    ctx.okSilent(&.{ "check", "tests/cases/imports/uses.b4m" });

    // `using import(I) thm` — cite an imported theorem across the file boundary via the
    // import accelerant (the explicit cross-file citation seam, mirroring `using model(M)`).
    ctx.okSilent(&.{ "check", "tests/cases/imports/import_accel.b4m" });

    // CYCLIC FILE IMPORTS are now allowed (architecture refactor: file graph may
    // cycle; proof-graph acyclicity is the separate, proof-time concern). cycle_a and
    // cycle_b mutually import each other and declare sorts A/B — no proof cycle, so it
    // checks green. The engine-driven loader assigns each file its FileId at DISCOVERY
    // (before parse), so a back-reference resolves to the existing id — cycles just work.
    ctx.okSilent(&.{ "check", "tests/cases/imports/cycle_a.b4m" });

    ctx.fail(&.{ "check", "tests/cases/imports/bad_alias.b4m" }, "tests/cases/imports/bad_alias.b4m:4:14: error: 'lib.NIL' is not a sort\n");

    ctx.fail(&.{ "check", "tests/cases/imports/unknown_ns.b4m" }, "tests/cases/imports/unknown_ns.b4m:4:10: error: reference not found: 'ghost'\n");
}
