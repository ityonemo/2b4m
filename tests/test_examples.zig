//! Integration gates — the examples/ corpus (peano, gauss, euclid, sqrt2, literate).
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

    // the living demo: automation-assisted PA — simplify inside the
    // inductions and arithmetic certificates throughout. Since Cooper-
    // --fast = DECIDE only: each accelerant consults its procedure (rejecting a
    // false goal) but emits NO kernel-checked theorem, disclosing itself as
    // accelerated instead. simplify (and arithmetic's certifiers) therefore taint
    // here rather than emitting their chains; all six still report proven, and
    // the banner fires. Under the default mode below they build kernel-checked
    // certificates (no acceleration).
    ctx.ok(&.{ "check", "--fast", "examples/peano.bpa" },
        \\OK: 18 declarations, 6 theorems proven
        \\  — NOT FULLY VERIFIED: 6 theorem(s) accelerated (admitted, not proved): simplify, arithmetic
        \\
    );

    // ...and under the DEFAULT (verify everything) it is now proven with no acceleration too: the
    // evenOrOdd accelerated step (∀∃, Cooper-QE) certifies via the cooper link's
    // synthesized induction (period-2 parity split), so all six theorems are
    // proven with no acceleration.
    ctx.okSilent(&.{ "check", "examples/peano.bpa" });

    // the by-hand twin: every induction case in primitive rules
    ctx.okSilent(&.{ "check", "examples/peano-pure.bpa" });

    // the incorrect-proof showcase: three classic mistakes, three exact
    // diagnostics (this file is documentation; its output is the contract)
    ctx.fail(&.{ "check", "examples/incorrect.bpa" },
        \\examples/incorrect.bpa:39:41: error: modus_ponens: expected antecedent 'raining', got 'wet'
        \\examples/incorrect.bpa:61:4: error: step claims 'forall n: Nat; is_zero(n)' but forall_intro derives 'forall n: Nat; is_zero(ZERO)'
        \\examples/incorrect.bpa:77:5: error: unproved obligation: 'ZERO != ZERO'
        \\
    );

    // Gauss's summation formula, by hand, proven over the imported base
    ctx.okSilent(&.{ "check", "examples/gauss-pure.bpa" });

    // the automation-assisted twin: `ac` replaces the by-hand exchange
    // lemma, still proven
    ctx.okSilent(&.{ "check", "examples/gauss.bpa" });

    // Euclid's algorithm from a consumer's view: import the verified gcd
    // library and cite its correctness theorems to derive concrete facts
    ctx.okSilent(&.{ "check", "examples/euclid.bpa" });

    ctx.okSilent(&.{ "check", "examples/euclid-compute.bpa" });

    // √2 is irrational (stated over ℕ), proven — the headline result.
    ctx.okSilent(&.{ "check", "examples/sqrt2.bpa" });

    // literate: `check` on a .md checks its ```bpa blocks (prose masked).
    ctx.okSilent(&.{ "check", "examples/literate.md" });
}
