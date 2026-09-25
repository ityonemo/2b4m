//! Shared context + declarative helpers for the integration gates.
//!
//! Each gate spawns the built `2b4m` binary with some arguments and asserts its
//! stdout / stderr / exit code against goldens. The raw `b.addRunArtifact` form
//! is 6–8 lines of boilerplate per gate; these helpers collapse a gate to a
//! single call:
//!
//!   ctx.okSilent(&.{ "check", "std/peano.b4m" });               // checks OK, exit 0
//!   ctx.fail(&.{ "check", "tests/cases/mp_bad.b4m" }, "…:16:22: error: …\n");
//!
//! Prefer `okSilent` for "this file checks" gates — do NOT pin declaration/theorem
//! COUNTS in the golden (they churn on every edit and are noise, not a regression
//! signal). `ok` with a full "OK: …" golden is reserved for gates that assert a
//! meaningful BANNER (the `(N accelerated: …)` / `NOT FULLY VERIFIED` disclosure),
//! where the count rides along harmlessly.
//!
//! `ok` asserts (stdout == given, stderr == "", exit 0); `fail` asserts
//! (stderr == given, exit 1) and leaves stdout unchecked; `okCode` is `ok` with
//! an explicit exit code (the 0-theorems-proven warning gates print an OK line
//! yet exit 1); `okSilent` asserts (stderr == "", exit 0) with no stdout check
//! (fmt --check, decls-only elaboration); `run` returns the raw Run for the rare
//! gate that needs a bespoke assertion.
//!
//! NOTE ordering trap: `expectStdOutEqual` auto-adds an `exited == 0` term check
//! when none exists yet, so `expectExitCode` MUST be set first. `okCode` does so.

const std = @import("std");
const Run = std.Build.Step.Run;

const Ctx = @This();

b: *std.Build,
exe: *std.Build.Step.Compile,
test_step: *std.Build.Step,

pub fn init(b: *std.Build, exe: *std.Build.Step.Compile, test_step: *std.Build.Step) Ctx {
    return .{ .b = b, .exe = exe, .test_step = test_step };
}

/// A run of the built `2b4m` with `args`, pinned to the repo root and always
/// re-executed (paths are not tracked as inputs), wired into the test step.
pub fn run(self: Ctx, args: []const []const u8) *Run {
    const r = self.b.addRunArtifact(self.exe);
    r.has_side_effects = true;
    r.setCwd(self.b.path("."));
    r.addArgs(args);
    self.test_step.dependOn(&r.step);
    return r;
}

/// Success: stdout == `stdout`, stderr == "", exit 0.
pub fn ok(self: Ctx, args: []const []const u8, stdout: []const u8) void {
    const r = self.run(args);
    r.expectStdErrEqual("");
    r.expectStdOutEqual(stdout);
    r.expectExitCode(0);
}

/// Like `ok` but with an explicit exit code (e.g. the 0-theorems warning gates
/// print an OK line to stdout yet exit 1). Exit check precedes the stdout check
/// so the latter does not auto-assert exit 0.
pub fn okCode(self: Ctx, args: []const []const u8, stdout: []const u8, code: u8) void {
    const r = self.run(args);
    r.expectStdErrEqual("");
    r.expectExitCode(code);
    r.expectStdOutEqual(stdout);
}

/// Success with no stdout assertion: stderr == "", exit 0 (fmt --check, a
/// decls-only file that elaborates cleanly but proves nothing to pin).
pub fn okSilent(self: Ctx, args: []const []const u8) void {
    const r = self.run(args);
    r.expectStdErrEqual("");
    r.expectExitCode(0);
}

/// Failure: stderr == `stderr`, exit 1; stdout unchecked.
pub fn fail(self: Ctx, args: []const []const u8, stderr: []const u8) void {
    const r = self.run(args);
    r.expectStdErrEqual(stderr);
    r.expectExitCode(1);
}
