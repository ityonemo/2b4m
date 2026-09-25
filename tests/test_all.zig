//! Aggregates every integration-test group. build.zig calls this one
//! `addTests`, which fans out to each subject file. Gates spawn the built
//! `2b4m` binary and assert stdout / stderr / exit against goldens.

const std = @import("std");

const cli = @import("test_cli.zig");
const tactics = @import("test_tactics.zig");
const stdlib = @import("test_std.zig");
const aata = @import("test_aata.zig");
const examples = @import("test_examples.zig");
const query = @import("test_query.zig");
const imports = @import("test_imports.zig");
const sweeps = @import("test_sweeps.zig");

pub fn addTests(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    test_step: *std.Build.Step,
) void {
    cli.addTests(b, exe, test_step);
    tactics.addTests(b, exe, test_step);
    stdlib.addTests(b, exe, test_step);
    aata.addTests(b, exe, test_step);
    examples.addTests(b, exe, test_step);
    query.addTests(b, exe, test_step);
    imports.addTests(b, exe, test_step);
    sweeps.addTests(b, exe, test_step);
}
