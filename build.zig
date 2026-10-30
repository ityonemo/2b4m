const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    // DEFAULT TO ReleaseFast, not Debug. A Debug build of this project is ~35x slower (see
    // the bench comment below), and nothing in the binary's output reveals its mode, so a
    // Debug default is a trap: you run the corpus, conclude the checker is slow, and
    // restructure your workflow around a number that is purely an artifact of the build.
    //
    // `standardOptimizeOption`'s `preferred_optimize_mode` does NOT do this — it only takes
    // effect under `-Drelease=true`, so bare `zig build` would still be Debug (measured).
    // Hence the explicit override: honour `-Doptimize=<mode>` when given, else ReleaseFast.
    const requested_optimize = b.standardOptimizeOption(.{});
    const optimize: std.builtin.OptimizeMode =
        if (b.user_input_options.get("optimize") != null) requested_optimize else .ReleaseFast;

    // Core library module: all proof-checking logic lives here; main.zig is a thin CLI.
    const mod = b.addModule("b4m", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
    });

    const exe = b.addExecutable(.{
        .name = "2b4m",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "b4m", .module = mod },
            },
        }),
    });
    b.installArtifact(exe);

    const run_step = b.step("run", "Run 2b4m");
    const run_cmd = b.addRunArtifact(exe);
    run_step.dependOn(&run_cmd.step);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_cmd.addArgs(args);

    // Unit tests (library + CLI modules).
    const mod_tests = b.addTest(.{ .root_module = mod });
    const run_mod_tests = b.addRunArtifact(mod_tests);
    const exe_tests = b.addTest(.{ .root_module = exe.root_module });
    const run_exe_tests = b.addRunArtifact(exe_tests);

    const test_step = b.step("test", "Run tests");
    test_step.dependOn(&run_mod_tests.step);
    test_step.dependOn(&run_exe_tests.step);

    // Integration test gates (spawn `2b4m`, assert stdout/stderr/exit) live in
    // tests/ grouped by subject; build.zig stays build configuration.
    //
    // The gates reuse the SAME `exe` as the install step, so they inherit the ReleaseFast
    // default above. A separate Debug test binary was tried and dropped: every gate is an
    // `addRunArtifact` on this exe (tests/Ctx.zig), so a second mode means compiling the
    // whole engine TWICE per `zig build test` — real wall time and real heat on a laptop,
    // bought for safety checks that no gate actually asserts. Reach for Debug explicitly
    // (`zig build test -Doptimize=Debug`) when hunting a leak or an overflow.
    const tests = @import("tests/test_all.zig");
    tests.addTests(b, exe, test_step);

    // `zig build bench` — wall-clock over the real corpus.
    //
    // ALWAYS ReleaseFast, never `optimize`: a Debug build is ~35x slower (the std sweep is
    // 62 s Debug against 1.8 s ReleaseFast), and a benchmark that silently measures Debug
    // produces numbers that send you optimizing the wrong thing. This is why the step
    // builds its own binary instead of reusing `exe`.
    const bench_exe = b.addExecutable(.{
        .name = "2b4m-bench",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = .ReleaseFast,
            .imports = &.{.{ .name = "b4m", .module = mod }},
        }),
    });
    const bench_step = b.step("bench", "Time the corpus (always ReleaseFast)");
    // The two whole-corpus sweeps plus the heaviest single file. (`examples/` is excluded:
    // it carries `incorrect.b4m`, a deliberate negative that exits 1 by design.)
    for ([_][]const []const u8{
        &.{ "check", "std" },
        &.{ "check", "aata" },
        &.{ "check", "std/integer/divides.b4m" },
    }) |argv| {
        const r = b.addRunArtifact(bench_exe);
        r.has_side_effects = true; // never cached: the point is to actually run it
        r.setCwd(b.path("."));
        r.addArgs(argv);
        bench_step.dependOn(&r.step);
    }
}
