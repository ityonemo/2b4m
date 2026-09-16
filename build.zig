const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Core library module: all proof-checking logic lives here; main.zig is a thin CLI.
    const mod = b.addModule("bpa", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
    });

    const exe = b.addExecutable(.{
        .name = "bpa",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "bpa", .module = mod },
            },
        }),
    });
    b.installArtifact(exe);

    const run_step = b.step("run", "Run bpa");
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

    // Integration test gates (spawn `bpa`, assert stdout/stderr/exit) live in
    // tests/ grouped by subject; build.zig stays build configuration.
    const tests = @import("tests/test_all.zig");
    tests.addTests(b, exe, test_step);

    // `zig build bench` — wall-clock over the real corpus.
    //
    // ALWAYS ReleaseFast, never `optimize`: a Debug build is ~35x slower (the std sweep is
    // 62 s Debug against 1.8 s ReleaseFast), and a benchmark that silently measures Debug
    // produces numbers that send you optimizing the wrong thing. This is why the step
    // builds its own binary instead of reusing `exe`.
    const bench_exe = b.addExecutable(.{
        .name = "bpa-bench",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = .ReleaseFast,
            .imports = &.{.{ .name = "bpa", .module = mod }},
        }),
    });
    const bench_step = b.step("bench", "Time the corpus (always ReleaseFast)");
    // The two whole-corpus sweeps plus the heaviest single file. (`examples/` is excluded:
    // it carries `incorrect.bpa`, a deliberate negative that exits 1 by design.)
    for ([_][]const []const u8{
        &.{ "check", "std" },
        &.{ "check", "aata" },
        &.{ "check", "std/integer/divides.bpa" },
    }) |argv| {
        const r = b.addRunArtifact(bench_exe);
        r.has_side_effects = true; // never cached: the point is to actually run it
        r.setCwd(b.path("."));
        r.addArgs(argv);
        bench_step.dependOn(&r.step);
    }
}
