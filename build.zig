const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

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

    // SOURCE-CONVENTION gates: invariants the language cannot express, checked by reading the
    // source (Zig has no field privacy, so "touch this map only through its accessor" is
    // enforceable only by a test). Runs from the repo root so its walk finds `src/`.
    const convention_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_source_conventions.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    const run_convention_tests = b.addRunArtifact(convention_tests);
    run_convention_tests.setCwd(b.path("."));
    test_step.dependOn(&run_convention_tests.step);

    // Integration test gates (spawn `2b4m`, assert stdout/stderr/exit) live in
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
