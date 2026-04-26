const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const c_flags = [_][]const u8{
        "-std=c11",
        "-O3",
        "-Wall",
        "-Wextra",
        "-Wno-unused-parameter",
        "-Wno-unused-function",
        "-fno-strict-aliasing",
        "-D_POSIX_C_SOURCE=200809L",
    };

    const lib = b.addStaticLibrary(.{
        .name = "rsf",
        .root_source_file = .{ .path = "src/api.zig" },
        .target = target,
        .optimize = optimize,
    });
    lib.main_pkg_path = .{ .path = "." };
    lib.addIncludePath(.{ .path = "c" });
    lib.addCSourceFile(.{ .file = .{ .path = "c/tpm.c" }, .flags = &c_flags });
    lib.linkLibC();
    b.installArtifact(lib);

    const rsf_module = b.addModule("rsf", .{
        .source_file = .{ .path = "rsf.zig" },
    });

    const exe = b.addExecutable(.{
        .name = "rsf",
        .root_source_file = .{ .path = "c/main.zig" },
        .target = target,
        .optimize = optimize,
    });
    exe.main_pkg_path = .{ .path = "." };
    exe.addIncludePath(.{ .path = "c" });
    exe.addModule("rsf", rsf_module);
    exe.addCSourceFile(.{ .file = .{ .path = "c/tpm.c" }, .flags = &c_flags });
    exe.linkLibC();
    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run the RSF CLI");
    run_step.dependOn(&run_cmd.step);

    const unit_tests = b.addTest(.{
        .root_source_file = .{ .path = "src/api.zig" },
        .target = target,
        .optimize = optimize,
    });
    unit_tests.main_pkg_path = .{ .path = "." };
    unit_tests.addIncludePath(.{ .path = "c" });
    unit_tests.addCSourceFile(.{ .file = .{ .path = "c/tpm.c" }, .flags = &c_flags });
    unit_tests.linkLibC();
    const run_unit_tests = b.addRunArtifact(unit_tests);

    const crash_tests = b.addTest(.{
        .root_source_file = .{ .path = "test/crash_test.zig" },
        .target = target,
        .optimize = optimize,
    });
    crash_tests.main_pkg_path = .{ .path = "." };
    crash_tests.addIncludePath(.{ .path = "c" });
    crash_tests.addModule("rsf", rsf_module);
    crash_tests.addCSourceFile(.{ .file = .{ .path = "c/tpm.c" }, .flags = &c_flags });
    crash_tests.linkLibC();
    const run_crash_tests = b.addRunArtifact(crash_tests);

    const test_step = b.step("test", "Run the RSF test suite");
    test_step.dependOn(&run_unit_tests.step);
    test_step.dependOn(&run_crash_tests.step);

    const bench_exe = b.addExecutable(.{
        .name = "rsf-bench",
        .root_source_file = .{ .path = "src/benchmark.zig" },
        .target = target,
        .optimize = optimize,
    });
    bench_exe.main_pkg_path = .{ .path = "." };
    bench_exe.addIncludePath(.{ .path = "c" });
    bench_exe.addCSourceFile(.{ .file = .{ .path = "c/tpm.c" }, .flags = &c_flags });
    bench_exe.linkLibC();
    b.installArtifact(bench_exe);

    const bench_run = b.addRunArtifact(bench_exe);
    bench_run.step.dependOn(b.getInstallStep());
    if (b.args) |args| bench_run.addArgs(args);
    const bench_step = b.step("bench", "Run the RSF benchmarks");
    bench_step.dependOn(&bench_run.step);

    const inspect_exe = b.addExecutable(.{
        .name = "rsf-inspect",
        .root_source_file = .{ .path = "c/inspect.zig" },
        .target = target,
        .optimize = optimize,
    });
    inspect_exe.main_pkg_path = .{ .path = "." };
    inspect_exe.addIncludePath(.{ .path = "c" });
    inspect_exe.addModule("rsf", rsf_module);
    inspect_exe.addCSourceFile(.{ .file = .{ .path = "c/tpm.c" }, .flags = &c_flags });
    inspect_exe.linkLibC();
    b.installArtifact(inspect_exe);
}
