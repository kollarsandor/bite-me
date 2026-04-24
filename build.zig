const std = @import("std");  
  
pub fn build(b: *std.Build) void {  
    const target = b.standardTargetOptions(.{});  
    const optimize = b.standardOptimizeOption(.{});  
  
    const gpu_accel = b.option(bool, "gpu_acceleration", "Enable GPU acceleration via CUDA/Futhark") orelse false;  
  
    const build_options = b.addOptions();  
    build_options.addOption(bool, "gpu_acceleration", gpu_accel);  
  
    const wf = b.addWriteFiles();  
    const rsf_root = wf.addCopyFile(b.path("rsf.zig"), "rsf/rsf.zig");  
    _ = wf.addCopyFile(b.path("oftb.zig"), "rsf/oftb.zig");  
    _ = wf.addCopyFile(b.path("accel_interface.zig"), "hw/accel/accel_interface.zig");  
    _ = wf.addCopyFile(b.path("futhark_bindings.zig"), "hw/accel/futhark_bindings.zig");  
    _ = wf.addCopyFile(b.path("cuda_bindings.zig"), "hw/accel/cuda_bindings.zig");  
    _ = wf.addCopyFile(b.path("core/tensor.zig"), "core/tensor.zig");  
    _ = wf.addCopyFile(b.path("core/memory.zig"), "core/memory.zig");  
  
    const lib = b.addStaticLibrary(.{  
        .name = "rsf",  
        .root_source_file = rsf_root,  
        .target = target,  
        .optimize = optimize,  
    });  
  
    lib.root_module.addOptions("build_options", build_options);  
    lib.addCSourceFile(.{  
        .file = b.path("futhark_kernels.c"),  
        .flags = &.{ "-std=c99", "-O2", "-fno-sanitize=undefined" },  
    });  
    lib.addIncludePath(b.path("."));  
    lib.linkLibC();  
  
    if (gpu_accel) {  
        lib.linkSystemLibrary("cuda");  
    }  
  
    b.installArtifact(lib);  
}
