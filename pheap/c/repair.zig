const std = @import("std");
const security = @import("../src/security.zig");
const header_mod = @import("../src/header.zig");
const schema = @import("../src/schema.zig");
const snapshot_mod = @import("snapshot.zig");

pub const RepairError = error{
    NotRepairable,
    BackupMissing,
    HeaderUnreadable,
    PayloadUnreadable,
    IoFailed,
    NothingToDo,
} || header_mod.HeaderError || security.SecurityError || std.mem.Allocator.Error;

pub const RepairReport = struct {
    primary_path: []const u8,
    backup_path: []const u8,
    primary_present: bool,
    backup_present: bool,
    primary_valid: bool,
    backup_valid: bool,
    repaired_from_backup: bool,
    promoted_temp: bool,
    bytes_total: usize,
};

pub const Repairer = struct {
    allocator: std.mem.Allocator,
    dir: std.fs.Dir,
    primary: []u8,
    backup: []u8,
    temp: []u8,

    pub fn init(allocator: std.mem.Allocator, dir: std.fs.Dir, primary_name: []const u8) !Repairer {
        const primary_owned = try allocator.dupe(u8, primary_name);
        errdefer allocator.free(primary_owned);
        const backup_owned = try std.fmt.allocPrint(allocator, "{s}.bak", .{primary_name});
        errdefer allocator.free(backup_owned);
        const temp_owned = try std.fmt.allocPrint(allocator, "{s}.tmp", .{primary_name});
        errdefer allocator.free(temp_owned);
        return .{
            .allocator = allocator,
            .dir = dir,
            .primary = primary_owned,
            .backup = backup_owned,
            .temp = temp_owned,
        };
    }

    pub fn deinit(self: *Repairer) void {
        self.allocator.free(self.primary);
        self.allocator.free(self.backup);
        self.allocator.free(self.temp);
    }

    pub fn repair(self: *Repairer) RepairError!RepairReport {
        var report = RepairReport{
            .primary_path = self.primary,
            .backup_path = self.backup,
            .primary_present = false,
            .backup_present = false,
            .primary_valid = false,
            .backup_valid = false,
            .repaired_from_backup = false,
            .promoted_temp = false,
            .bytes_total = 0,
        };
        report.primary_present = pathExists(self.dir, self.primary);
        report.backup_present = pathExists(self.dir, self.backup);
        const temp_present = pathExists(self.dir, self.temp);
        if (report.primary_present) {
            const ok = self.validate(self.primary) catch false;
            report.primary_valid = ok;
        }
        if (report.backup_present) {
            const ok = self.validate(self.backup) catch false;
            report.backup_valid = ok;
        }
        if (!report.primary_valid and temp_present) {
            const ok = self.validate(self.temp) catch false;
            if (ok) {
                self.dir.deleteFile(self.primary) catch {};
                self.dir.rename(self.temp, self.primary) catch return RepairError.IoFailed;
                report.primary_present = true;
                report.primary_valid = true;
                report.promoted_temp = true;
            } else {
                self.dir.deleteFile(self.temp) catch {};
            }
        }
        if (!report.primary_valid and report.backup_valid) {
            self.dir.deleteFile(self.primary) catch {};
            self.copyFile(self.backup, self.primary) catch return RepairError.IoFailed;
            report.primary_present = true;
            report.primary_valid = true;
            report.repaired_from_backup = true;
        }
        if (!report.primary_valid and !report.backup_valid) {
            return RepairError.NotRepairable;
        }
        if (report.primary_valid and !report.backup_valid) {
            self.copyFile(self.primary, self.backup) catch return RepairError.IoFailed;
            report.backup_present = true;
            report.backup_valid = true;
        }
        report.bytes_total = self.statSize(self.primary);
        return report;
    }

    pub fn validate(self: *Repairer, sub_path: []const u8) !bool {
        const file = self.dir.openFile(sub_path, .{}) catch return false;
        defer file.close();
        const stat = file.stat() catch return false;
        if (stat.size < header_mod.HEADER_SIZE + 4) return false;
        const bytes = self.allocator.alloc(u8, @intCast(stat.size)) catch return false;
        defer self.allocator.free(bytes);
        const n = file.readAll(bytes) catch return false;
        if (n != bytes.len) return false;
        const hdr = header_mod.Header.readBytes(bytes[0..header_mod.HEADER_SIZE]) catch return false;
        const cfg = hdr.toConfig() catch return false;
        const half = cfg.dim / 2;
        const matrix = half * half;
        const params = 2 * matrix + 2 * half;
        const expected_payload = cfg.layers * params * @sizeOf(f32);
        if (bytes.len != header_mod.HEADER_SIZE + expected_payload + @sizeOf(u32)) return false;
        const payload_end = header_mod.HEADER_SIZE + expected_payload;
        const stored = std.mem.readIntLittle(u32, bytes[payload_end .. payload_end + 4][0..4]);
        const computed = security.Crc32.computeBytes(bytes[header_mod.HEADER_SIZE..payload_end]);
        if (stored != computed) return false;
        var snap = snapshot_mod.SavedModelSnapshot.readBytes(self.allocator, bytes) catch return false;
        defer snap.deinit();
        for (snap.layer_data) |slice| {
            security.ensureFiniteF32(slice) catch return false;
        }
        return true;
    }

    fn copyFile(self: *Repairer, src: []const u8, dst: []const u8) !void {
        const in = try self.dir.openFile(src, .{});
        defer in.close();
        var out = try self.dir.createFile(dst, .{ .truncate = true });
        defer out.close();
        var buffer: [16 * 1024]u8 = undefined;
        while (true) {
            const n = try in.read(&buffer);
            if (n == 0) break;
            try out.writeAll(buffer[0..n]);
        }
        try out.sync();
    }

    fn statSize(self: *Repairer, sub_path: []const u8) usize {
        const f = self.dir.openFile(sub_path, .{}) catch return 0;
        defer f.close();
        const s = f.stat() catch return 0;
        return @intCast(s.size);
    }
};

pub fn pathExists(dir: std.fs.Dir, name: []const u8) bool {
    if (dir.access(name, .{})) |_| return true else |_| return false;
}

test "repair restores primary from backup" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = schema.RSFConfig{ .dim = 8, .layers = 1 };
    const pheap_core = @import("pheap.zig");
    const core = try pheap_core.RSFCore.init(alloc, cfg);
    defer core.destroy();
    var snap = try snapshot_mod.SavedModelSnapshot.capture(alloc, core);
    defer snap.deinit();
    try snapshot_mod.writeSnapshotToFile(&snap, alloc, tmp_dir.dir, "model.rsf.bak");
    var rep = try Repairer.init(alloc, tmp_dir.dir, "model.rsf");
    defer rep.deinit();
    const report = try rep.repair();
    try std.testing.expect(report.primary_valid);
    try std.testing.expect(report.repaired_from_backup);
}

test "repair fails when nothing valid" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var rep = try Repairer.init(alloc, tmp_dir.dir, "missing.rsf");
    defer rep.deinit();
    try std.testing.expectError(RepairError.NotRepairable, rep.repair());
}
