//! The parse task: payload + behavior. `src/Engine/` is where all engine task payloads
//! live (ParseTask now; ProveTask and friends alongside it later).
//!
//! This FILE IS the payload struct (capitalized-file = top-level-struct convention):
//! `const ParseTask = @import("Engine/ParseTask.zig")` yields the type directly. It is
//! self-contained: `new()` packages a payload into a rack-ready `Engine.Task` (bundling
//! the run-fn), and `run` IS that run-fn — the parse-task body.
//!
//! A FileId is assigned at DISCOVERY time (so a child's id exists before its parse runs —
//! cyclic-import safe); the SOURCE is read HERE, by the file's own ParseTask — nobody hands
//! it in (a `.md` is a literate document: its ```bpa blocks are extracted here too). Parse is
//! the ONE task type that never suspends.
//!
//! LAZY PARSING (Step 11): a ParseTask parses ONE file. It discovers + resolves that
//! file's imports (populating `import_maps` so a qualified `ns.name` can find the child's
//! FileId) but does NOT rack the children's ParseTasks — a child is parsed only when a
//! Fetch/Prove task first cites into it (via `Context.demandParse`, which racks the
//! ParseTask and suspends on it). At completion this task marks its file `parsed`
//! (waking anyone suspended on it). The ROOT ParseTask additionally scans its theorems
//! and racks the ProveTasks that seed demand.

const std = @import("std");
const parser = @import("../parser.zig");
const ast = @import("../ast.zig");
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");
const literate = @import("../literate.zig");

const ParseTask = @This();

/// The file to parse. Its path is on the Context (`files[file_id].path`); the task reads it.
file_id: Context.FileId,
/// Does this parse SEED PROOFS? True when something asked for this file to be CHECKED (the
/// entry point racked it) — the task scans the parsed decls and racks a ProveTask per local
/// theorem + axiom statement. False when the file is merely being read because something cited
/// into it (`demandParse`): its theorems are proved only where they are cited. The entry point
/// also sets it false when it racks a specific ProveTask itself (`check <file> <theorem>`),
/// since it has already said what to prove.
seed_proofs: bool = false,

/// Package a payload into a rack-ready `Engine.Task`. Arena-allocates the payload (so it
/// outlives the queue slot behind the engine's type-erased `*anyopaque`) and bundles the
/// typed `runErased`. Call sites just `try h.rack(ParseTask.new(arena, .{…}))`.
pub fn new(arena: std.mem.Allocator, payload: ParseTask) std.mem.Allocator.Error!Engine.Task {
    const p = try arena.create(ParseTask);
    p.* = payload;
    return .{ .payload = p, .run = &runErased };
}

/// The engine calls this with the type-erased payload; cast back and dispatch to `run`.
fn runErased(self: *Context, payload: *anyopaque, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const task: *ParseTask = @ptrCast(@alignCast(payload));
    return run(self, task.*, h);
}

/// The parse-task body: parse ONE file, resolve its imports (DISCOVER each child + record
/// the raw-path -> child-FileId map, so citations can find it — but do NOT rack the
/// child's ParseTask; that happens on demand when something cites into it). Mark the file
/// `parsed` at the end (the completion wakes anyone suspended in `demandParse`). If this
/// is the root file, scan its theorems and rack the seed ProveTasks.
pub fn run(self: *Context, task: ParseTask, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const idx = @intFromEnum(task.file_id);
    const path = self.files.get(idx).path;
    if (self.verify.trace_facts) {
        const line = std.fmt.allocPrint(self.arena, "[parse] task#{d} = {s}\n", .{ @intFromEnum(h.self_index), path }) catch "";
        self.traceLine(line);
    }
    // READ the file (the one place source enters the engine); a literate `.md` yields its
    // ```bpa blocks with every other line blanked, so offsets index the document as written.
    // A file that cannot be read is diagnosed where it was NAMED — the parent's import token
    // — or at the top of the file itself for a root; it then counts as parsed-and-empty so
    // whatever cited into it proceeds to its own "reference not found".
    const bytes = self.read_fn(self.read_ctx, self.arena, path) catch {
        if (self.origins.get(idx)) |o| {
            // diagnosed at the IMPORT token, so it belongs to the importing file
            try self.sink.add(@intFromEnum(o.file), o.loc, "cannot open '{s}': file not found", .{path});
        } else {
            try self.sink.add(idx, 0, "cannot open '{s}': file not found", .{path});
        }
        self.parse_state.set(idx, .parsed);
        return;
    };
    const source = if (std.mem.endsWith(u8, path, ".md")) try literate.extract(self.arena, bytes) else bytes;
    self.files.at(idx).source = source; // in place: `at` is a stable pointer
    var p: parser.Parser = .initInterningInFile(self.arena, source, self.sink, self.interner, idx);
    const parsed = try p.parseFile();
    self.parsed.set(idx, parsed);
    self.addDeclarations(parsed.decls.len);
    // register each decl by name for O(1) by-name resolution (the demand tasks look up
    // decls by name, not position). The parsed slice is arena-stable, so the pointers hold.
    // This is the AUTHORITATIVE first pass: a name already registered here is a genuine
    // intra-file duplicate declaration — diagnosed at the later decl's name token (the
    // demand engine would otherwise silently keep the first and never notice, since a file
    // is only elaborated on demand). `forward` (intheory) decls register nothing and never
    // collide (registerDecl returns true for them).
    for (self.parsed.get(idx).decls) |*decl| {
        const fresh = try self.registerDecl(task.file_id, decl);
        if (!fresh) {
            const nt = ast.declName(decl);
            try self.sink.add(idx, nt.start, "duplicate declaration of '{s}'", .{self.interner.stringBytes(nt.name)});
        }
    }

    // FORWARD (`intheory name`) is a manifest PROMISE that `name` is defined later in this file
    // as a THEOREM. It lands NOWHERE durable (not the registry, not the pool); ParseTask just
    // checks the promise holds (the real theorem registered above) and drops it. A missing name
    // or a name defined as something OTHER than a theorem (an axiom, etc.) is diagnosed.
    for (self.parsed.get(idx).decls) |decl| {
        if (decl != .forward) continue;
        const promised = decl.forward.name;
        const target = self.declOf(task.file_id, promised.name) orelse {
            try self.sink.add(idx, promised.start, "forwarded theorem '{s}' is never defined", .{self.interner.stringBytes(promised.name)});
            continue;
        };
        if (target.* != .theorem) {
            const kind: []const u8 = switch (target.*) {
                .axiom => "an axiom",
                .hole => "a hole",
                else => "a non-theorem",
            };
            try self.sink.add(idx, promised.start, "'{s}' is forwarded as a theorem but defined as {s}", .{ self.interner.stringBytes(promised.name), kind });
        }
    }

    // resolved import-path strings are TRANSIENT — used only to look the child file up / discover
    // it, then dropped (the common re-reference / std-hit case retains nothing). Resolve them into
    // a GPA-backed scratch arena (reclaimed at the end of the loop) instead of leaking every path
    // into the never-reset main arena. TRAP: `discover` RETAINS the path (stores it in
    // `files[].path`, read later by diagnostics), so on the discover branch we DUPE it onto the
    // main arena; the scratch string stays purely transient otherwise.
    var path_scratch: std.heap.ArenaAllocator = .init(self.gpa);
    defer path_scratch.deinit();
    const scratch = path_scratch.allocator();
    for (parsed.decls) |decl| {
        if (decl != .import) continue;
        const d = decl.import;
        // the parser stamped the quote-stripped path string; path RESOLUTION (fs joins)
        // works on its bytes — that's I/O, not name comparison.
        const raw = self.interner.stringBytes(d.path.name);
        const resolved = if (std.mem.startsWith(u8, raw, "std/"))
            try std.fs.path.resolve(scratch, &.{ self.std_root, raw["std/".len..] })
        else
            try std.fs.path.resolve(scratch, &.{ std.fs.path.dirname(path) orelse ".", raw });

        const child: Context.FileId = if (try self.lookupFile(resolved)) |existing|
            existing // already discovered (incl. a cyclic re-reference) — reuse id
        else
            // DISCOVER the child (reserve its FileId + table slots) so the import resolves —
            // nothing is READ: a citation into it racks its ParseTask, which reads it (and
            // reports a missing file at THIS import token). Import resolution only needs the
            // child's identity. discover RETAINS the path → dupe it durably (the scratch copy
            // is freed below).
            try self.discover(try self.arena.dupe(u8, resolved), .{ .file = task.file_id, .loc = d.path.start });
        try self.import_maps.at(idx).put(self.arena, d.path.name, child); // mutated in place
    }

    // this file's AST is now populated — mark it parsed so `demandParse` waiters wake.
    self.parse_state.set(idx, .parsed);

    // the ROOT file's theorems are the roots of demand: scan + rack a ProveTask each.
    // (Only the root — imported files' theorems are demanded by citations, not proved
    // just for being imported.)
    if (task.seed_proofs) {
        const file_index = try self.fileIndex(path);
        for (parsed.decls) |decl| {
            switch (decl) {
                // a LOCAL theorem is a root of demand — rack its ProveTask; BUT a
                // theorem-SCHEMA (params != null) is a template, NOT proved as a root (it is
                // instantiated on demand). A schema is NOT checked at its decl: soundness comes
                // from the PER-INSTANCE proof at each `[using instantiation …]` (which the kernel
                // always runs). A schema need not be a true universal — a narrow one is bad form,
                // not wrong, and a bad instantiation fails at its use site (#93). An alias theorem
                // proves nothing new.
                .theorem => |t| switch (t) {
                    .local => |l| {
                        if (l.fact.params == null) {
                            try h.rack(try Engine.ProveTask.new(self.arena, .{ .file = file_index, .name = l.fact.name.name }));
                        }
                    },
                    .alias => {},
                },
                // a root-file AXIOM is not "proved", but its ProveTask still ELABORATES its
                // stated formula — which discharges any guarded/refined-application obligation
                // in the statement (an axiom asserting `div(ZERO, ZERO) = …` owes `ZERO != ZERO`,
                // else it smuggles a partial function outside its domain). A ground axiom's task
                // is a leaf publish; a schema-axiom (params) stays an on-demand template.
                .axiom => |a| switch (a) {
                    .local => |f| {
                        if (f.params == null) {
                            try h.rack(try Engine.ProveTask.new(self.arena, .{ .file = file_index, .name = f.name.name }));
                        }
                    },
                    .alias => {},
                },
                // a `model` decl is NOT built eagerly — a model is validated only when it is
                // actually CITED (`[by model(M) …]` racks its ModelTask). An unused model,
                // even a malformed one, is inert: nothing depends on it, so nothing is wrong.
                else => {},
            }
        }
    }
}
