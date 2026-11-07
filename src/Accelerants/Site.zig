//! Site — what an accelerated tactic SEES of the proof it runs inside. A tactic (one
//! variant of `Accelerants.Tactic`) never holds the driver (`Engine/ProveTask/Prove.zig`): it
//! is handed a `*Site` per phase hook, and everything it may read or signal is a field or
//! method here. The driver builds the Site as a VIEW over its own state right before each
//! hook (`Prove.site`) and reads the RESULT CHANNEL back afterwards; the unit-test rig builds
//! one standalone. Keeping this struct narrow is what keeps the tactics out of the prover's
//! lowering state — a tactic that needs more than this is asking the scaffolding for a hook,
//! not for a field.
//!
//! RESULT CHANNEL (written by a hook, read by the driver after it returns):
//!   `producer_blocker`      a demand the hook racked — the step suspends on it and re-runs
//!   `admit_mode`/`admit_ok` `--fast`: run the decision only; `admit_ok` = accepted
//!   `producer_premise_refs` under admit, cleared (no certificate carries the refs)
//!   `quant_guards`          per-eigen guards a `_quantified` tactic peels and re-closes

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const kernel = @import("../kernel.zig");
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");
const FactKV = @import("../FactKV.zig");
const Walk = @import("../Engine/ProveTask/Walk.zig");
const Elab = @import("../Engine/ProveTask/Elab.zig");

const Site = @This();

pub const Error = error{ Recover, OutOfMemory };
pub const tokName = lexer.tokName;

ctx: *Context,
/// the engine handle of the CURRENT run (racking/suspension go through it)
h: *Engine.Handle,
/// the proof's own term scratchpad — every term a tactic builds lives here
pool: *term.Pool,
/// the proving file's source (step tokens index into it)
source: []const u8,
/// the proving file's pool `.file` Index and universe namespace
file: InternPool.Index,
ns: InternPool.Index,
/// the model this proof runs THROUGH (`.universe` = an ordinary proof)
model: InternPool.Index,
/// the proof's own `(namespace, name)`, inherited as `parent` by every task it demands
self_key: ?FactKV.Key,
/// hygienic fresh-name counter, shared with the driver and its Elab
fresh_counter: *u32,
/// Walk StepOrdinal -> kernel StepId (a local step ref resolves through this)
ordinal_step: *const std.ArrayList(kernel.StepId),
/// the lowered kernel steps and their SOURCE-space formulas (what a cited premise reads as)
low_steps: *const std.ArrayList(kernel.Step),
source_formulas: *const std.ArrayList(TermId),
/// taint the proof inherits from what it cites (`resolveFactRef` appends)
holes_used: *std.ArrayList(InternPool.StrId),
axioms_used: *std.ArrayList(InternPool.Index),

// -- the result channel ------------------------------------------------------------------
/// ADMIT MODE (`--fast <tactic>`): the hook does its own cheap acceptance check and returns
/// WITHOUT a certificate; it sets `admit_ok` on accept and fails (error.Recover) on reject.
admit_mode: bool = false,
admit_ok: bool = false,
/// an outstanding demand: the hook racked a task it needs and returned null WITHOUT a
/// diagnostic; the driver reports `.blocked` and the hook re-runs on resume, idempotently
producer_blocker: ?Engine.TaskIndex = null,
/// the local premise refs the produced synthetic kept as antecedents (null = none produced)
producer_premise_refs: ?[]const lexer.Token = null,
/// per-eigen relativization guards peeled off a `_quantified` tactic's transferred goal
quant_guards: []const ?TermId = &.{},

pub fn text(self: *const Site, tok: lexer.Token) []const u8 {
    return self.source[tok.start..tok.end];
}

/// A term's sort: an fvar's own sort, an app's head result sort; `.prop` for non-term
/// structure. (The operand sort for polynomial's rule-pattern fvars comes from here.)
pub fn termSort(self: *const Site, t: TermId) SortId {
    return switch (self.pool.get(t)) {
        .fvar => |v| v.sort,
        .app => |a| @enumFromInt(@intFromEnum(self.ctx.interner.symResult(@enumFromInt(@intFromEnum(a.sym))))),
        // not a term node — a proposition. Returns the marker, which matches no real sort, so
        // every consumer's `!= v.sort` test rejects it (none of them wants a proposition here).
        else => Elab.prop_sort,
    };
}

/// A stamped name in a LOCAL-only position (step label, step/block ref, proof binder):
/// a `ns.`-qualified token is rejected — matching only its base name would let `x.y`
/// falsely resolve to a local `y`.
pub fn localName(self: *const Site, tok: lexer.Token) Error!StrId {
    if (tok.qualifier != InternPool.Index.none) {
        return self.fail(tok.start, "'{s}' cannot be namespace-qualified here", .{self.text(tok)});
    }
    return tokName(tok);
}

pub fn fail(self: *const Site, offset: u32, comptime fmt: []const u8, args: anytype) Error {
    self.ctx.sink.add(self.diagFile(), offset, fmt, args) catch return error.OutOfMemory;
    return error.Recover;
}

pub fn freshNamed(self: *const Site, prefix: []const u8) Error!StrId {
    self.fresh_counter.* += 1;
    const s = std.fmt.allocPrint(self.ctx.arena, "{s}#{d}", .{ prefix, self.fresh_counter.* }) catch return error.OutOfMemory;
    return self.ctx.interner.internString(s) catch error.OutOfMemory;
}

pub fn renderTerm(self: *const Site, id: TermId) Error![]const u8 {
    return @import("../print.zig").render(self.ctx.arena, self.pool, self.ctx.interner, id) catch error.OutOfMemory;
}

/// The file a cited fact token names: its own file when unqualified, else the import's file.
/// Null when the qualifier does not (yet) resolve to an import — the process pass diagnoses.
pub fn citedFactFile(self: *const Site, t: lexer.Token) ?InternPool.Index {
    if (t.qualifier == InternPool.Index.none) return self.file;
    const st = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = t.qualifier }) orelse return null;
    const ix = switch (st) {
        .done => |x| x,
        .in_flight => return null,
    };
    if (self.ctx.interner.keyOf(ix) != .import) return null;
    return self.ctx.interner.keyOf(self.ctx.interner.keyOf(ix).import.namespace).namespace.file;
}

/// Does the file a cited fact token names DECLARE that name? A trusted decision reads a cited
/// statement only when so — a name nothing declares is a typo for the process pass to report.
pub fn citationDeclared(self: *const Site, t: lexer.Token) bool {
    const file = self.citedFactFile(t) orelse return false;
    const fid = self.ctx.fileOf(file) orelse return false;
    return self.ctx.declOf(fid, tokName(t)) != null;
}

/// The formula of a cited local step AS AN ACCELERANT PRODUCER'S INPUT: source space. Under a
/// model transfer the lowered formula (`low_steps[..].formula`) is relativized to the target;
/// a producer must not mix that with its source-space goal, so it reads the source-space twin
/// recorded at lowering. Identical to the lowered formula in an ordinary proof.
pub fn producerPremiseFormula(self: *const Site, sref: kernel.SRef) TermId {
    // While a producer runs in SOURCE mode, `self.model` is toggled to the universe
    // (demandUsing) → the source twin. Under a guarded model's legacy target-space production
    // the model stays set → the lowered (target) formula. Both coincide in an ordinary proof.
    if (self.model == .universe) return self.source_formulas.items[@intFromEnum(sref.id)];
    return self.low_steps.items[@intFromEnum(sref.id)].formula;
}

/// A kernel-rule step reference: LOCAL-only (a live label in the walk's scope).
pub fn resolveStepRef(self: *const Site, w: *const Walk, tok: lexer.Token) Error!kernel.SRef {
    const name = try self.localName(tok);
    const target = w.resolveStep(name) orelse {
        // nicety: a global fact cited where a step label belongs — name the fix. Check both the
        // FactKV (already-demanded) and the file's AST (a same-file fact decl that nothing
        // demanded, e.g. the cited axiom in `apply_at(t) myAxiom`), so it fires regardless.
        const is_fact = self.ctx.facts.lookup(self.ctx.io, .{ .namespace = self.ns, .name = name }) != null or
            (tok.qualifier == InternPool.Index.none and if (self.ctx.fileOf(self.file)) |fid|
                if (self.ctx.declOf(fid, name)) |d| ast.factOf(d) != null else false
            else
                false);
        if (is_fact) {
            return self.fail(tok.start, "'{s}' is a fact, not a proof step; introduce it as a step first with `[by cite {s}]`, then reference that step", .{
                self.text(tok), self.text(tok),
            });
        }
        return self.fail(tok.start, "unknown reference '{s}'", .{self.text(tok)});
    };
    return switch (target) {
        .step => |ord| .{ .id = self.ordinal_step.items[@intFromEnum(ord)], .loc = tok.start },
        .block => self.fail(tok.start, "'{s}' names a subproof; a step reference is required", .{self.text(tok)}),
    };
}

/// `--trace-facts`: report what a citation RESOLVED TO. Two theorems in different theories
/// can share a name, and a model transfer publishes a second copy of its source's facts under
/// the same names in a `(model, file)` namespace — so which copy a step actually got is not
/// answerable from the source. `why` says which resolution path produced it. Stderr; the
/// verdict is unaffected.
pub fn traceFact(self: *const Site, tok: lexer.Token, ix: InternPool.Index, why: []const u8) void {
    if (!self.ctx.verify.trace_facts) return;
    const a = self.ctx.arena;
    var line: []const u8 = std.fmt.allocPrint(a, "{s}: cite {s}\n    -> {s}\n", .{
        self.siteOf(self.file, tok.start),
        self.text(tok),
        self.describeNamespaceOf(ix),
    }) catch return;
    if (self.ctx.interner.keyOf(ix) == .fact) {
        const f = self.ctx.interner.keyOf(ix).fact;
        line = std.fmt.allocPrint(a, "{s}       {s} {s}\n", .{ line, @tagName(f.kind), self.ctx.interner.stringBytes(f.name) }) catch return;
        if (self.pool.copyIn(self.ctx.interner, f.formula)) |t| {
            if (self.renderTerm(t)) |stmt| {
                line = std.fmt.allocPrint(a, "{s}       {s}\n", .{ line, stmt }) catch return;
            } else |_| {}
        } else |_| {}
    }
    line = std.fmt.allocPrint(a, "{s}       via {s}\n", .{ line, why }) catch return;
    self.ctx.traceLine(line);
}

/// `file:line:col` for a source offset. The offset must belong to `file` — a fact's `loc`
/// indexes the file it was DECLARED in, which is generally not the citing file, so an offset
/// past the end means we were handed the wrong file and the site is reported as unknown
/// rather than read out of bounds.
pub fn siteOf(self: *const Site, file: InternPool.Index, off: u32) []const u8 {
    const fid = self.ctx.fileOf(file) orelse return "?";
    const f = self.ctx.files.get(@intFromEnum(fid));
    if (off >= f.source.len) return std.fmt.allocPrint(self.ctx.arena, "offset {d} (not in {s})", .{ off, f.path }) catch "?";
    const lc = std.zig.findLineColumn(f.source, off);
    return std.fmt.allocPrint(self.ctx.arena, "{s}:{d}:{d}", .{ f.path, lc.line + 1, lc.column + 1 }) catch "?";
}

/// Which FILE a published fact was declared in — searched by scanning the file table for the
/// one whose namespace holds it. A fact Index records its `loc` but not its file, so the trace
/// recovers it here (a linear scan is fine for a diagnostic).
pub fn fileOfFact(self: *const Site, ix: InternPool.Index) ?InternPool.Index {
    const key = self.ctx.interner.keyOf(ix);
    const name: StrId = switch (key) {
        .fact => |f| f.name,
        .schema => |k| return k.file,
        else => return null,
    };
    var files_it = self.ctx.files.iterator();
    while (files_it.next()) |f| {
        const pf = self.ctx.fileIndex(f.path) catch continue;
        const ns = self.ctx.interner.namespace(.universe, pf) catch continue;
        if (self.ctx.facts.lookup(self.ctx.io, .{ .namespace = ns, .name = name })) |st| {
            if (st == .proven and st.proven == ix) return pf;
        }
    }
    return null;
}

/// Describe where a resolved fact CAME FROM: the namespace the citing task is resolving in
/// (`universe` for an ordinary proof, or the model it is proving under) plus the fact's own
/// declaration site. The distinction is the point of the trace — a citation that should have
/// stayed in the universe but came back through a model is the bug this exists to show.
pub fn describeNamespaceOf(self: *const Site, ix: InternPool.Index) []const u8 {
    const key = self.ctx.interner.keyOf(ix);
    const loc: u32 = switch (key) {
        .fact => |f| f.loc,
        .schema => |k| k.loc,
        else => return "(not a fact)",
    };
    const ns_text = if (self.model == InternPool.Index.none or self.model == .universe)
        "universe"
    else
        std.fmt.allocPrint(self.ctx.arena, "model#{d}", .{@intFromEnum(self.model)}) catch "model?";
    const decl_file = self.fileOfFact(ix) orelse self.file;
    return std.fmt.allocPrint(self.ctx.arena, "resolved in ns={s}, declared at {s}", .{ ns_text, self.siteOf(decl_file, loc) }) catch "?";
}

/// An axiom/theorem citation: GLOBAL fact via FactKV (the read pass made it proven, or
/// left an in_flight-self / failed entry — diagnosed here).
pub fn resolveFactRef(self: *const Site, tok: lexer.Token) Error!InternPool.Index {
    const ns = try self.resolveQualifier(tok);
    return self.resolveFactIn(tok, ns);
}

/// `resolveFactRef` with the namespace already chosen: the fact `tok` names in `ns`, with the
/// TRANSFER redirect (a source theorem → its copy re-proved under this proof's model) and the
/// axiom overlay applied. Shared by the bare/qualified `cite` and the `[using import(I) thm]`
/// citation, whose namespace is the import's — an import cite inside a transferred proof used to
/// skip the redirect and hand the kernel the UNTRANSFERRED source statement.
pub fn resolveFactIn(self: *const Site, tok: lexer.Token, ns: InternPool.Index) Error!InternPool.Index {
    const state = self.ctx.facts.lookup(self.ctx.io, .{ .namespace = ns, .name = tokName(tok) }) orelse {
        return self.fail(tok.start, "unknown statement '{s}'", .{self.text(tok)});
    };
    const src = switch (state) {
        .proven => |x| x,
        .in_flight => return self.fail(tok.start, "cites '{s}', whose proof has not completed (self-citation or a failed/cyclic dependency)", .{self.text(tok)}),
    };
    // In a TRANSFER, a cited SOURCE THEOREM resolves to its TRANSFERRED version (re-proved under
    // the model), keyed `(model, ns.file).name` — the read pass demanded it. ONLY a theorem: an
    // AXIOM stays on the `applyModel` overlay path (mapped → local discharging fact), never a free
    // transferred leaf (see the read-pass note).
    if (self.model != InternPool.Index.none and self.model != .universe and
        self.ctx.interner.keyOf(src) == .fact and self.ctx.interner.keyOf(src).fact.kind == .theorem)
    {
        const nsfile = self.ctx.interner.keyOf(ns).namespace.file;
        const tns = try self.ctx.interner.namespace(self.model, nsfile);
        if (self.ctx.facts.lookup(self.ctx.io, .{ .namespace = tns, .name = tokName(tok) })) |st| switch (st) {
            .proven => |x| if (self.ctx.interner.keyOf(x) != .schema) {
                self.inheritHoles(x);
                self.inheritAxioms(x);
                self.traceFact(tok, x, "TRANSFER redirect: the citing task runs under a model, so the cited theorem resolved to its transferred copy");
                return x;
            },
            // the transferred copy is being proved RIGHT NOW by another task (or by this one):
            // falling through hands the citation the UNTRANSFERRED source copy, whose statement
            // is in the source sort — the mismatch `--trace-facts` exists to expose.
            .in_flight => |owner| self.traceFact(tok, src, if (owner == self.h.self_index)
                "TRANSFER redirect FELL THROUGH: the transferred copy is in_flight owned by THIS task (self-cycle) — using the untransferred source copy"
            else
                "TRANSFER redirect FELL THROUGH: the transferred copy is in_flight owned by ANOTHER task — using the untransferred source copy"),
        } else {
            self.traceFact(tok, src, "TRANSFER redirect FELL THROUGH: no transferred copy was ever demanded for this citation — using the untransferred source copy");
        }
    }
    const ix = switch (state) {
        // in a model transfer, a source-axiom citation remaps (via the overlay) to its
        // discharging LOCAL fact — an obligation. `.universe` = identity (ordinary proof).
        .proven => |x| self.ctx.interner.applyModel(self.model, x),
        .in_flight => unreachable, // handled above
    };
    // a SCHEMA lives in the fact table too (a fact-with-params), but it is NOT a citable ground
    // fact — it has no closed formula. It must be MONOMORPHIZED via `[using instantiation …]`.
    // Reject here so every fact-formula reader below can assume a real `.fact` Index.
    if (self.ctx.interner.keyOf(ix) == .schema)
        return self.fail(tok.start, "'{s}' is a schema; use `[using instantiation {s}(...)]`, not a fact citation", .{ self.text(tok), self.text(tok) });
    self.inheritHoles(ix);
    self.inheritAxioms(ix);
    self.traceFact(tok, ix, if (self.model == InternPool.Index.none or self.model == .universe) "direct lookup" else "overlay (applyModel) under the citing task's model");
    return ix;
}

/// HOLE TAINT inheritance (summary blast-radius only): if the cited fact `ix` rests on holes,
/// add each hole name to THIS proof's `holes_used` (deduped). Citing a hole — or a fact that
/// rests on one — makes the current proof rest on it. NEVER affects the proof verdict; a hole is
/// an axiom everywhere the KERNEL is concerned. See [[hole-mechanism]].
pub fn inheritHoles(self: *const Site, ix: InternPool.Index) void {
    const names = self.ctx.holeTaintOf(ix) orelse return;
    outer: for (names) |h| {
        for (self.holes_used.items) |seen| if (seen == h) continue :outer; // already tracked
        self.holes_used.append(self.ctx.arena, h) catch return; // OOM: best-effort taint
    }
}

/// AXIOM DEPENDENCY inheritance (the `--axioms` report): the cited fact's own axiom set becomes
/// part of this proof's. An AXIOM is its own seed — a theorem is not (it carries whatever its
/// proof rested on). Deduped; never affects the proof verdict.
pub fn inheritAxioms(self: *const Site, ix: InternPool.Index) void {
    if (self.ctx.axiomTaintOf(ix)) |axs| {
        outer: for (axs) |a| {
            for (self.axioms_used.items) |seen| if (seen == a) continue :outer;
            self.axioms_used.append(self.ctx.arena, a) catch return; // OOM: best-effort
        }
    }
}

/// The namespace a (possibly `ns.`-qualified) stamped token resolves in: unqualified =
/// this proof's ns; qualified = the import named by `tok.qualifier`. (Multi-level
/// qualification was diagnosed at parse — the stamped qualifier is at most one level.)
pub fn resolveQualifier(self: *const Site, tok: lexer.Token) Error!InternPool.Index {
    if (tok.qualifier == InternPool.Index.none) return self.ns;
    const qtext = self.ctx.interner.stringBytes(tok.qualifier);
    const state = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = tok.qualifier }) orelse {
        return self.fail(tok.start, "unknown namespace '{s}'", .{qtext});
    };
    return switch (state) {
        .done => |ix| switch (self.ctx.interner.keyOf(ix)) {
            .import => |m| m.namespace,
            else => self.fail(tok.start, "'{s}' is not a namespace", .{qtext}),
        },
        .in_flight => self.fail(tok.start, "unknown namespace '{s}'", .{qtext}),
    };
}

/// Collect distinct free fvars (by name) into `out`.
/// Collect the DISTINCT free vars of `id` into `out` (on the caller's arena). Iterative work-stack
/// (was native recursion) — depth-safe. The frontier stack is GPA-backed scratch (reclaimed here);
/// `out` stays durable. (Note: this collects fvars regardless of binder depth — a "free var" here
/// is any `.fvar` node, matching the original; bound vars are `.bvar` and contribute nothing.)
pub fn collectFreeFvars(self: *const Site, id: TermId, out: *std.ArrayList(term.Node.Fvar)) Error!void {
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const a = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(a, id);
    while (stack.pop()) |cur| {
        const node = self.pool.get(cur);
        switch (node) {
            .fvar => |v| {
                var seen = false;
                for (out.items) |e| if (e.name == v.name) {
                    seen = true;
                    break;
                };
                if (!seen) try out.append(self.ctx.arena, v);
            },
            else => try self.pool.pushChildren(&stack, a, node),
        }
    }
}

pub fn isBiconditionalShape(self: *const Site, id: TermId) bool {
    const pool = self.pool;
    const n = pool.get(id);
    if (n != .bin or n.bin.op != .and_op) return false;
    const l = pool.get(n.bin.lhs);
    const r = pool.get(n.bin.rhs);
    if (l != .bin or l.bin.op != .implies) return false;
    if (r != .bin or r.bin.op != .implies) return false;
    return pool.alphaEq(l.bin.lhs, r.bin.rhs) and pool.alphaEq(l.bin.rhs, r.bin.lhs);
}

/// Intern a comptime literal once (cached on the Context's interner; cheap dedup).
pub fn internStr(self: *const Site, comptime s: []const u8) Error!StrId {
    return self.ctx.interner.internString(s) catch error.OutOfMemory;
}

/// The file this proof's offsets index — its own `file`, as a dense FileId. Derived rather
/// than tracked on the sink so a diagnostic's file is a value (see diagnostics.zig).
pub fn diagFile(self: *const Site) u32 {
    const fid = self.ctx.fileOf(self.file) orelse return 0;
    return @intFromEnum(fid);
}
