//! Elaboration: surface AST -> kernel terms. Resolves names, checks sorts,
//! stores declarations in the Env. Schemas are stored as forms, NOT
//! elaborated (comptime semantics: checked per instantiation, in M4).
//!
//! Untrusted machinery: nothing here establishes a theorem; it only prepares
//! concrete terms for the kernel and rejects ill-formed input early with
//! precise diagnostics.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("ast.zig");
const lexer = @import("lexer.zig");
const InternPool = @import("InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("term.zig");
const SortId = term.SortId;
const TermId = term.TermId;
const Env = @import("env.zig").Env;
const FileId = @import("env.zig").FileId;
const Symbol = @import("env.zig").Symbol;
const Statement = @import("env.zig").Statement;
pub const StatementId = @import("env.zig").StatementId;
const Diagnostics = @import("diagnostics.zig");
const kernel = @import("kernel.zig");
const simplify_mod = @import("simplify.zig");
const smt_mod = @import("accelerant/arithmetic/smt.zig");
const presburger_mod = @import("accelerant/arithmetic/presburger.zig");
const farkas_mod = @import("accelerant/arithmetic/farkas.zig");
const accel_simplify = @import("accelerant/simplify.zig");
const accel_assoc_commut = @import("accelerant/assoc_commut.zig");
const accel_assoc = @import("accelerant/assoc.zig");
const accel_polynomial = @import("accelerant/polynomial.zig");
const accel_ext = @import("accelerant/ext.zig");
const accel_model = @import("accelerant/model.zig");
const accel_tautology = @import("accelerant/tautology.zig");
const accel_specialize = @import("accelerant/specialize.zig");
const accel_chain = @import("accelerant/chain.zig");
const accel_arithmetic = @import("accelerant/arithmetic.zig");

/// One accelerated tactic, keyed by the `[by <name>]` spelling it owns. Every
/// accelerant conforms to the same signature — `justify(self, low, block, goal,
/// c)` — so the dispatcher is a single table lookup rather than a per-tactic
/// switch case. A tactic's `foo` / `foo_quantified` spellings are two entries
/// pointing at `justify` / `justifyQuantified`. Kernel-primitive rules (axiom,
/// modus_ponens, …) are NOT here — they stay in the `lowerJustification` switch.
pub const Accelerant = struct {
    name: []const u8,
    justify: *const fn (*Elaborator, *Elaborator.Lowering, kernel.BlockId, TermId, ast.Step.Claim) ElabError!kernel.Justification,
};

const accelerants = [_]Accelerant{
    .{ .name = "simplify", .justify = &accel_simplify.justify },
    .{ .name = "simplify_quantified", .justify = &accel_simplify.justifyQuantified },
    .{ .name = "assoc_commut", .justify = &accel_assoc_commut.justify },
    .{ .name = "assoc_commut_quantified", .justify = &accel_assoc_commut.justifyQuantified },
    .{ .name = "assoc", .justify = &accel_assoc.justify },
    .{ .name = "assoc_quantified", .justify = &accel_assoc.justifyQuantified },
    .{ .name = "polynomial", .justify = &accel_polynomial.justify },
    .{ .name = "polynomial_quantified", .justify = &accel_polynomial.justifyQuantified },
    .{ .name = "tautology", .justify = &accel_tautology.justify },
    .{ .name = "arithmetic", .justify = &accel_arithmetic.justify },
    .{ .name = "ext", .justify = &accel_ext.justify },
    .{ .name = "ext_quantified", .justify = &accel_ext.justifyQuantified },
    .{ .name = "model", .justify = &accel_model.justify },
    .{ .name = "specialize", .justify = &accel_specialize.justify },
    .{ .name = "chain", .justify = &accel_chain.justify },
};

/// name -> index into `accelerants`, built once at comptime.
const accelerant_index = blk: {
    const Entry = struct { []const u8, usize };
    var entries: [accelerants.len]Entry = undefined;
    for (accelerants, 0..) |a, i| entries[i] = .{ a.name, i };
    break :blk std.StaticStringMap(usize).initComptime(entries);
};

pub const ElabError = error{ Recover, OutOfMemory };

/// What to actually verify, as independent knobs. Full verification (all true)
/// is the default; the CLI's `--fast`/`--faster`/`--reckless` flags are
/// monotonic presets that turn these off one at a time to speed up the
/// edit→check loop during development (always loudly disclosed). Modeled as
/// separate booleans, not a flat enum, so a future per-project manifest and
/// verification cache address the same knobs without rework.
pub const Verify = struct {
    /// `by arithmetic`/`by tautology` must produce a checkable certificate
    /// (elaborated to kernel steps); an accelerated fallback is a hard error.
    /// When false, take the accelerated verdict and record it (disclosed in the
    /// summary).
    certify_arithmetic: bool = true,
    /// re-check imported theorems' proofs. When false, imported theorem bodies
    /// are trusted (declarations load, proofs are not re-verified).
    recheck_imports: bool = true,
    /// re-check imported schemas at each instantiation. When false, a proven
    /// imported schema is trusted without re-instantiating its body.
    recheck_schemas: bool = true,
    /// `--draft` mode: a WIP proof. The single coarse "work in progress" bit that
    /// author-hygiene checks consult to relax — NOT rejecting a proof for a dead
    /// step (a fact it introduces but never uses), a redundant arithmetic
    /// `fallback`, etc. (Holes are allowed under `--draft` too, gated in main.)
    draft: bool = false,
};

pub const Elaborator = struct {
    arena: Allocator,
    source: []const u8,
    interner: *InternPool,
    pool: *term.Pool,
    env: *Env,
    sink: *Diagnostics.Sink,
    /// the file being elaborated: all unqualified names resolve in its scope
    file: FileId,
    /// the scope well-known ARITHMETIC names (symbols + lemmas) resolve in.
    /// Null means "local scope" (self.file) — bare `by arithmetic`, today's
    /// behavior. Set to a named theory module's FileId for `arithmetic(<mod>)`
    /// so the certifiers resolve roles against that theory regardless of local
    /// aliases. Scoped: set at the top of arithmeticJustification, restored
    /// after.
    theory_file: ?FileId = null,
    /// raw import path (as written, interned) -> loaded file, from the loader
    imports: ?*const std.AutoHashMapUnmanaged(StrId, FileId) = null,
    /// trusted mode (imported files without --recursive): declarations are
    /// elaborated but proofs are NOT checked and obligations are NOT owed;
    /// theorems are marked proven-by-trust. Schema proofs are unaffected —
    /// they are always re-checked at instantiation, in the instantiating
    /// file's (untrusted) elaboration.
    trusted: bool = false,
    /// which layers to verify (see `Verify`). Default: verify everything.
    verify: Verify = .{},
    /// accelerated-tactic names the CURRENT top-level theorem's proof has
    /// leaned on (directly, or transitively via citations and schema
    /// re-checks); cleared per theorem, stored on the fact when it proves
    accelerated_used: std.ArrayList(StrId) = .empty,
    /// hole names the CURRENT top-level theorem's proof rests on (a cited hole,
    /// or a cited theorem that itself rests on holes); cleared per theorem,
    /// stored on the fact when it proves. Same accumulate-then-store shape as
    /// accelerated_used.
    holes_used: std.ArrayList(StrId) = .empty,
    /// scratch: when the arithmetic equation certifier declines because a rewrite
    /// rule lemma it needs is NOT in theory scope (wellKnownFact resolves null),
    /// the rule name is recorded here so the certifier adapter can report the
    /// specific missing lemma instead of the generic "form not in certification
    /// scope". Set in `ruleIndex`, cleared/read per equation-certifier attempt.
    arith_missing_lemma: ?[]const u8 = null,
    /// innermost binding last: quantifier binders, proof vars, func params
    scope: std.ArrayList(ScopeEntry) = .empty,
    /// generator for hygienic binder fvar names ('#' cannot lex, so these can
    /// never collide with user identifiers)
    fresh_counter: u32 = 0,
    /// set while elaborating a schema body/proof: param name -> argument
    schema_args: ?*const SchemaArgs = null,
    /// schemas currently being instantiated, innermost last. A StatementId
    /// already on the stack means the schema (transitively) instantiates
    /// itself — a genuine cycle, reported as such. Depth is otherwise
    /// unbounded for terminating chains (only a huge backstop guards memory).
    instantiating: std.ArrayList(StatementId) = .empty,
    /// the file's forward manifest: names promised to be theorems, checked
    /// for existence and kind once the whole file has elaborated
    forwards: std.ArrayList(struct { name: StrId, loc: u32, text: []const u8 }) = .empty,
    /// proof-carrying schemas awaiting the strict declaration-time well-formedness
    /// check (opaque-parameter self-instantiation). Deferred to end-of-file so a
    /// schema whose body instantiates a LATER-declared schema still resolves.
    pending_schema_checks: std.ArrayList(struct { stmt_id: StatementId, params: []const ast.SchemaParam }) = .empty,
    /// proof obligations (TCCs) from guarded-function applications, emitted at
    /// the application and wrapped in logical context (binders, antecedents,
    /// left conjuncts) as elaboration returns upward. Discharged at the
    /// enclosing statement/step; an undischarged obligation fails the check.
    pending_tccs: std.ArrayList(Tcc) = .empty,
    /// RESULT POSTCONDITIONS surfaced by predicated-result funcs: when an
    /// application `op(x,y)` has a refined result (`func op(...): H`), `inH(op(x,y))`
    /// is asserted true by op's signature and pushed here — available for TCC
    /// discharge (so `f(op(x,y))` composes). Sound as the signature's assertion (an
    /// uninterpreted func's result-type is an axiom, like any). Accumulated during a
    /// statement/step's elaboration; the discharge consults it, then it is cleared.
    result_facts: std.ArrayList(TermId) = .empty,
    /// USE-ALL-FACTS support: extra reachability ROOTS for the dead-step walk —
    /// indices (into the current proof's lowered `steps`) of steps that are USED
    /// via an edge the kernel justification does NOT carry, so the walk would
    /// otherwise wrongly flag them dead. Two sources: (1) a step that DISCHARGED a
    /// proof obligation (TCC) — an elaboration-time α-match, recorded in
    /// `tccMatches`; (2) a step passed as an accelerant PREMISE (`c.refs`) whose
    /// citation edge the accelerant's lowering swallowed (`.accelerated` fallback /
    /// synthetic-theorem packaging), recorded at the accelerant dispatch.
    /// `checkAllStepsUsed` seeds reachability from all of these. Reset per proof in
    /// `checkProofSteps`. (See the REFACTOR NOTE on `checkAllStepsUsed`: a
    /// disciplined rebuild would fold these into one uniform use-relation.)
    extra_reachable_steps: std.ArrayList(u32) = .empty,

    /// declared `model`s, keyed by instance name. A cite `[by model(Name) thm]`
    /// looks the model up here and remaps `thm`'s formula through its `Remap`.
    models: std.AutoHashMapUnmanaged(StrId, Model) = .empty,

    /// PREDICATED `fix`/`unpack` blocks: `fix h: H { … }` (H a predicated sort)
    /// lowers to `fix h: G { assume inH(h) { … } }`. This maps the OUTER fix/unpack
    /// block to the injected guard-`assume` block, so `[by predicate <fixlabel>]`
    /// can surface `inH(h)` as that assume's hypothesis. Per-lowering (cleared with
    /// the proof); a fix without a predicated sort is absent from the map.
    fix_guard_block: std.AutoHashMapUnmanaged(kernel.BlockId, kernel.BlockId) = .empty,

    const Tcc = struct { formula: TermId, loc: u32 };

    /// A resolved `model` declaration: the interpretation (`remap`) plus the
    /// source theory's file (to resolve cited source theorems at their origin)
    /// and a location for diagnostics. Owned slices live in the arena.
    pub const Model = struct {
        remap: term.Pool.Remap,
        source_file: FileId,
        loc: u32,
        name: StrId,
        /// axiom obligations: source-axiom StatementId -> the local fact that
        /// discharges it. Strict materialization repoints an `axiom_ref` to a
        /// source axiom through this map. Absent source axioms are undischarged.
        stmt_map: []const StmtPair,
        /// memo of already-materialized source theorems (strict mode): source
        /// theorem StatementId -> the synthetic `Model$thm` StatementId. Keyed
        /// per model so all cites share the materialized copies. Grows lazily.
        materialized: std.AutoHashMapUnmanaged(StatementId, StatementId) = .empty,
    };

    pub const StmtPair = struct { from: StatementId, to: StatementId };

    const ScopeEntry = struct {
        /// user-facing name (what source text resolves against)
        name: StrId,
        sort: SortId,
        /// fvar identity in kernel terms: fresh for quantifier binders
        /// (closed away immediately), the user name for proof vars and params
        fvar: StrId,
    };

    pub const SchemaArgs = std.AutoHashMapUnmanaged(StrId, SchemaArg);
    pub const SchemaArg = union(enum) {
        value: Typed,
        /// N-argument generator. `body` holds the N binders as FREE fvars named
        /// `params[i]` (of sort `arg_sorts[i]`); application substitutes each via
        /// capture-free `substFvar` (no de Bruijn multi-binder bookkeeping — the
        /// kernel has no lambda node, and `open`/`close` assume a wrapping binder).
        /// A unary param (`Nat -> Prop`) is the 1-element case.
        lambda: struct { body: TermId, params: []const StrId, arg_sorts: []const SortId, result_sort: SortId },
    };

    pub const Typed = struct { id: TermId, sort: SortId };

    pub fn init(
        arena: Allocator,
        source: []const u8,
        interner: *InternPool,
        pool: *term.Pool,
        env: *Env,
        sink: *Diagnostics.Sink,
        file: FileId,
    ) Elaborator {
        return .{
            .arena = arena,
            .source = source,
            .interner = interner,
            .pool = pool,
            .env = env,
            .sink = sink,
            .file = file,
        };
    }

    pub fn text(self: *const Elaborator, tok: lexer.Token) []const u8 {
        return self.source[tok.start..tok.end];
    }

    pub fn internTok(self: *Elaborator, tok: lexer.Token) !StrId {
        return self.interner.internString(self.text(tok));
    }

    pub fn fail(self: *Elaborator, offset: u32, comptime fmt: []const u8, args: anytype) ElabError {
        self.sink.add(offset, fmt, args) catch return error.OutOfMemory;
        return error.Recover;
    }

    fn sortName(self: *const Elaborator, id: SortId) []const u8 {
        return self.env.sortName(self.interner, id);
    }

    pub fn elaborateFile(self: *Elaborator, file: ast.File) !void {
        for (file.decls) |*decl| {
            self.elaborateDecl(decl) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => continue, // diagnostic already recorded
            };
        }
        // strict schema well-formedness: now that every declaration is registered
        // (so a body may forward-reference a later schema), check each proof-
        // carrying schema's body at opaque parameters.
        for (self.pending_schema_checks.items) |pending| {
            self.checkSchemaBodyOpaque(pending.stmt_id, pending.params) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => continue, // diagnostic already recorded
            };
        }
        // verify the forward manifest: every promised theorem must now exist
        for (self.forwards.items) |fwd| {
            const stmt = self.env.findStatement(self.file, fwd.name) orelse {
                self.sink.add(fwd.loc, "forwarded theorem '{s}' is never defined", .{fwd.text}) catch return error.OutOfMemory;
                continue;
            };
            const kind_name: ?[]const u8 = switch (stmt.*) {
                .theorem => null, // ok
                .schema => |s| if (s.proof != null) null else "a parameterized axiom",
                .axiom => "an axiom",
            };
            if (kind_name) |k| {
                self.sink.add(fwd.loc, "'{s}' is forwarded as a theorem but defined as {s}", .{ fwd.text, k }) catch return error.OutOfMemory;
            }
        }
    }

    fn elaborateDecl(self: *Elaborator, decl: *const ast.Decl) ElabError!void {
        std.debug.assert(self.scope.items.len == 0);
        defer self.scope.clearRetainingCapacity();
        // obligations never survive a declaration (error paths may leave some)
        defer self.pending_tccs.clearRetainingCapacity();
        switch (decl.*) {
            .forward => |d| {
                try self.forwards.append(self.arena, .{
                    .name = try self.internTok(d.name),
                    .loc = d.name.start,
                    .text = self.text(d.name),
                });
            },
            .import => |d| {
                const name = try self.internTok(d.ns);
                try self.checkFreshName(name, d.ns);
                const path_text = self.text(d.path);
                const raw = self.interner.internString(path_text[1 .. path_text.len - 1]) catch return error.OutOfMemory;
                // the loader resolved (and diagnosed) imports; a missing entry
                // means it already reported — stay silent here
                const target = if (self.imports) |m| m.get(raw) else null;
                if (target) |t| try self.env.addNamespace(self.file, name, t);
            },
            .alias => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const target = try self.resolveTarget(d.target);
                switch (d.kind) {
                    .sort => {
                        const id = self.env.findSort(target.file, target.base) orelse
                            return self.fail(d.target.start, "'{s}' is not a sort", .{self.text(d.target)});
                        if (d.guard) |g| {
                            // predicated sort `sort H = G where inH`: a NEW SortId
                            // refining `id` (= G, itself possibly refined) by the
                            // guard `inH`. The pred must be unary over the target sort.
                            const gname = try self.internTok(g);
                            const gsym = self.env.findSym(self.file, gname) orelse
                                return self.fail(g.start, "predicated-sort guard '{s}' is not a predicate in scope", .{self.text(g)});
                            const sym = self.env.sym(gsym);
                            // A `where` guard naming a transparent (`define`d) pred is
                            // REIFIED (task #125): the guard is the define's inlined
                            // body (see qualifierApp), so the define rides along as a
                            // qualifier symbol exactly like an opaque pred — its uses
                            // expand. The unary-pred check below still applies (a
                            // define'd pred has kind == .pred and its declared arity).
                            // the guard must be a unary predicate over the target's
                            // CARRIER (a pred's arg sorts are stored lowered, so a
                            // pred over a refined target `B` has arg-sort = carrier).
                            const arg_ok = sym.arg_sorts.len == 1 and
                                self.env.carrierOf(sym.arg_sorts[0]) == self.env.carrierOf(id);
                            if (sym.kind != .pred or !arg_ok) {
                                return self.fail(g.start, "predicated-sort guard '{s}' must be a unary predicate over '{s}'", .{ self.text(g), self.text(d.target) });
                            }
                            const quals = try self.arena.dupe(term.SymId, &.{gsym});
                            _ = try self.env.addRefinedSort(self.file, name, d.name.start, id, quals);
                        } else {
                            // plain alias `sort H = G` — same SortId, no refinement.
                            try self.env.registerSort(self.file, name, id);
                        }
                    },
                    .constant, .func, .pred => {
                        const id = self.env.findSym(target.file, target.base) orelse
                            return self.fail(d.target.start, "'{s}' is not a {s}", .{ self.text(d.target), @tagName(d.kind) });
                        const sym = self.env.sym(id);
                        const ok = switch (d.kind) {
                            .constant => sym.kind == .app and sym.arg_sorts.len == 0,
                            .func => sym.kind == .app,
                            .pred => sym.kind == .pred,
                            else => unreachable,
                        };
                        if (!ok) {
                            return self.fail(d.target.start, "'{s}' is not a {s}", .{ self.text(d.target), @tagName(d.kind) });
                        }
                        try self.env.registerSym(self.file, name, id);
                    },
                    .axiom, .theorem => {
                        const id = self.env.findStatementId(target.file, target.base) orelse
                            return self.fail(d.target.start, "'{s}' is not a {s}", .{ self.text(d.target), @tagName(d.kind) });
                        const stmt = self.env.statements.items[@intFromEnum(id)];
                        // parameterized statements (schemas) alias under the
                        // keyword matching their epistemic kind
                        const ok = switch (d.kind) {
                            .axiom => stmt == .axiom or (stmt == .schema and stmt.schema.proof == null),
                            .theorem => stmt == .theorem or (stmt == .schema and stmt.schema.proof != null),
                            else => unreachable,
                        };
                        if (!ok) {
                            return self.fail(d.target.start, "'{s}' is not a {s}", .{ self.text(d.target), @tagName(d.kind) });
                        }
                        try self.env.registerStatement(self.file, name, id);
                    },
                }
            },
            .sort => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                _ = try self.env.addSort(self.file, name, d.name.start);
            },
            .constant => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                // a const may have a predicated sort (`const E: H`); the stored
                // (kernel) result sort is its carrier, but result_refined keeps the
                // refined sort so a reference to `E` surfaces `inH(E)` — asserting
                // E ∈ H by the const's signature (like a func result, nullary).
                const sort_refined = try self.resolveSort(d.sort);
                const sort = self.env.carrierOf(sort_refined);
                _ = try self.env.addSym(self.file, .{
                    .name = name,
                    .kind = .app,
                    .arg_sorts = &.{},
                    .result = sort,
                    .result_refined = sort_refined,
                    .guard = null,
                    .param_names = &.{},
                    .loc = d.name.start,
                });
            },
            .define => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                // a `define` is a MACRO: its body is elaborated ONCE here (with the
                // params in scope as fvars named after themselves), stored, and every
                // use expands to it with actuals substituted. The body may be a term
                // (a defined const/function) or a prop (a defined predicate) — the
                // kind is the body's sort. `params` empty = a nullary abbreviation.
                const arg_sorts, const param_names = try self.resolveParams(d.params);
                for (param_names, arg_sorts) |pn, ps| {
                    try self.scope.append(self.arena, .{ .name = pn, .sort = ps, .fvar = pn });
                }
                const tcc_start = self.pending_tccs.items.len;
                const value = try self.elaborateExpr(d.value);
                // guards inside the definition are owed once, here; uses
                // expand to the already-vetted body
                try self.dischargeTccs(null, @enumFromInt(0), tcc_start);
                self.scope.clearRetainingCapacity();
                _ = try self.env.addSym(self.file, .{
                    .name = name,
                    .kind = if (value.sort == .prop) .pred else .app,
                    .arg_sorts = arg_sorts,
                    .result = value.sort,
                    .guard = null,
                    .definition = value.id,
                    .param_names = param_names,
                    .loc = d.name.start,
                });
            },
            .func => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const arg_sorts, const param_names = try self.resolveParams(d.params);
                // a func result may be a predicated sort (`func op(...): H`); the
                // stored (kernel) result sort is its carrier, but the REFINED result
                // is kept (result_refined) so an application surfaces the result
                // postcondition `inH(op(...))` — sound as the signature's assertion.
                const result_refined = try self.resolveSort(d.result);
                const result = self.env.carrierOf(result_refined);
                if (result == .prop) {
                    return self.fail(d.result.start, "a func cannot return 'Prop'; declare a pred instead", .{});
                }
                var guard: ?TermId = null;
                if (d.requires) |req| {
                    // params in scope as fvars named after themselves
                    for (param_names, arg_sorts) |pn, ps| {
                        try self.scope.append(self.arena, .{ .name = pn, .sort = ps, .fvar = pn });
                    }
                    const tcc_start = self.pending_tccs.items.len;
                    const g = try self.elaborateExpr(req);
                    // guards must be guard-free, or obligations regress
                    if (self.pending_tccs.items.len > tcc_start) {
                        return self.fail(self.pending_tccs.items[tcc_start].loc, "a 'requires' clause may only mention total functions", .{});
                    }
                    guard = (try self.requireProp(g, req)).id;
                    self.scope.clearRetainingCapacity();
                }
                // PREDICATED ARG SORTS (`func f(x: H): R`): each H-typed param owes
                // `inH(x)` at every call. Fold those guards into the symbol's guard
                // formula (over the param fvars), reusing the requires/TCC machinery —
                // the obligation is emitted at each application (elaborateCall).
                for (d.params, param_names) |p, pn| {
                    const refined = try self.resolveBinderSort(p);
                    const quals = try self.sortQualifiers(refined);
                    if (quals.len == 0) continue;
                    const carrier = self.env.carrierOf(refined);
                    const pfv = try self.pool.add(.{ .fvar = .{ .name = pn, .sort = carrier } });
                    for (quals) |qpred| {
                        const app = try self.qualifierApp(qpred, pfv);
                        guard = if (guard) |prev| try self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = prev, .rhs = app } }) else app;
                    }
                }
                _ = try self.env.addSym(self.file, .{
                    .name = name,
                    .kind = .app,
                    .arg_sorts = arg_sorts,
                    .result = result,
                    .result_refined = result_refined,
                    .guard = guard,
                    .param_names = param_names,
                    .loc = d.name.start,
                });
            },
            .pred => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const arg_sorts, const param_names = try self.resolveParams(d.params);
                _ = try self.env.addSym(self.file, .{
                    .name = name,
                    .kind = .pred,
                    .arg_sorts = arg_sorts,
                    .result = .prop,
                    .guard = null,
                    .param_names = param_names,
                    .loc = d.name.start,
                });
            },
            .axiom => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const f = try self.elaborateExpr(d.formula);
                const typed = try self.requireProp(f, d.formula);
                // an axiom with unproved guard obligations must not enter the
                // environment: it would smuggle in unguarded applications
                try self.dischargeTccs(null, @enumFromInt(0), 0);
                _ = try self.env.addStatement(self.file, name, .{ .axiom = .{
                    .name = name,
                    .formula = typed.id,
                    .loc = d.name.start,
                } });
            },
            .hole => |d| {
                // mechanically an axiom, but marked a hole: default mode rejects
                // any proof that (transitively) rests on it; --draft allows it.
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const f = try self.elaborateExpr(d.formula);
                const typed = try self.requireProp(f, d.formula);
                try self.dischargeTccs(null, @enumFromInt(0), 0);
                _ = try self.env.addStatement(self.file, name, .{ .axiom = .{
                    .name = name,
                    .formula = typed.id,
                    .loc = d.name.start,
                    .is_hole = true,
                    .holes = try self.arena.dupe(StrId, &.{name}),
                } });
            },
            .schema => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                // lazy (comptime semantics): validate only the parameter
                // signature; the body is checked per instantiation.
                for (d.params) |p| {
                    try self.checkNoShadow(try self.internTok(p.name), p.name);
                    for (p.arg_sorts) |s| _ = try self.resolveSort(s);
                    _ = try self.resolveSort(p.result);
                }
                const stmt_id = try self.env.addStatement(self.file, name, .{ .schema = .{
                    .name = name,
                    .params = d.params,
                    .body = d.formula,
                    .proof = d.steps,
                    .file = self.file,
                    .source = self.source,
                    .loc = d.name.start,
                } });
                // STRICT well-formedness: in a fully-verifying run, check the
                // schema's proof body by instantiating it at fresh OPAQUE
                // parameters — a self-instantiation that catches structural errors
                // (rule arity, ref resolution, block shape) and most logical ones
                // without waiting for a concrete use site. DEFERRED to end-of-file
                // (a schema body may instantiate a schema declared later). In
                // --fast (certify_arithmetic=false) the body stays lazy, checked
                // only at real instantiations. See GUIDE.md "Schema well-formedness".
                if (self.verify.certify_arithmetic and d.steps != null) {
                    try self.pending_schema_checks.append(self.arena, .{ .stmt_id = stmt_id, .params = d.params });
                }
            },
            .theorem => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const f = try self.elaborateExpr(d.formula);
                const typed = try self.requireProp(f, d.formula);
                // the statement's own guard obligations must match a prior
                // axiom or proven theorem (no hypotheses exist at this level)
                try self.dischargeTccs(null, @enumFromInt(0), 0);
                // registered unproven first: a self-citation is then caught by
                // the kernel as "cites unproven theorem"
                _ = try self.env.addStatement(self.file, name, .{ .theorem = .{
                    .name = name,
                    .formula = typed.id,
                    .loc = d.name.start,
                    .proven = false,
                } });
                if (self.trusted) {
                    // imported without --recursive: the proof is NOT checked
                    const fact = &self.env.findStatement(self.file, name).?.theorem;
                    fact.proven = true;
                    fact.trusted = true;
                } else {
                    self.accelerated_used.clearRetainingCapacity();
                    self.holes_used.clearRetainingCapacity();
                    const lowered = try self.checkProofSteps(d.steps, typed.id, d.name.start);
                    if (lowered) |proof| {
                        const fact = &self.env.findStatement(self.file, name).?.theorem;
                        fact.proven = true;
                        fact.accelerated = try self.arena.dupe(StrId, self.accelerated_used.items);
                        fact.holes = try self.arena.dupe(StrId, self.holes_used.items);
                        // retain the lowered kernel proof so a `model` transfer
                        // can materialize a remapped copy in strict mode.
                        fact.proof = proof;
                    }
                }
            },
            .model => |d| try self.elaborateModel(d),
        }
    }

    /// Resolve a `model <Name> = <carrier> [where <guard>] { src: tgt ... }`
    /// declaration into a stored `Model` (an interpretation), keyed by name.
    /// Each mapping's source (a qualified theory entity) and target (a local
    /// entity) are resolved to ids; sorts feed the sort-map, funcs/consts/preds
    /// the sym-map. Axiom mappings are recorded but NOT checked here (the MVP
    /// `--fast` transfer trusts them; strict-mode obligation discharge is a
    /// later stage). See MODEL-DESIGN.md.
    fn elaborateModel(self: *Elaborator, d: anytype) ElabError!void {
        const name = try self.internTok(d.name);
        try self.checkFreshName(name, d.name);
        // No carrier/guard header — both are inferred from the mappings after they
        // are built (the guard from a predicated TARGET sort, below).

        var sort_map: std.ArrayList(term.Pool.Remap.SortPair) = .empty;
        var sym_map: std.ArrayList(term.Pool.Remap.SymPair) = .empty;
        var expands: std.ArrayList(term.Pool.Remap.Expand) = .empty;
        var stmt_map: std.ArrayList(StmtPair) = .empty;
        // schema discharges (source schema -> local schema) recorded for a
        // DEFERRED α-check: the check needs the finished remap (guard included),
        // which is only assembled after this mapping loop.
        var schema_pairs: std.ArrayList(StmtPair) = .empty;
        var source_file: ?FileId = null;

        for (d.mappings) |m| {
            const src = try self.resolveTarget(m.source);
            const tgt = try self.resolveTarget(m.target);
            // Source and target are distinguished by POSITION (left is source), not
            // by file: a subgroup models its own carrier, so the source theory may
            // be in THIS file (bare names) — an inlined `std/group.bpa`. Record the
            // source's file so cited source theorems resolve at their origin
            // (self.file for the same-file case). All sources must share one file.
            if (source_file) |sf| {
                if (sf != src.file) return self.fail(m.source.start, "all model mappings must come from one source theory", .{});
            } else source_file = src.file;

            // OPERATOR ↔ SOURCE-KIND check: `:` interprets a SORT or SYMBOL; `<-`
            // discharges an OBLIGATION (a source axiom, or an axiom-shaped schema).
            // A mismatch is a hard error — the two relations are distinct
            // (interpretation vs. verification), so the syntax states which the
            // author means. A THEOREM source is neither: it's not mappable at all,
            // and falls through to the "maps only axioms" rejection below
            // (regardless of operator), which is the more precise diagnostic.
            const is_sort = self.env.findSort(src.file, src.base) != null;
            const is_sym = self.env.findSym(src.file, src.base) != null;
            const src_stmt: ?Statement = if (!is_sort and !is_sym)
                if (self.env.findStatementId(src.file, src.base)) |sid| self.env.statements.items[@intFromEnum(sid)] else null
            else
                null;
            // an obligation source = an axiom, or a schema with no proof (a
            // parameterized axiom). A proof-carrying schema / theorem is derived.
            const src_is_obligation = if (src_stmt) |st| switch (st) {
                .axiom => true,
                .schema => |s| s.proof == null,
                .theorem => false,
            } else false;
            switch (m.kind) {
                .symbol => if (src_is_obligation) return self.fail(m.source.start, "'{s}' is an axiom obligation, not a sort/symbol — discharge it with `<-` (`{s} <- <local fact>`), not `:`", .{ self.text(m.source), self.text(m.source) }),
                // `<-` requires an obligation source. A sort/symbol under `<-` is a
                // clear "use `:`" error; a theorem under `<-` falls through to the
                // theorem-rejection below (drop it entirely).
                .obligation => if (is_sort or is_sym) return self.fail(m.source.start, "'{s}' is a sort or symbol, not an axiom — map it with `:` (`{s}: <target>`), not `<-`", .{ self.text(m.source), self.text(m.source) }),
            }

            // dispatch on what the source entity is: sort, symbol, or statement.
            if (self.env.findSort(src.file, src.base)) |from_sort| {
                const to_sort = self.env.findSort(tgt.file, tgt.base) orelse
                    return self.fail(m.target.start, "'{s}' is not a sort", .{self.text(m.target)});
                try sort_map.append(self.arena, .{ .from = from_sort, .to = to_sort });
            } else if (self.env.findSym(src.file, src.base)) |from_sym| {
                // A `define`d (transparent) SOURCE symbol is not a model mapping entity:
                // it IS its body, so it rides along on the primitive symbols in that body
                // (which the model maps). Nominally remapping the transparent source would
                // remap the NAME while ignoring its definition — definition-blind and
                // unsound. Reject; map the body's primitives instead. (A transparent
                // TARGET is fine — mapping a source symbol onto a defined target
                // expression is legitimate; the target expands to its body.)
                if (self.env.sym(from_sym).definition != null) {
                    return self.fail(m.source.start, "'{s}' is a transparent (`define`d) symbol — it rides along on the primitives in its body and cannot be a model mapping source; map those primitives instead", .{self.text(m.source)});
                }
                const to_sym = self.env.findSym(tgt.file, tgt.base) orelse
                    return self.fail(m.target.start, "'{s}' is not a function/predicate", .{self.text(m.target)});
                // a transparent (`define`d) TARGET: the source symbol expands to the
                // target's BODY (not an application of the defined name, which would
                // leave a dangling `DEFINED` in the transferred formula).
                if (self.env.sym(to_sym).definition) |body| {
                    try expands.append(self.arena, .{ .from = from_sym, .body = body });
                } else {
                    try sym_map.append(self.arena, .{ .from = from_sym, .to = to_sym });
                }
            } else if (self.env.findStatementId(src.file, src.base)) |from_stmt| {
                // a model discharges the source theory's AXIOM obligations only. A
                // source THEOREM is derived, so it materializes automatically through
                // the mapped axioms — mapping it explicitly is misusing `model`
                // (redundant at best, a silent override at worst). Reject it. This
                // holds for BOTH the plain and `@`-projection forms — if a guarded
                // transfer fails to auto-materialize a theorem, the fix is to make the
                // materializer emit it, never to re-permit a theorem mapping.
                if (self.env.statements.items[@intFromEnum(from_stmt)] == .theorem) {
                    return self.fail(m.source.start, "model maps only axioms; '{s}' is a theorem — it materializes through the mapped axioms, so drop this mapping", .{self.text(m.source)});
                }
                // axiom obligation: the local fact `to_stmt` discharges the source
                // axiom `from_stmt`. `<model>@<projected>` (the projection form)
                // discharges it by transferring `projected` THROUGH the named model
                // and binding that materialized statement; otherwise a plain local fact.
                const to_stmt = if (m.projection) |proj|
                    try self.resolveModelProjection(m.target, proj)
                else
                    self.env.findStatementId(tgt.file, tgt.base) orelse
                        return self.fail(m.target.start, "'{s}' is not an axiom/theorem", .{self.text(m.target)});
                // A SCHEMA source (an induction/recursion family) is discharged by a
                // local schema whose statement is the guard-relativized remap of the
                // source's body — verified below once the remap is built. The target
                // MUST itself be a schema (a ground axiom/theorem cannot instantiate).
                if (self.env.statements.items[@intFromEnum(from_stmt)] == .schema) {
                    if (self.env.statements.items[@intFromEnum(to_stmt)] != .schema) {
                        return self.fail(m.target.start, "'{s}' discharges a schema, so it must itself be a schema (with a matching predicate parameter)", .{self.text(m.target)});
                    }
                    try schema_pairs.append(self.arena, .{ .from = from_stmt, .to = to_stmt });
                }
                try stmt_map.append(self.arena, .{ .from = from_stmt, .to = to_stmt });
            } else {
                return self.fail(m.source.start, "unknown model mapping source '{s}'", .{self.text(m.source)});
            }
        }

        const sorts = try sort_map.toOwnedSlice(self.arena);

        // INFER the guard from the mappings: the model is guarded exactly when a
        // sort-mapping's TARGET is a PREDICATED sort (`group.Grp: H`, `H = Grp where
        // inH`). That mapping supplies both `Guard.carrier` (the SOURCE sort — the
        // relativization keys on the pre-remap binder sort) and `Guard.pred` (the
        // target sort's qualifier). At most one such mapping is expected.
        // A guard is INTRODUCED only when a NON-predicated source sort maps to a
        // PREDICATED target (`group.Grp: H` — group's plain carrier becomes the inH
        // subset). When the SOURCE is already predicated (`subgroup.Sub: H`,
        // Sub itself `= Grp where inSubgroup`), the source theorem is ALREADY
        // relativized; the mapping just CARRIES the guard across (the source's
        // qualifier pred remaps via sym_map) — no new relativization.
        var guard: ?term.Pool.Remap.Guard = null;
        for (sorts) |p| {
            if (!self.env.isRefined(p.to)) continue;
            if (self.env.isRefined(p.from)) continue;
            const quals = self.env.qualifiersOf(self.arena, p.to) catch return error.OutOfMemory;
            guard = .{ .pred = quals[0], .carrier = p.from };
        }
        // the sort-map must lower predicated targets to their CARRIER for the kernel
        // remap (H -> Grp), since the guard now carries the relativization.
        for (sorts) |*p| p.to = self.env.carrierOf(p.to);

        const remap: term.Pool.Remap = .{
            .sorts = sorts,
            .syms = try sym_map.toOwnedSlice(self.arena),
            .guard = guard,
            .expands = try expands.toOwnedSlice(self.arena),
        };
        // SOUNDNESS GATE: each schema discharge's statement must α-equal the
        // guard-relativized remap of the source schema's body. Checked here, once,
        // at the DECL — a wrong discharge is caught even if never cited.
        for (schema_pairs.items) |sp| try self.checkSchemaDischarge(sp.from, sp.to, remap, d.name.start);
        try self.models.put(self.arena, name, .{
            .remap = remap,
            .source_file = source_file orelse self.file,
            .loc = d.name.start,
            .name = name,
            .stmt_map = try stmt_map.toOwnedSlice(self.arena),
        });
    }

    /// A `<model>@<projected>` mapping value: discharge an obligation by transferring
    /// the `projected` theorem THROUGH the model named `model_tok`. Resolves the
    /// declared model, resolves `projected` (a theorem in that model's source), and
    /// materializes the transfer into a synthetic statement — returning its id (the
    /// discharging `to_stmt`). This is nested-model materialization: the outer model
    /// discharges via the inner model's reified output.
    fn resolveModelProjection(self: *Elaborator, model_tok: lexer.Token, projected: lexer.Token) ElabError!StatementId {
        const mname = try self.internTok(model_tok);
        const model = self.models.getPtr(mname) orelse
            return self.fail(model_tok.start, "'{s}' is not a declared model", .{self.text(model_tok)});
        const proj = try self.resolveTarget(projected);
        const source_stmt = self.env.findStatementId(proj.file, proj.base) orelse
            return self.fail(projected.start, "'{s}' is not an axiom/theorem", .{self.text(projected)});
        return accel_model.materializeThrough(self, model, source_stmt, projected.start);
    }

    // --- proof lowering: surface Fitch tree -> kernel steps + blocks ---

    pub const Lowering = struct {
        steps: std.ArrayList(kernel.Step) = .empty,
        blocks: std.ArrayList(kernel.Block) = .empty,
        labels: std.AutoHashMapUnmanaged(StrId, LabelTarget) = .empty,

        const LabelTarget = union(enum) { step: kernel.StepId, block: kernel.BlockId };
    };

    /// Lower and kernel-check a proof. Returns the LOWERED proof if proven
    /// (retained on the Fact for `model` materialization), else null. Lowering
    /// errors record a diagnostic and yield null (the file continues).
    fn checkProofSteps(self: *Elaborator, steps: []const ast.Step, goal: TermId, goal_loc: u32) Allocator.Error!?Statement.LoweredProof {
        var low: Lowering = .{};
        // `extra_reachable_steps` is per-proof reachability state (TCC dischargers +
        // accelerant premises) indexed into THIS proof's `low.steps`, consumed by
        // `checkAllStepsUsed` below. checkProofSteps is RE-ENTRANT: lowering a schema
        // `instantiate` step re-verifies the schema body via a nested checkProofSteps
        // (recheck_schemas), which has its own, disjoint step indexing. So SAVE the
        // outer proof's accumulator, run this proof fresh, and RESTORE on exit — the
        // nested call fully consumes its own roots before returning, so discarding
        // them afterward is correct, and the outer proof's roots (recorded before the
        // instantiate step) survive. Without this the nested clear orphaned the
        // outer's accelerant-premise roots → a false "unused fact" under --fast (where
        // the accelerant emits no kernel citation edge to reach the premise otherwise).
        const saved_roots = self.extra_reachable_steps;
        self.extra_reachable_steps = .empty;
        defer self.extra_reachable_steps = saved_roots;
        const root_label = try self.interner.internString("proof");
        try low.blocks.append(self.arena, .{
            .parent = null,
            .label = root_label,
            .kind = .root,
            .first_step = 0,
            .last_step = 0,
        });
        self.lowerSteps(&low, steps, @enumFromInt(0)) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return null,
        };
        low.blocks.items[0].last_step = @intCast(low.steps.items.len);

        var k: kernel.Kernel = .{
            .arena = self.arena,
            .pool = self.pool,
            .env = self.env,
            .interner = self.interner,
            .sink = self.sink,
        };
        const proven = k.check(
            .{ .steps = low.steps.items, .blocks = low.blocks.items },
            goal,
            goal_loc,
        );
        if (!(try proven)) return null;
        // no dead steps: every step must be reachable from the conclusion via
        // citation edges (a proof must USE all the facts it introduces). `--draft`
        // (a WIP proof may have not-yet-wired facts) skips this.
        if (!self.verify.draft) {
            if (try self.checkAllStepsUsed(low.steps.items, low.blocks.items) == false) return null;
        }
        return .{ .steps = low.steps.items, .blocks = low.blocks.items };
    }

    /// USE-ALL-FACTS: every AUTHOR-WRITTEN step must be reachable from the
    /// conclusion via citation edges — a proof that introduces a fact it never
    /// uses (a dead step) is rejected. Backward reachability from the conclusion:
    /// a step's justification cites SRefs (mark those steps) and BRefs (mark the
    /// referenced block's concluding step, which cascades through its subtree);
    /// AND, since an `unpack` block's existential source is an edge carried on the
    /// BLOCK (`kind.unpack.source`) rather than on any step justification, marking
    /// any step inside an unpack block also marks that source. Any unmarked step
    /// is dead — EXCEPT accelerant-emitted synthetics (hygienic `#`-labels): those
    /// are machine-generated micro-derivations behind a single author `[by …]`
    /// line, not author facts, so they are walked-through but never reported.
    /// Returns false (and records one diagnostic) if any authored step is dead,
    /// true otherwise. Gated off by `--draft`.
    ///
    /// REFACTOR NOTE: reachability here is stitched together from several
    /// SEPARATE edge sources — step-justification SRefs/BRefs (below), the
    /// block-carried `unpack.source` edge, and the `extra_reachable_steps` roots
    /// (TCC dischargers + accelerant premises whose edges the lowering swallowed).
    /// Each is a use that the kernel/elaborator already knows about but expresses
    /// in its own representation. When the proof IR is
    /// refactored we want ONE generic notion of "what does this step depend on"
    /// (a uniform dependency/use relation every construct populates), so this walk
    /// — and anyone else asking "is X used?" — consumes that instead of
    /// re-deriving each edge kind by hand. Until then, every NEW edge-bearing
    /// construct must be taught to this walk explicitly (as unpack/TCC were).
    fn checkAllStepsUsed(self: *Elaborator, steps: []const kernel.Step, blocks: []const kernel.Block) Allocator.Error!bool {
        if (steps.len == 0) return true;
        const reached = try self.arena.alloc(bool, steps.len);
        @memset(reached, false);
        // the last owned step of a block is its "result" — what a BRef consumes.
        const lastStepOf = struct {
            fn f(bs: []const kernel.Block, b: kernel.BlockId) ?u32 {
                const blk = bs[@intFromEnum(b)];
                if (blk.last_step > blk.first_step) return blk.last_step - 1;
                return null;
            }
        }.f;
        // seed: the concluding step (last step owned by the root block).
        var seed: ?u32 = null;
        {
            var it: usize = steps.len;
            while (it > 0) {
                it -= 1;
                if (@intFromEnum(steps[it].block) == 0) {
                    seed = @intCast(it);
                    break;
                }
            }
        }
        const start = seed orelse return true;
        var work: std.ArrayList(u32) = .empty;
        try work.append(self.arena, start);
        reached[start] = true;
        // also seed from `extra_reachable_steps` (TCC dischargers + accelerant
        // premises): each is genuinely used, but via an edge the kernel
        // justification doesn't carry — so it is a reachability root alongside the
        // conclusion. (See the field doc for the two sources.)
        for (self.extra_reachable_steps.items) |di| try mark(reached, &work, self.arena, di);
        while (work.pop()) |si| {
            // block edges: a reached step's enclosing `unpack` blocks (up the
            // ancestor chain) depend on their existential source step. Mark each.
            {
                var b: ?kernel.BlockId = steps[si].block;
                while (b) |bid| {
                    const blk = blocks[@intFromEnum(bid)];
                    if (blk.kind == .unpack) try mark(reached, &work, self.arena, @intFromEnum(blk.kind.unpack.source.id));
                    b = blk.parent;
                }
            }
            const j = steps[si].just;
            // every SRef the justification cites → the cited step is used.
            switch (j) {
                .modus_ponens => |r| {
                    try mark(reached, &work, self.arena, @intFromEnum(r.implication.id));
                    try mark(reached, &work, self.arena, @intFromEnum(r.antecedent.id));
                },
                .forall_elim => |r| try mark(reached, &work, self.arena, @intFromEnum(r.step.id)),
                .exists_intro => |r| try mark(reached, &work, self.arena, @intFromEnum(r.step.id)),
                .and_intro => |r| {
                    try mark(reached, &work, self.arena, @intFromEnum(r.left.id));
                    try mark(reached, &work, self.arena, @intFromEnum(r.right.id));
                },
                .and_elim_left, .and_elim_right, .or_intro_left, .or_intro_right, .double_negation, .symmetry => |sr| try mark(reached, &work, self.arena, @intFromEnum(sr.id)),
                .rewrite => |r| {
                    try mark(reached, &work, self.arena, @intFromEnum(r.equation.id));
                    try mark(reached, &work, self.arena, @intFromEnum(r.target.id));
                },
                .iff_rewrite => |r| {
                    try mark(reached, &work, self.arena, @intFromEnum(r.biconditional.id));
                    try mark(reached, &work, self.arena, @intFromEnum(r.target.id));
                },
                .absurd => |r| {
                    try mark(reached, &work, self.arena, @intFromEnum(r.s1.id));
                    try mark(reached, &work, self.arena, @intFromEnum(r.s2.id));
                },
                .not_intro => |r| {
                    if (lastStepOf(blocks, r.block.id)) |ls| try mark(reached, &work, self.arena, ls);
                    try mark(reached, &work, self.arena, @intFromEnum(r.s1.id));
                    try mark(reached, &work, self.arena, @intFromEnum(r.s2.id));
                },
                .or_elim => |r| {
                    try mark(reached, &work, self.arena, @intFromEnum(r.disj.id));
                    if (lastStepOf(blocks, r.left.id)) |ls| try mark(reached, &work, self.arena, ls);
                    if (lastStepOf(blocks, r.right.id)) |ls| try mark(reached, &work, self.arena, ls);
                },
                .implies_intro, .forall_intro, .exists_elim => |b| {
                    if (lastStepOf(blocks, b.id)) |ls| try mark(reached, &work, self.arena, ls);
                },
                // a `hypothesis`/`predicate` restatement asserts its block's OWN
                // premise (assume-condition / fix-guard / unpack witness) — no step
                // dependency. (An unpack block's source is marked via the block-edge
                // pass above, when a step inside it is reached.)
                .hypothesis => {},
                .schema_instance => |r| for (r.premises) |p| try mark(reached, &work, self.arena, @intFromEnum(p.id)),
                // axiom_ref / theorem_ref / reflexivity / accelerated: no step deps.
                .axiom_ref, .theorem_ref, .reflexivity, .accelerated => {},
            }
        }
        // any unmarked AUTHOR step is dead — report the FIRST one (source order).
        // Accelerant-emitted synthetics (hygienic `#`-labels) are exempt: they are
        // machine codegen behind one author `[by …]` line, not author facts, and
        // their internal wiring need not be a clean cite-tree.
        // Report EVERY unreached author step (the whole dead cluster), not just the
        // first — a dead step often feeds another dead step, so listing all of them
        // at once lets the author remove the cluster in one pass rather than
        // rerunning the check per step. Synthetics (hygienic `#`-labels) are exempt.
        var any_dead = false;
        for (steps, 0..) |s, i| {
            if (reached[i]) continue;
            const label = self.interner.stringBytes(s.label);
            if (std.mem.indexOfScalar(u8, label, '#') != null) continue; // synthetic
            self.sink.add(s.loc, "unused fact: step '{s}' is never used — no later step or the conclusion cites it (a proof must use every fact it introduces; use --draft while filling in a proof)", .{label}) catch return error.OutOfMemory;
            any_dead = true;
        }
        return !any_dead;
    }

    fn mark(reached: []bool, work: *std.ArrayList(u32), arena: Allocator, id: u32) Allocator.Error!void {
        if (id >= reached.len or reached[id]) return;
        reached[id] = true;
        try work.append(arena, id);
    }

    /// Lower a block's sibling steps. Labels resolve across the whole block
    /// regardless of textual order: the steps are topologically sorted by
    /// their intra-block citations before lowering, so a step may cite a
    /// later-written label. The kernel still receives strictly-backward
    /// references (dependencies lower first); a citation cycle is a located
    /// error. Ties break by textual order, so already-ordered proofs lower
    /// identically to before.
    /// A unit of pending lowering work. The block-nesting recursion
    /// (`lowerSteps → lowerOneStep → lowerSteps` for assume/fix/unpack steps) is
    /// linearized onto an explicit heap stack of these, so lowering a proof of any
    /// nesting depth cannot overflow the native call stack. LIFO discipline: for a
    /// block step we push its `.exit_block` FIRST then its children in reverse topo
    /// order, so children pop in topo order and the exit (closeBlock + optional
    /// scope.pop) fires exactly when the block's subtree is fully drained. The block
    /// + its subtree therefore occupy a CONTIGUOUS `[first_step, last_step)` step
    /// span (the invariant `kernel.zig` checkEigen/lastFormula/checkClosedBlockRef
    /// rely on) — because `newBlock` (which stamps `first_step`) runs at POP time,
    /// and nothing but this block's own children can append a step above it.
    const WorkItem = union(enum) {
        lower_step: struct { step: *const ast.Step, block_id: kernel.BlockId },
        exit_block: struct { block_id: kernel.BlockId, pop_scope: bool },
    };

    /// Seed the entry block's siblings and run the iterative lowering loop. The
    /// work-stack is a LOCAL (not an Elaborator field) so schema-instantiate
    /// re-entrancy (a nested checkProofSteps) and per-arm case drives each get an
    /// independent stack. No longer self-recurses.
    fn lowerSteps(self: *Elaborator, low: *Lowering, steps: []const ast.Step, block_id: kernel.BlockId) ElabError!void {
        var stack: std.ArrayList(WorkItem) = .empty;
        try self.pushBlockBody(low, &stack, steps, block_id);
        while (stack.pop()) |item| {
            switch (item) {
                .exit_block => |e| {
                    self.closeBlock(low, e.block_id);
                    if (e.pop_scope) _ = self.scope.pop();
                },
                .lower_step => |ls| try self.driveOneStep(low, &stack, ls.step, ls.block_id),
            }
        }
    }

    /// Validate the sibling group's labels (no duplicates, no shadowing of an
    /// enclosing label), topo-sort them, and push each as a `.lower_step` in REVERSE
    /// topo order so they pop in topo order. Runs at block-enter (the root seed and
    /// each block-opening step's driveOneStep), exactly where `lowerSteps` did this
    /// per sibling-group before.
    fn pushBlockBody(self: *Elaborator, low: *Lowering, stack: *std.ArrayList(WorkItem), steps: []const ast.Step, block_id: kernel.BlockId) ElabError!void {
        var index_of: std.AutoHashMapUnmanaged(StrId, usize) = .empty;
        for (steps, 0..) |*s, i| {
            const label = try self.internTok(s.label);
            if (self.labelInScope(low, label, block_id)) {
                return self.fail(s.label.start, "label '{s}' shadows an enclosing label; choose a fresh name", .{self.text(s.label)});
            }
            const gop = index_of.getOrPut(self.arena, label) catch return error.OutOfMemory;
            if (gop.found_existing) {
                return self.fail(s.label.start, "duplicate label '{s}'", .{self.text(s.label)});
            }
            gop.value_ptr.* = i;
        }
        const order = try self.topoSortSteps(steps, index_of);
        var i = order.len;
        while (i > 0) {
            i -= 1;
            try stack.append(self.arena, .{ .lower_step = .{ .step = &steps[order[i]], .block_id = block_id } });
        }
    }

    /// Is `label` already defined in `block_id` or an enclosing (ancestor)
    /// block — i.e. would (re)defining it here be *shadowing*? A label defined
    /// in a disjoint, already-closed sibling block is NOT in scope (reuse is
    /// fine); only the ancestor chain counts. Labels linger in `low.labels`
    /// after their block closes (parent discharge rules still cite into closed
    /// subproofs), so scope is decided structurally, by walking parents.
    fn labelInScope(self: *Elaborator, low: *const Lowering, label: StrId, block_id: kernel.BlockId) bool {
        _ = self;
        const target = low.labels.get(label) orelse return false;
        // the block the label lives *in*: a step's own block; a sub-block label
        // is registered in its parent's scope, so its home is that parent.
        const home: ?kernel.BlockId = switch (target) {
            .step => |id| low.steps.items[@intFromEnum(id)].block,
            .block => |id| low.blocks.items[@intFromEnum(id)].parent,
        };
        var cur: ?kernel.BlockId = block_id;
        while (cur) |c| {
            if (home == c) return true;
            cur = low.blocks.items[@intFromEnum(c)].parent;
        }
        return false;
    }

    /// Citations a step makes to labels *in its own block* (intra-block
    /// dependency edges). Enclosing-block labels and statement names are not
    /// edges — they are already available.
    fn stepSiblingDeps(step: *const ast.Step, index_of: std.AutoHashMapUnmanaged(StrId, usize), interner: *InternPool, source: []const u8, out: *std.ArrayList(usize), arena: Allocator) !void {
        const tok = struct {
            fn ref(t: lexer.Token, idx: std.AutoHashMapUnmanaged(StrId, usize), in: *InternPool, src: []const u8, o: *std.ArrayList(usize), a: Allocator) !void {
                const name = in.internString(src[t.start..t.end]) catch return error.OutOfMemory;
                if (idx.get(name)) |dep| try o.append(a, dep);
            }
        };
        switch (step.body) {
            .claim => |c| for (c.refs) |r| try tok.ref(r, index_of, interner, source, out, arena),
            .unpack => |blk| try tok.ref(blk.from, index_of, interner, source, out, arena),
            .case => |c| try tok.ref(c.disj, index_of, interner, source, out, arena),
            .assume, .fix => {}, // no header citations
        }
    }

    /// Topologically sort the sibling steps so every intra-block citation
    /// points to an earlier position. Kahn's algorithm; ties (independent
    /// steps) resolve in textual order for stable, unchanged output. A cycle
    /// is reported by name.
    fn topoSortSteps(self: *Elaborator, steps: []const ast.Step, index_of: std.AutoHashMapUnmanaged(StrId, usize)) ElabError![]const usize {
        const n = steps.len;
        // deps[i] = the sibling indices step i cites; dependents count for Kahn
        const deps = try self.arena.alloc([]const usize, n);
        const remaining = try self.arena.alloc(usize, n); // unlowered deps of i
        for (steps, 0..) |*s, i| {
            var d: std.ArrayList(usize) = .empty;
            try stepSiblingDeps(s, index_of, self.interner, self.source, &d, self.arena);
            deps[i] = d.items;
            remaining[i] = d.items.len;
        }
        var order: std.ArrayList(usize) = .empty;
        // repeatedly emit the lowest-index step whose deps are all emitted
        var emitted = try self.arena.alloc(bool, n);
        @memset(emitted, false);
        while (order.items.len < n) {
            var progressed = false;
            for (0..n) |i| {
                if (emitted[i] or remaining[i] != 0) continue;
                emitted[i] = true;
                try order.append(self.arena, i);
                // decrement dependents: any j citing i now has one fewer dep
                for (0..n) |j| {
                    if (emitted[j]) continue;
                    for (deps[j]) |dj| {
                        if (dj == i) remaining[j] -= 1;
                    }
                }
                progressed = true;
                break; // restart scan from lowest index for textual-order ties
            }
            if (!progressed) return self.reportCycle(steps, deps, emitted);
        }
        return order.items;
    }

    /// Emit a located "cyclic justification: a -> b -> ... -> a" error from
    /// the remaining unemitted steps (which form at least one cycle).
    fn reportCycle(self: *Elaborator, steps: []const ast.Step, deps: []const []const usize, emitted: []const bool) ElabError {
        // find a cycle by walking dependency edges among unemitted nodes
        var start: usize = 0;
        while (start < steps.len and emitted[start]) start += 1;
        var path: std.ArrayList(usize) = .empty;
        var on_path = self.arena.alloc(bool, steps.len) catch return error.OutOfMemory;
        @memset(on_path, false);
        var cur = start;
        while (!on_path[cur]) {
            on_path[cur] = true;
            path.append(self.arena, cur) catch return error.OutOfMemory;
            // step into the first unemitted dependency
            var next: ?usize = null;
            for (deps[cur]) |d| {
                if (!emitted[d]) {
                    next = d;
                    break;
                }
            }
            cur = next orelse break; // should not happen: a stuck node has a dep
        }
        // the cycle is path[first-occurrence-of-cur .. ] then cur again
        var msg: std.Io.Writer.Allocating = .init(self.arena);
        var started = false;
        for (path.items) |i| {
            if (!started and i != cur) continue;
            started = true;
            msg.writer.print("{s} -> ", .{self.text(steps[i].label)}) catch return error.OutOfMemory;
        }
        msg.writer.print("{s}", .{self.text(steps[cur].label)}) catch return error.OutOfMemory;
        return self.fail(steps[cur].label.start, "cyclic justification: {s}", .{msg.written()});
    }

    /// Lower one sibling step (claim or sub-block). Its label's real id is
    /// recorded here; because callers lower in topological order, any label
    /// this step cites is already resolved.
    /// Lower one step. The three BLOCK arms (assume/fix/unpack) do their ENTER work
    /// (elaborate/bind/newBlock/label) then SCHEDULE the block's exit + children onto
    /// `stack` instead of recursing — pushing `.exit_block` first so it pops last
    /// (after the whole subtree). The `.claim`/`.case` arms are byte-identical to the
    /// old recursive `lowerOneStep` (no scheduling; `.case`'s emitCaseTree stays
    /// recursive, bounded by arm count, not proof depth).
    fn driveOneStep(self: *Elaborator, low: *Lowering, stack: *std.ArrayList(WorkItem), s: *const ast.Step, block_id: kernel.BlockId) ElabError!void {
        const label = try self.internTok(s.label);
        switch (s.body) {
            .assume => |blk| {
                const tcc_start = self.pending_tccs.items.len;
                const f = try self.requireProp(try self.elaborateExpr(blk.formula), blk.formula);
                // the assumption's guards are owed in the PARENT context
                try self.dischargeTccs(low, block_id, tcc_start);
                const b = try self.newBlock(low, label, block_id, .{ .assume = f.id });
                low.labels.put(self.arena, label, .{ .block = b }) catch return error.OutOfMemory;
                // exit under the children (no scope frame for assume), then children.
                try stack.append(self.arena, .{ .exit_block = .{ .block_id = b, .pop_scope = false } });
                try self.pushBlockBody(low, stack, blk.steps, b);
            },
            .fix => |blk| {
                const v = try self.bindProofVar(blk.name, blk.sort);
                // a PREDICATED fix (`fix h: H`) carries the guard `inH(h)` on the
                // block: it becomes the block's hypothesis (`[by predicate <lbl>]`)
                // and the antecedent of the `forall_intro` conclusion.
                const guard = try self.fixGuard(blk.sort, v);
                const b = try self.newBlock(low, label, block_id, .{ .fix = .{ .v = v, .guard = guard } });
                low.labels.put(self.arena, label, .{ .block = b }) catch return error.OutOfMemory;
                // exit pops the eigenvariable scope frame AFTER the subtree drains.
                try stack.append(self.arena, .{ .exit_block = .{ .block_id = b, .pop_scope = true } });
                try self.pushBlockBody(low, stack, blk.steps, b);
            },
            .unpack => |blk| {
                const source = try self.resolveStepRef(low, blk.from);
                const v = try self.bindProofVar(blk.name, blk.sort);
                const b = try self.newBlock(low, label, block_id, .{ .unpack = .{ .v = v, .source = source } });
                low.labels.put(self.arena, label, .{ .block = b }) catch return error.OutOfMemory;
                try stack.append(self.arena, .{ .exit_block = .{ .block_id = b, .pop_scope = true } });
                try self.pushBlockBody(low, stack, blk.steps, b);
            },
            .claim => |c| {
                const tcc_start = self.pending_tccs.items.len;
                const f = try self.requireProp(try self.elaborateExpr(c.formula), c.formula);
                const just = try self.lowerJustification(low, block_id, f.id, c);
                // guards owed by the claim (and by rule arguments/schema
                // instances) are discharged in this step's context
                try self.dischargeTccs(low, block_id, tcc_start);
                low.labels.put(self.arena, label, .{ .step = @enumFromInt(low.steps.items.len) }) catch return error.OutOfMemory;
                try low.steps.append(self.arena, .{
                    .formula = f.id,
                    .just = just,
                    .block = block_id,
                    .label = label,
                    .loc = s.label.start,
                });
            },
            .case => |c| try self.lowerCase(low, s, block_id, label, c),
        }
    }

    /// Lower a `case` step: eliminate the cited disjunction (optionally after
    /// unpacking an existential witness) by fanning out the user's arms into a
    /// nested `or_elim` tree. The step's own claim is the shared goal; every
    /// arm must conclude it. The kernel checks the synthesized or_elim tree
    /// exactly as if hand-written, so this adds no trust.
    fn lowerCase(self: *Elaborator, low: *Lowering, s: *const ast.Step, block_id: kernel.BlockId, label: StrId, c: ast.Step.CaseBlock) ElabError!void {
        const loc = s.label.start;
        const goal_tcc = self.pending_tccs.items.len;
        // the case step advances a goal, stated on the step line like a claim
        const goal = try self.requireProp(try self.elaborateExpr(c.goal), c.goal);
        try self.dischargeTccs(low, block_id, goal_tcc);
        // the goal is a normal step in this block, justified by the (possibly
        // nested) or_elim tree fanned out over the cited disjunction's arms.
        const disj = try self.resolveStepRef(low, c.disj);
        const just = try self.emitCaseTree(low, block_id, loc, disj, c.arms, goal.id);
        low.labels.put(self.arena, label, .{ .step = @enumFromInt(low.steps.items.len) }) catch return error.OutOfMemory;
        try low.steps.append(self.arena, .{ .formula = goal.id, .just = just, .block = block_id, .label = label, .loc = loc });
    }

    /// Lower one `case` arm as a fresh `assume <disjunct>` block whose steps are
    /// the arm's body; returns the block. The block's conclusion is checked by
    /// the kernel to match the arm's disjunct and the shared goal.
    fn emitArmBlock(self: *Elaborator, low: *Lowering, parent: kernel.BlockId, arm: ast.Step.CaseBlock.Arm, expected: TermId) ElabError!kernel.BlockId {
        const f = try self.requireProp(try self.elaborateExpr(arm.assumption), arm.assumption);
        if (!self.pool.alphaEq(f.id, expected)) {
            return self.fail(exprLoc(arm.assumption), "case arm assumes '{s}', but the disjunct here is '{s}'", .{
                try self.renderTerm(f.id), try self.renderTerm(expected),
            });
        }
        const b = try self.newBlock(low, try self.internTok(arm.label), parent, .{ .assume = f.id });
        low.labels.put(self.arena, try self.internTok(arm.label), .{ .block = b }) catch return error.OutOfMemory;
        try self.lowerSteps(low, arm.steps, b);
        self.closeBlock(low, b);
        return b;
    }

    /// Fan the arms out over the (left-nested) disjunction `disj_formula`,
    /// proved by step `disj`, into a nested `or_elim` tree concluding `goal`.
    /// Returns the justification proving `goal` in `parent`.
    fn emitCaseTree(self: *Elaborator, low: *Lowering, parent: kernel.BlockId, loc: u32, disj: kernel.SRef, arms: []const ast.Step.CaseBlock.Arm, goal: TermId) ElabError!kernel.Justification {
        const disj_formula = low.steps.items[@intFromEnum(disj.id)].formula;
        const node = self.pool.get(disj_formula);
        if (node != .bin or node.bin.op != .or_op) {
            return self.fail(loc, "case: 'on' step is '{s}', not a disjunction", .{try self.renderTerm(disj_formula)});
        }
        if (arms.len < 2) {
            return self.fail(loc, "case over a disjunction needs at least two arms", .{});
        }
        // right arm (last) matches the rhs disjunct; the lhs holds the rest.
        const right_block = try self.emitArmBlock(low, parent, arms[arms.len - 1], node.bin.rhs);
        const left_block = if (arms.len == 2)
            try self.emitArmBlock(low, parent, arms[0], node.bin.lhs)
        else blk: {
            // lhs is itself `L or R`: an assume block that re-splits it.
            const lb = try self.newBlock(low, try self.freshNamed("case"), parent, .{ .assume = node.bin.lhs });
            const hyp = try self.emitStep(low, lb, loc, node.bin.lhs, .{ .hypothesis = .{ .id = lb, .loc = loc } });
            const inner = try self.emitCaseTree(low, lb, loc, hyp, arms[0 .. arms.len - 1], goal);
            _ = try self.emitStep(low, lb, loc, goal, inner);
            self.closeBlock(low, lb);
            break :blk lb;
        };
        return .{ .or_elim = .{
            .disj = disj,
            .left = .{ .id = left_block, .loc = loc },
            .right = .{ .id = right_block, .loc = loc },
        } };
    }

    pub fn newBlock(self: *Elaborator, low: *Lowering, label: StrId, parent: kernel.BlockId, kind: kernel.Block.Kind) ElabError!kernel.BlockId {
        const id: kernel.BlockId = @enumFromInt(low.blocks.items.len);
        try low.blocks.append(self.arena, .{
            .parent = parent,
            .label = label,
            .kind = kind,
            .first_step = @intCast(low.steps.items.len),
            .last_step = 0,
        });
        return id;
    }

    pub fn closeBlock(self: *Elaborator, low: *Lowering, id: kernel.BlockId) void {
        _ = self;
        const blk = &low.blocks.items[@intFromEnum(id)];
        blk.last_step = @intCast(low.steps.items.len);
        // Contiguity tripwire (Debug only): the iterative work-stack must give this
        // block + its whole subtree a CONTIGUOUS [first_step, last_step) span — the
        // kernel's checkEigen/lastFormula/checkClosedBlockRef rely on it. Every step
        // in the range must belong to this block or a descendant of it; none may
        // belong to an unrelated (ancestor/sibling) block.
        if (std.debug.runtime_safety) {
            const self_idx = @intFromEnum(id);
            var i: usize = blk.first_step;
            while (i < blk.last_step) : (i += 1) {
                // Walk this step's block up its ancestor chain. Blocks are allocated
                // in DFS order, so a descendant's index always exceeds its ancestor's;
                // the walk strictly decreases and must pass THROUGH `id` iff the step
                // lies in this block's subtree. Stop once the index drops to/below
                // `self_idx` — hitting `id` means in-subtree, anything else is an
                // interleaving bug the contiguity invariant forbids.
                var bi = @intFromEnum(low.steps.items[i].block);
                while (bi > self_idx) {
                    // a descendant (index > self_idx) always has a non-null parent.
                    bi = @intFromEnum(low.blocks.items[bi].parent.?);
                }
                std.debug.assert(bi == self_idx);
            }
        }
    }

    /// fix/unpack variable. Zig's rule: no *shadowing* — the name must be fresh
    /// against every enclosing-scope variable and every declaration, but a
    /// disjoint sibling subproof MAY reuse it.
    ///
    /// The kernel identifies an eigenvariable by its interned name, so two
    /// disjoint `fix x` blocks that both used the bare name `x` would produce
    /// representationally identical eigenvariables — and closing the second with
    /// `forall_intro` would trip `checkEigen` on the first block's (closed)
    /// `x`-steps, which the kernel cannot tell apart. To keep sibling reuse
    /// sound AND accepted, we bind the fix var to a FRESH disambiguated identity
    /// `x#<n>` in kernel terms while keeping the source name `x` for scope
    /// lookups and shadow-checks. `#` is not a legal identifier character, so
    /// the disambiguated name can never collide with a userland name, and the
    /// printer trims each fvar at `#` so proofs still render `x` (see
    /// `print.zig` `displayName`).
    fn bindProofVar(self: *Elaborator, name_tok: lexer.Token, sort_tok: lexer.Token) ElabError!term.Node.Fvar {
        const name = try self.internTok(name_tok);
        for (self.scope.items) |entry| {
            if (entry.name == name) {
                return self.fail(name_tok.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(name_tok)});
            }
        }
        if (self.env.findSym(self.file, name) != null) {
            return self.fail(name_tok.start, "'{s}' shadows a declaration; choose a fresh name", .{self.text(name_tok)});
        }
        // the eigenvariable's KERNEL sort is the carrier (a predicated fix/unpack
        // sort `H` lowers to `G`); the guard is applied separately by the fix/unpack
        // lowering (which re-resolves the sort token to get H's qualifiers).
        const sort = self.env.carrierOf(try self.resolveSort(sort_tok));
        const fvar = try self.freshNamed(self.text(name_tok));
        try self.scope.append(self.arena, .{ .name = name, .sort = sort, .fvar = fvar });
        return .{ .name = fvar, .sort = sort };
    }

    pub fn resolveStepRef(self: *Elaborator, low: *Lowering, tok: lexer.Token) ElabError!kernel.SRef {
        const name = try self.internTok(tok);
        const target = low.labels.get(name) orelse {
            // A common mistake is naming an axiom/theorem/schema where a proof
            // STEP is required (e.g. `forall_elim(a) unionMember` instead of
            // materializing `@ax | ... [by axiom unionMember]` first, then
            // `forall_elim(a) ax`). Detect that and point at the fix rather than
            // reporting a bare "unknown reference".
            const name_text = self.text(tok);
            if (self.statementByName(name)) |stmt| {
                // article + the intro keyword that materializes this kind as a step
                const desc: []const u8, const intro: []const u8 = switch (stmt) {
                    .axiom => .{ "an axiom", "axiom" },
                    .theorem => .{ "a theorem", "theorem" },
                    .schema => .{ "a schema", "instantiate" },
                };
                return self.fail(tok.start, "'{s}' is {s}, not a proof step; introduce it as a step first with `[by {s} {s}]`, then reference that step", .{
                    name_text, desc, intro, name_text,
                });
            }
            return self.fail(tok.start, "unknown reference '{s}'", .{name_text});
        };
        return switch (target) {
            .step => |id| .{ .id = id, .loc = tok.start },
            .block => self.fail(tok.start, "'{s}' names a subproof; a step reference is required", .{self.text(tok)}),
        };
    }

    /// Look up a statement (axiom/theorem/schema) visible by name in the theory
    /// scope or the current file — used to sharpen "unknown reference" hints.
    fn statementByName(self: *Elaborator, name: StrId) ?Statement {
        const id = self.env.findStatementId(self.theoryScope(), name) orelse
            self.env.findStatementId(self.file, name) orelse return null;
        return self.env.statements.items[@intFromEnum(id)];
    }

    fn resolveBlockRef(self: *Elaborator, low: *Lowering, tok: lexer.Token) ElabError!kernel.BRef {
        const name = try self.internTok(tok);
        const target = low.labels.get(name) orelse {
            return self.fail(tok.start, "unknown reference '{s}'", .{self.text(tok)});
        };
        return switch (target) {
            .block => |id| .{ .id = id, .loc = tok.start },
            .step => self.fail(tok.start, "'{s}' names a step; a subproof reference is required", .{self.text(tok)}),
        };
    }

    pub fn resolveStatementRef(self: *Elaborator, tok: lexer.Token) ElabError!StatementId {
        const target = try self.resolveTarget(tok);
        return self.env.findStatementId(target.file, target.base) orelse
            self.fail(tok.start, "unknown statement '{s}'", .{self.text(tok)});
    }

    /// What a cited ref resolves to, in the caller's proof: a caller-LOCAL step
    /// (a hypothesis / prior derived fact — only in scope here), or a GLOBAL
    /// statement (axiom/theorem in the environment). Accelerant-agnostic
    /// mechanics: an accelerant that wants to CLOSE its refs (e.g. make each a
    /// premise of a context-free synthetic theorem) uses this to decide, per
    /// ref, how it appears in the signature and how it is discharged at the
    /// cite. `formula` is the ref's stated formula either way.
    pub const RefTarget = union(enum) {
        local_step: struct { sref: kernel.SRef, formula: TermId },
        global: struct { stmt: StatementId, formula: TermId, is_theorem: bool },
    };

    pub fn refTarget(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, tok: lexer.Token) ElabError!RefTarget {
        const name = try self.internTok(tok);
        if (low.labels.get(name)) |target| switch (target) {
            .step => |sid| {
                const s = low.steps.items[@intFromEnum(sid)];
                if (!lowAncestorOrSelf(low, s.block, block_id)) {
                    return self.fail(tok.start, "'{s}' is not accessible from this step (closed subproof)", .{self.text(tok)});
                }
                return .{ .local_step = .{ .sref = .{ .id = sid, .loc = tok.start }, .formula = s.formula } };
            },
            .block => return self.fail(tok.start, "'{s}' names a subproof; a formula reference is required", .{self.text(tok)}),
        };
        const stmt_id = try self.resolveStatementRef(tok);
        const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
        return switch (stmt) {
            .axiom => |a| .{ .global = .{ .stmt = stmt_id, .formula = a.formula, .is_theorem = false } },
            .theorem => |t| blk: {
                if (!t.proven) return self.fail(tok.start, "cites unproven theorem '{s}'", .{self.text(tok)});
                break :blk .{ .global = .{ .stmt = stmt_id, .formula = t.formula, .is_theorem = true } };
            },
            .schema => self.fail(tok.start, "'{s}' is a schema; a formula reference is required", .{self.text(tok)}),
        };
    }

    const RuleKind = enum {
        axiom,
        theorem,
        hypothesis,
        predicate,
        modus_ponens,
        implies_intro,
        forall_intro,
        forall_elim,
        exists_intro,
        exists_elim,
        and_intro,
        and_elim_left,
        and_elim_right,
        // iff sugar: an `iff` desugars to `(P -> Q) and (Q -> P)`, so these are
        // thin renames of the `and` rules that read naturally on a biconditional.
        iff_intro,
        iff_elim_forward,
        iff_elim_backward,
        or_intro_left,
        or_intro_right,
        or_elim,
        not_intro,
        absurd,
        double_negation,
        reflexivity,
        symmetry,
        rewrite,
        iff_rewrite,
        instantiate,
        specialize,
        chain,
        simplify,
        simplify_quantified,
        ac,
        ac_quantified,
        assoc,
        assoc_quantified,
        polynomial,
        polynomial_quantified,
        tautology,
        arithmetic,
        ext,
        ext_quantified,
        model,
    };

    const rule_names = std.StaticStringMap(RuleKind).initComptime(.{
        .{ "axiom", .axiom },
        .{ "theorem", .theorem },
        .{ "hypothesis", .hypothesis },
        .{ "predicate", .predicate },
        .{ "modus_ponens", .modus_ponens },
        .{ "implies_intro", .implies_intro },
        .{ "forall_intro", .forall_intro },
        .{ "forall_elim", .forall_elim },
        .{ "exists_intro", .exists_intro },
        .{ "exists_elim", .exists_elim },
        .{ "and_intro", .and_intro },
        .{ "and_elim_left", .and_elim_left },
        .{ "and_elim_right", .and_elim_right },
        .{ "iff_intro", .iff_intro },
        .{ "iff_elim_forward", .iff_elim_forward },
        .{ "iff_elim_backward", .iff_elim_backward },
        .{ "or_intro_left", .or_intro_left },
        .{ "or_intro_right", .or_intro_right },
        .{ "or_elim", .or_elim },
        .{ "not_intro", .not_intro },
        .{ "absurd", .absurd },
        .{ "double_negation", .double_negation },
        .{ "symmetry", .symmetry },
        .{ "reflexivity", .reflexivity },
        .{ "rewrite", .rewrite },
        .{ "iff_rewrite", .iff_rewrite },
        .{ "instantiate", .instantiate },
        .{ "specialize", .specialize },
        .{ "chain", .chain },
        .{ "simplify", .simplify },
        .{ "simplify_quantified", .simplify_quantified },
        .{ "assoc_commut", .ac },
        .{ "assoc_commut_quantified", .ac_quantified },
        .{ "assoc", .assoc },
        .{ "assoc_quantified", .assoc_quantified },
        .{ "polynomial", .polynomial },
        .{ "polynomial_quantified", .polynomial_quantified },
        .{ "tautology", .tautology },
        .{ "arithmetic", .arithmetic },
        .{ "ext", .ext },
        .{ "ext_quantified", .ext_quantified },
        .{ "model", .model },
    });

    /// A term has *biconditional shape* iff it is `(X -> Y) and (Y -> X)` for
    /// matching X, Y — i.e. exactly what `P iff Q` desugars to. Such a shape is
    /// ALWAYS a biconditional (there is no legitimate non-iff reading of two
    /// mutually-inverse implications conjoined), so it is the canonical iff form:
    /// `iff_intro` requires it, and `and_intro` is forbidden from producing it
    /// (use `iff_intro` — the surface should say what it means).
    fn isBiconditionalShape(self: *const Elaborator, id: TermId) bool {
        const n = self.pool.get(id);
        if (n != .bin or n.bin.op != .and_op) return false;
        const l = self.pool.get(n.bin.lhs);
        const r = self.pool.get(n.bin.rhs);
        if (l != .bin or l.bin.op != .implies) return false;
        if (r != .bin or r.bin.op != .implies) return false;
        // left is `X -> Y`, right must be `Y -> X`
        return self.pool.alphaEq(l.bin.lhs, r.bin.rhs) and
            self.pool.alphaEq(l.bin.rhs, r.bin.lhs);
    }

    fn lowerJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const kind = rule_names.get(self.text(c.rule)) orelse {
            return self.fail(c.rule.start, "unknown rule '{s}'", .{self.text(c.rule)});
        };
        // argument-count discipline
        const wants_args: usize = switch (kind) {
            // forall_elim specializes at one OR MORE arguments (a multi-arg
            // call emits the intermediate chain); zero arguments is an error.
            .forall_elim => if (c.args.len == 0) 1 else c.args.len,
            .exists_intro => 1,
            .instantiate => c.args.len, // schema-dependent, checked in M4
            .specialize => c.args.len, // theorem-dependent (the ∀-prefix arity)
            // assoc_commut takes an OPTIONAL explicit AC triple
            // `(assoc, comm, swap)` for a custom operator; bare = well-known
            // add/mul. Exactly-0-or-3 is validated inside the tactic.
            .ac, .ac_quantified => c.args.len,
            // assoc REQUIRES exactly one arg (the associativity lemma); the
            // "requires an associativity lemma" message is emitted in the
            // tactic so a bare `assoc` gets a helpful error, not a generic one.
            .assoc, .assoc_quantified => c.args.len,
            else => 0,
        };
        if (c.args.len != wants_args) {
            return self.fail(c.rule.start, "'{s}' expects {d} argument(s), got {d}", .{
                self.text(c.rule), wants_args, c.args.len,
            });
        }
        // accelerated tactics dispatch through the registry (one uniform call);
        // kernel-primitive rules fall through to the switch below.
        if (accelerant_index.get(self.text(c.rule))) |i| {
            // USE-ALL-FACTS: an accelerant CONSUMES its `c.refs` (premises), but its
            // lowering may swallow the citation edge (an `.accelerated` fallback
            // carries only the tactic name; a certificate may package a premise
            // into a synthetic theorem). Record each ref that names a local step as
            // a reachability root so the dead-step walk sees the use. Uses the
            // NON-failing label lookup — a ref naming an axiom/theorem/block simply
            // isn't a `.step` and is skipped (no diagnostic).
            for (c.refs) |ref| {
                const name = try self.internTok(ref);
                if (low.labels.get(name)) |tgt| switch (tgt) {
                    .step => |id| self.extra_reachable_steps.append(self.arena, @intFromEnum(id)) catch {},
                    .block => {},
                };
            }
            return accelerants[i].justify(self, low, block_id, goal, c);
        }
        switch (kind) {
            .axiom => {
                try self.wantRefs(c, 1);
                const stmt_id = try self.resolveStatementRef(c.refs[0]);
                // a `hole` is stored as an axiom-kind Fact with is_hole set;
                // citing one makes the current theorem rest on that hole.
                const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
                if (stmt == .axiom and stmt.axiom.is_hole) try self.inheritHoles(stmt.axiom.holes);
                return .{ .axiom_ref = .{ .stmt = stmt_id, .loc = c.refs[0].start } };
            },
            .theorem => {
                try self.wantRefs(c, 1);
                const stmt_id = try self.resolveStatementRef(c.refs[0]);
                const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
                if (stmt == .theorem) {
                    try self.inheritAccelerated(stmt.theorem.accelerated);
                    try self.inheritHoles(stmt.theorem.holes);
                }
                return .{ .theorem_ref = .{ .stmt = stmt_id, .loc = c.refs[0].start } };
            },
            .hypothesis => {
                try self.wantRefs(c, 1);
                return .{ .hypothesis = try self.resolveBlockRef(low, c.refs[0]) };
            },
            // `predicate <fix-label>` surfaces the GUARD of a predicated fix/unpack
            // binder (`fix h: H` gives `inH(h)`). Kernel-identical to `hypothesis`
            // (the kernel's hypothesisOf returns a guarded fix's guard); a distinct
            // keyword so the source reads as "the sort's predicate", not an assume.
            .predicate => {
                try self.wantRefs(c, 1);
                return .{ .hypothesis = try self.resolveBlockRef(low, c.refs[0]) };
            },
            .modus_ponens => {
                try self.wantRefs(c, 2);
                return .{ .modus_ponens = .{
                    .implication = try self.resolveStepRef(low, c.refs[0]),
                    .antecedent = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            .implies_intro => {
                try self.wantRefs(c, 1);
                return .{ .implies_intro = try self.resolveBlockRef(low, c.refs[0]) };
            },
            .forall_intro => {
                try self.wantRefs(c, 1);
                return .{ .forall_intro = try self.resolveBlockRef(low, c.refs[0]) };
            },
            .forall_elim => {
                try self.wantRefs(c, 1);
                // `forall_elim(A, B, C) ref` specializes at several arguments
                // in one written step: each argument but the last emits an
                // intermediate forall_elim step (kernel-checked as usual); the
                // last becomes this step's own justification.
                var cur = try self.resolveStepRef(low, c.refs[0]);
                var cur_formula = low.steps.items[@intFromEnum(cur.id)].formula;
                for (c.args[0 .. c.args.len - 1]) |arg_expr| {
                    const node = self.pool.get(cur_formula);
                    if (node != .quant or node.quant.q != .forall) {
                        return self.fail(exprLoc(arg_expr), "forall_elim: '{s}' is not universally quantified here", .{try self.renderTerm(cur_formula)});
                    }
                    const arg = try self.elaborateExpr(arg_expr);
                    const opened = try self.pool.open(node.quant.body, arg.id);
                    cur = try self.emitStep(low, block_id, exprLoc(arg_expr), opened, .{
                        .forall_elim = .{ .step = cur, .with = arg.id, .with_loc = exprLoc(arg_expr) },
                    });
                    cur_formula = opened;
                }
                const last = c.args[c.args.len - 1];
                const arg = try self.elaborateExpr(last);
                return .{ .forall_elim = .{
                    .step = cur,
                    .with = arg.id,
                    .with_loc = exprLoc(last),
                } };
            },
            .exists_intro => {
                try self.wantRefs(c, 1);
                const arg = try self.elaborateExpr(c.args[0]);
                return .{ .exists_intro = .{
                    .step = try self.resolveStepRef(low, c.refs[0]),
                    .witness = arg.id,
                    .witness_loc = exprLoc(c.args[0]),
                } };
            },
            .exists_elim => {
                try self.wantRefs(c, 1);
                return .{ .exists_elim = try self.resolveBlockRef(low, c.refs[0]) };
            },
            .and_intro => {
                try self.wantRefs(c, 2);
                // `(X -> Y) and (Y -> X)` is canonically a biconditional — route it
                // through `iff_intro` so the surface names what it means.
                if (self.isBiconditionalShape(goal)) {
                    return self.fail(c.rule.start, "this goal is a biconditional '(X -> Y) and (Y -> X)' — use `iff_intro` (which is the same rule, named for what it proves)", .{});
                }
                return .{ .and_intro = .{
                    .left = try self.resolveStepRef(low, c.refs[0]),
                    .right = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            .and_elim_left => {
                try self.wantRefs(c, 1);
                return .{ .and_elim_left = try self.resolveStepRef(low, c.refs[0]) };
            },
            .and_elim_right => {
                try self.wantRefs(c, 1);
                return .{ .and_elim_right = try self.resolveStepRef(low, c.refs[0]) };
            },
            // iff sugar: `P iff Q` desugars to `(P -> Q) and (Q -> P)`, so
            // iff_intro/forward/backward reduce to the `and` rules. iff_intro
            // takes the forward (`P -> Q`) then backward (`Q -> P`) directions;
            // forward projects the left conjunct, backward the right.
            .iff_intro => {
                try self.wantRefs(c, 2);
                // iff_intro's goal must be a biconditional shape (which every
                // `P iff Q` desugars to). Reject a plain conjunction — that is
                // `and_intro`'s job.
                if (!self.isBiconditionalShape(goal)) {
                    return self.fail(c.rule.start, "iff_intro's goal must be a biconditional (from `P iff Q`); this goal is not of the form '(X -> Y) and (Y -> X)' — did you mean `and_intro`?", .{});
                }
                return .{ .and_intro = .{
                    .left = try self.resolveStepRef(low, c.refs[0]),
                    .right = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            .iff_elim_forward => {
                try self.wantRefs(c, 1);
                return .{ .and_elim_left = try self.resolveStepRef(low, c.refs[0]) };
            },
            .iff_elim_backward => {
                try self.wantRefs(c, 1);
                return .{ .and_elim_right = try self.resolveStepRef(low, c.refs[0]) };
            },
            .or_intro_left => {
                try self.wantRefs(c, 1);
                return .{ .or_intro_left = try self.resolveStepRef(low, c.refs[0]) };
            },
            .or_intro_right => {
                try self.wantRefs(c, 1);
                return .{ .or_intro_right = try self.resolveStepRef(low, c.refs[0]) };
            },
            .or_elim => {
                try self.wantRefs(c, 3);
                return .{ .or_elim = .{
                    .disj = try self.resolveStepRef(low, c.refs[0]),
                    .left = try self.resolveBlockRef(low, c.refs[1]),
                    .right = try self.resolveBlockRef(low, c.refs[2]),
                } };
            },
            .not_intro => {
                try self.wantRefs(c, 3);
                return .{ .not_intro = .{
                    .block = try self.resolveBlockRef(low, c.refs[0]),
                    .s1 = try self.resolveStepRef(low, c.refs[1]),
                    .s2 = try self.resolveStepRef(low, c.refs[2]),
                } };
            },
            .absurd => {
                try self.wantRefs(c, 2);
                return .{ .absurd = .{
                    .s1 = try self.resolveStepRef(low, c.refs[0]),
                    .s2 = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            .double_negation => {
                try self.wantRefs(c, 1);
                return .{ .double_negation = try self.resolveStepRef(low, c.refs[0]) };
            },
            .reflexivity => {
                try self.wantRefs(c, 0);
                return .reflexivity;
            },
            .symmetry => {
                try self.wantRefs(c, 1);
                return .{ .symmetry = try self.resolveStepRef(low, c.refs[0]) };
            },
            .rewrite => {
                try self.wantRefs(c, 2);
                return .{ .rewrite = .{
                    .equation = try self.resolveStepRef(low, c.refs[0]),
                    .target = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            // `iff_rewrite <biconditional> <target>`: replace the sub-proposition
            // P by Q (from `P iff Q`) throughout `target`'s formula — the prop
            // analogue of `rewrite`. First ref is the iff fact, second the target.
            .iff_rewrite => {
                try self.wantRefs(c, 2);
                return .{ .iff_rewrite = .{
                    .biconditional = try self.resolveStepRef(low, c.refs[0]),
                    .target = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            .instantiate => {
                const name_tok = c.schema.?; // parser guarantees presence
                const stmt_id = try self.resolveStatementRef(name_tok);
                const stmt = &self.env.statements.items[@intFromEnum(stmt_id)];
                if (stmt.* != .schema) {
                    return self.fail(name_tok.start, "'{s}' is not a schema", .{self.text(name_tok)});
                }
                const inst = try self.instantiateSchema(stmt_id, &stmt.schema, c);
                const premises = try self.arena.alloc(kernel.SRef, c.refs.len);
                for (c.refs, premises) |r, *out| out.* = try self.resolveStepRef(low, r);
                return .{ .schema_instance = .{ .instance = inst, .premises = premises } };
            },
            // accelerated tactics were dispatched through the registry above
            // (`specialize` among them — it emits a forall_elim+modus_ponens chain).
            .simplify, .simplify_quantified, .ac, .ac_quantified, .assoc, .assoc_quantified, .polynomial, .polynomial_quantified, .tautology, .arithmetic, .ext, .ext_quantified, .model, .specialize, .chain => unreachable,
        }
    }

    /// Check obligations [start..] against what is available, then drop them.
    /// ALL undischarged obligations are reported (not just the first), each
    /// with its exact formula in copy-pasteable surface syntax.
    fn dischargeTccs(self: *Elaborator, low: ?*const Lowering, block_id: kernel.BlockId, start: usize) ElabError!void {
        if (self.trusted) {
            self.pending_tccs.shrinkRetainingCapacity(start);
            return;
        }
        var any_failed = false;
        for (self.pending_tccs.items[start..]) |t| {
            if (!try self.tccDischarged(low, block_id, t.formula)) {
                const rendered = @import("print.zig").render(self.arena, self.pool, self.env, self.interner, t.formula) catch return error.OutOfMemory;
                self.sink.add(t.loc, "unproved obligation: '{s}'", .{rendered}) catch return error.OutOfMemory;
                any_failed = true;
            }
        }
        self.pending_tccs.shrinkRetainingCapacity(start);
        // surfaced result postconditions are valid within the enclosing statement;
        // clear them at the statement boundary (start == 0). Within a statement they
        // accumulate and remain matchable (they are TRUE facts about in-scope terms;
        // α-match requires the exact same term, so lingering is sound).
        if (start == 0) self.result_facts.clearRetainingCapacity();
        if (any_failed) return error.Recover;
    }

    /// An obligation is discharged by an EXACT (alpha-equal) match against an
    /// axiom, a proven theorem, an in-scope hypothesis, or an accessible step
    /// — NO proof search. Before matching, the obligation is decomposed
    /// structurally (deterministic, linear): `forall x. B` introduces a fresh
    /// eigenvariable, `A -> B` moves A into local hypotheses. This makes
    /// tautological wrappers (`d != ZERO -> d != ZERO`) self-discharging while
    /// anything substantive still requires an explicit lemma or step.
    fn tccDischarged(self: *Elaborator, low: ?*const Lowering, block_id: kernel.BlockId, formula: TermId) ElabError!bool {
        var hyps: std.ArrayList(TermId) = .empty;
        return self.tccDischargedHyps(low, block_id, formula, &hyps);
    }

    fn tccDischargedHyps(self: *Elaborator, low: ?*const Lowering, block_id: kernel.BlockId, formula: TermId, hyps: *std.ArrayList(TermId)) ElabError!bool {
        var f = formula;
        while (true) {
            for (hyps.items) |h| {
                if (self.pool.alphaEq(h, f)) return true;
            }
            if (self.tccMatches(low, block_id, f)) return true;
            const node = self.pool.get(f);
            if (node == .bin and node.bin.op == .implies) {
                try hyps.append(self.arena, node.bin.lhs);
                f = node.bin.rhs;
                continue;
            }
            // a conjunction obligation is discharged by discharging BOTH conjuncts
            // (and-intro), each under the accumulated hypotheses. Needed for a
            // predicated func's multi-arg guard `inH(a) and inH(b)`.
            if (node == .bin and node.bin.op == .and_op) {
                return (try self.tccDischargedHyps(low, block_id, node.bin.lhs, hyps)) and
                    (try self.tccDischargedHyps(low, block_id, node.bin.rhs, hyps));
            }
            if (node == .quant and node.quant.q == .forall) {
                const fresh = try self.freshName();
                const fv = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
                f = try self.pool.open(node.quant.body, fv);
                continue;
            }
            return false;
        }
    }

    fn tccMatches(self: *Elaborator, low: ?*const Lowering, block_id: kernel.BlockId, f: TermId) bool {
        // result postconditions surfaced by predicated-result funcs (`op(x,y): H`
        // asserts inH(op(x,y))).
        for (self.result_facts.items) |fact| {
            if (self.pool.alphaEq(fact, f)) return true;
        }
        for (self.env.statements.items) |stmt| {
            const known: TermId = switch (stmt) {
                .axiom => |a| a.formula,
                .theorem => |t| if (t.proven) t.formula else continue,
                .schema => continue,
            };
            if (self.pool.alphaEq(known, f)) return true;
        }
        const l = low orelse return false;
        // hypotheses on the ancestor chain: an `assume` block's assumption, and a
        // PREDICATED `fix h: H` block's guard `inH(h)` (surfaced by the sort).
        var cur: ?kernel.BlockId = block_id;
        while (cur) |c| {
            const b = l.blocks.items[@intFromEnum(c)];
            switch (b.kind) {
                .assume => |a| if (self.pool.alphaEq(a, f)) return true,
                .fix => |fx| if (fx.guard) |g| {
                    if (self.pool.alphaEq(g, f)) return true;
                },
                else => {},
            }
            cur = b.parent;
        }
        // accessible prior steps
        for (l.steps.items, 0..) |s, i| {
            if (!lowAncestorOrSelf(l, s.block, block_id)) continue;
            if (self.pool.alphaEq(s.formula, f)) {
                // this step discharges the obligation — a real (non-citation) use.
                // Record it so the dead-step walk doesn't flag it. (Best-effort:
                // OOM here just means the walk may over-report; not a soundness
                // issue, so swallow the error rather than fail elaboration.)
                self.extra_reachable_steps.append(self.arena, @intCast(i)) catch {};
                return true;
            }
        }
        return false;
    }

    pub fn lowAncestorOrSelf(low: *const Lowering, a: kernel.BlockId, b: kernel.BlockId) bool {
        var cur: ?kernel.BlockId = b;
        while (cur) |c| {
            if (c == a) return true;
            cur = low.blocks.items[@intFromEnum(c)].parent;
        }
        return false;
    }

    /// Monomorphize a schema at concrete, written-down arguments (comptime
    /// semantics). Value params substitute a term; generator params
    /// beta-reduce a single-argument lambda at the term level (capture-proof:
    /// all terms involved are locally closed). A proof-carrying schema has its
    /// proof re-elaborated and kernel-checked at THIS instance.
    fn statementName(stmt: Statement) StrId {
        return switch (stmt) {
            .axiom => |f| f.name,
            .theorem => |f| f.name,
            .schema => |s| s.name,
        };
    }

    /// Model SOUNDNESS GATE: verify a schema discharge. `src` is the source
    /// theory's schema (e.g. peano.induction), `dst` a local schema the model
    /// maps it to. Both are instantiated at ONE shared opaque predicate symbol;
    /// the source instance is remapped through the model, and the two bodies must
    /// be α-equal — i.e. the discharge's statement IS the guard-relativized remap
    /// of the source. (Lambda args are substituted structurally, not re-typechecked,
    /// so the same opaque symbol serves both the source-sorted and target-sorted
    /// binder — `alphaEq` keys on the symbol id, not its declared sort.)
    fn checkSchemaDischarge(self: *Elaborator, src: StatementId, dst: StatementId, remap: term.Pool.Remap, loc: u32) ElabError!void {
        const src_schema = &self.env.statements.items[@intFromEnum(src)].schema;
        const dst_schema = &self.env.statements.items[@intFromEnum(dst)].schema;
        if (src_schema.params.len != dst_schema.params.len) {
            return self.fail(loc, "schema discharge '{s}' has {d} parameter(s); the source schema '{s}' has {d}", .{
                self.interner.stringBytes(dst_schema.name), dst_schema.params.len,
                self.interner.stringBytes(src_schema.name),  src_schema.params.len,
            });
        }

        // one shared opaque symbol per parameter position; build a source-sorted
        // and a target-sorted lambda over each (same symbol id in both).
        var src_args: SchemaArgs = .empty;
        var dst_args: SchemaArgs = .empty;
        // param sorts resolve in their OWN schema's file scope (a source param's
        // sort token indexes the source file, not the consumer's).
        const src_ctx0: Ctx = .{ .source = src_schema.source, .file = src_schema.file, .diag = @intFromEnum(src_schema.file) };
        const dst_ctx0: Ctx = .{ .source = dst_schema.source, .file = dst_schema.file, .diag = @intFromEnum(dst_schema.file) };
        for (src_schema.params, dst_schema.params) |sp, dp| {
            // names + sorts resolve in their OWN schema's file scope: a token's
            // text (internTok) and sort (resolveSort) both index that file's source.
            const saved = self.swapCtx(src_ctx0);
            const sname = try self.internTok(sp.name);
            const src_sorts = try self.arena.alloc(SortId, sp.arg_sorts.len);
            for (sp.arg_sorts, src_sorts) |s, *o| o.* = try self.resolveSort(s);
            const result_sort = try self.resolveSort(sp.result);
            _ = self.swapCtx(dst_ctx0);
            const dname = try self.internTok(dp.name);
            const dst_sorts = try self.arena.alloc(SortId, dp.arg_sorts.len);
            for (dp.arg_sorts, dst_sorts) |s, *o| o.* = try self.resolveSort(s);
            _ = self.swapCtx(saved);
            const kind: term.AppKind = if (result_sort == .prop) .pred else .app;
            const opaque_sym = try self.env.addSym(self.file, .{
                .name = try self.freshNamed("model-schema-param"),
                .kind = kind,
                .arg_sorts = src_sorts,
                .result = result_sort,
                .result_refined = result_sort,
                .guard = null,
                .param_names = &.{},
                .loc = 0,
            });
            if (src_sorts.len == 0) {
                const t = try self.pool.addApp(kind, opaque_sym, &.{});
                src_args.put(self.arena, sname, .{ .value = .{ .id = t, .sort = result_sort } }) catch return error.OutOfMemory;
                dst_args.put(self.arena, dname, .{ .value = .{ .id = t, .sort = result_sort } }) catch return error.OutOfMemory;
            } else {
                src_args.put(self.arena, sname, try self.opaqueLambda(opaque_sym, kind, src_sorts, result_sort)) catch return error.OutOfMemory;
                dst_args.put(self.arena, dname, try self.opaqueLambda(opaque_sym, kind, dst_sorts, result_sort)) catch return error.OutOfMemory;
            }
        }

        const src_ctx: Ctx = .{ .source = src_schema.source, .file = src_schema.file, .diag = @intFromEnum(src_schema.file) };
        const dst_ctx: Ctx = .{ .source = dst_schema.source, .file = dst_schema.file, .diag = @intFromEnum(dst_schema.file) };
        // instantiate bodies only (skip re-checking either schema's own proof here —
        // that is done at each schema's declaration).
        const recheck = self.verify.recheck_schemas;
        self.verify.recheck_schemas = false;
        defer self.verify.recheck_schemas = recheck;
        const src_body = (try self.instantiateSchemaCore(src, src_schema, src_ctx, &src_args)) orelse
            return self.fail(loc, "could not instantiate source schema for the discharge check", .{});
        const dst_body = (try self.instantiateSchemaCore(dst, dst_schema, dst_ctx, &dst_args)) orelse
            return self.fail(loc, "could not instantiate the discharge schema", .{});
        const remapped = self.pool.remapFormula(src_body, remap) catch return error.OutOfMemory;
        if (!self.pool.alphaEq(remapped, dst_body)) {
            return self.fail(loc, "schema discharge '{s}' does not match the model's remap of '{s}':\n  expected (remapped source): {s}\n  discharge:                 {s}", .{
                self.interner.stringBytes(dst_schema.name), self.interner.stringBytes(src_schema.name),
                try self.renderTerm(remapped), try self.renderTerm(dst_body),
            });
        }
    }

    /// Build a `SchemaArg.lambda` `(fun x1…xn => opaque(x1…xn))` at the given arg
    /// sorts, reusing an existing opaque symbol. Binders are free fvars; the body
    /// applies `opaque` to them (substituted structurally at instantiation).
    fn opaqueLambda(self: *Elaborator, opaque_sym: term.SymId, kind: term.AppKind, arg_sorts: []const SortId, result_sort: SortId) ElabError!SchemaArg {
        const names = try self.arena.alloc(StrId, arg_sorts.len);
        const fvars = try self.arena.alloc(TermId, arg_sorts.len);
        for (arg_sorts, names, fvars) |asort, *n, *fv| {
            n.* = try self.freshName();
            fv.* = try self.pool.add(.{ .fvar = .{ .name = n.*, .sort = asort } });
        }
        const applied = try self.pool.addApp(kind, opaque_sym, fvars);
        return .{ .lambda = .{ .body = applied, .params = names, .arg_sorts = arg_sorts, .result_sort = result_sort } };
    }

    /// Strict-mode declaration check: instantiate a schema at fresh OPAQUE
    /// parameters and verify its proof body once, here. Each param `p: S1->…->Sn->R`
    /// becomes a fresh uninterpreted symbol `p#opaque` of that exact signature, so
    /// the body elaborates and kernel-checks exactly as at a real use site — but
    /// generically, catching malformed steps (e.g. a mis-arity `or_elim`) at the
    /// declaration rather than lying dormant until some caller instantiates it.
    fn checkSchemaBodyOpaque(self: *Elaborator, stmt_id: StatementId, params: []const ast.SchemaParam) ElabError!void {
        const schema = &self.env.statements.items[@intFromEnum(stmt_id)].schema;
        const schema_ctx: Ctx = .{ .source = schema.source, .file = schema.file, .diag = @intFromEnum(schema.file) };
        var args_map: SchemaArgs = .empty;
        for (params) |p| {
            const pname = try self.internTok(p.name);
            const arg_sorts = try self.arena.alloc(SortId, p.arg_sorts.len);
            for (p.arg_sorts, arg_sorts) |s, *out| out.* = try self.resolveSort(s);
            const result_sort = try self.resolveSort(p.result);
            const kind: term.AppKind = if (result_sort == .prop) .pred else .app;
            // a fresh uninterpreted symbol of the param's signature, BRANDED with
            // the original param name (`opaque-schema-param#<origName>#<n>`) so a
            // downstream error (e.g. arithmetic can't decide over it) can name the
            // user's parameter instead of leaking the raw internal symbol.
            const branded = std.fmt.allocPrint(self.arena, "opaque-schema-param#{s}", .{self.text(p.name)}) catch return error.OutOfMemory;
            const sym_name = try self.freshNamed(branded);
            const sym_id = try self.env.addSym(self.file, .{
                .name = sym_name,
                .kind = kind,
                .arg_sorts = arg_sorts,
                .result = result_sort,
                .result_refined = result_sort,
                .guard = null,
                .param_names = &.{},
                .loc = 0,
            });
            if (p.arg_sorts.len == 0) {
                // a nullary param (a value): the opaque constant itself.
                const t = try self.pool.addApp(kind, sym_id, &.{});
                args_map.put(self.arena, pname, .{ .value = .{ .id = t, .sort = result_sort } }) catch return error.OutOfMemory;
            } else {
                // an N-ary generator: `fun x1…xn => opaque(x1…xn)`, binders free.
                const names = try self.arena.alloc(StrId, arg_sorts.len);
                const fvars = try self.arena.alloc(TermId, arg_sorts.len);
                for (arg_sorts, names, fvars) |asort, *n, *fv| {
                    n.* = try self.freshName();
                    fv.* = try self.pool.add(.{ .fvar = .{ .name = n.*, .sort = asort } });
                }
                const applied = try self.pool.addApp(kind, sym_id, fvars);
                args_map.put(self.arena, pname, .{
                    .lambda = .{ .body = applied, .params = names, .arg_sorts = arg_sorts, .result_sort = result_sort },
                }) catch return error.OutOfMemory;
            }
        }
        // `instantiateSchemaCore` re-reads schema.* through the pointer; take a
        // fresh borrow (addSym above may have resized env.statements' backing).
        const sch = &self.env.statements.items[@intFromEnum(stmt_id)].schema;
        _ = self.instantiateSchemaCore(stmt_id, sch, schema_ctx, &args_map) catch |e| switch (e) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return, // diagnostic already recorded
        };
    }

    fn instantiateSchema(self: *Elaborator, stmt_id: StatementId, schema: *const Statement.Schema, c: ast.Step.Claim) ElabError!TermId {
        const name_tok = c.schema.?;
        // cycle detection: a schema that appears in its own instantiation
        // chain would re-check its proof forever. Report the chain by name.
        for (self.instantiating.items, 0..) |on_stack, i| {
            if (on_stack == stmt_id) {
                var msg: std.Io.Writer.Allocating = .init(self.arena);
                for (self.instantiating.items[i..]) |sid| {
                    const s = self.env.statements.items[@intFromEnum(sid)];
                    msg.writer.print("{s} -> ", .{self.interner.stringBytes(statementName(s))}) catch return error.OutOfMemory;
                }
                msg.writer.print("{s}", .{self.text(name_tok)}) catch return error.OutOfMemory;
                return self.fail(name_tok.start, "schema instantiation cycle: {s}", .{msg.written()});
            }
        }
        // a huge backstop purely to bound memory on a pathological (but
        // acyclic) blowup; far above any real proof
        if (self.instantiating.items.len >= 1024) {
            return self.fail(name_tok.start, "schema instantiation nested past 1024 (runaway?)", .{});
        }
        if (c.args.len != schema.params.len) {
            return self.fail(name_tok.start, "schema '{s}' expects {d} argument(s), got {d}", .{
                self.text(name_tok), schema.params.len, c.args.len,
            });
        }

        // the schema's SIGNATURE tokens (param names, param sorts) live in the
        // defining file; the ARGUMENT expressions live at the use site. Swap
        // contexts per operation.
        const schema_ctx: Ctx = .{
            .source = schema.source,
            .file = schema.file,
            .diag = @intFromEnum(schema.file),
        };
        var args_map: SchemaArgs = .empty;
        for (schema.params, c.args) |p, arg_expr| {
            const ctx = self.swapCtx(schema_ctx);
            const pname = try self.internTok(p.name);
            if (p.arg_sorts.len == 0) {
                const want = try self.resolveSort(p.result);
                _ = self.swapCtx(ctx);
                const t = try self.elaborateExpr(arg_expr);
                if (t.sort != want) {
                    return self.fail(exprLoc(arg_expr), "expected sort '{s}', got '{s}'", .{
                        self.sortName(want), self.sortName(t.sort),
                    });
                }
                args_map.put(self.arena, pname, .{ .value = t }) catch return error.OutOfMemory;
            } else {
                // an N-ary generator param `p: S1 -> … -> Sn -> R`.
                const arg_sorts = try self.arena.alloc(SortId, p.arg_sorts.len);
                for (p.arg_sorts, arg_sorts) |a, *out| out.* = try self.resolveSort(a);
                const result_sort = try self.resolveSort(p.result);
                const pname_text = self.text(p.name);
                _ = self.swapCtx(ctx);
                // eta-sugar: a bare predicate/function name `p` of the expected
                // `S1 -> … -> Sn -> R` signature stands for `fun x1…xn => p(x1…xn)`.
                // Synthesize that body directly and store the same `.lambda` shape.
                if (arg_expr.* == .name and
                    std.mem.indexOfScalar(u8, self.text(arg_expr.name), '.') == null)
                {
                    const nm = try self.internTok(arg_expr.name);
                    if (self.env.findSym(self.file, nm)) |sym_id| {
                        const sym = self.env.sym(sym_id);
                        const kind: term.AppKind = if (result_sort == .prop) .pred else .app;
                        if (sym.arg_sorts.len == arg_sorts.len and sym.result == result_sort and
                            std.mem.eql(SortId, sym.arg_sorts, arg_sorts))
                        {
                            const names = try self.arena.alloc(StrId, arg_sorts.len);
                            const fvars = try self.arena.alloc(TermId, arg_sorts.len);
                            for (arg_sorts, names, fvars) |asort, *n, *fv| {
                                n.* = try self.freshName();
                                fv.* = try self.pool.add(.{ .fvar = .{ .name = n.*, .sort = asort } });
                            }
                            const applied = try self.pool.addApp(kind, sym_id, fvars);
                            args_map.put(self.arena, pname, .{
                                .lambda = .{ .body = applied, .params = names, .arg_sorts = arg_sorts, .result_sort = result_sort },
                            }) catch return error.OutOfMemory;
                            continue;
                        }
                    }
                }
                if (arg_expr.* != .lambda) {
                    return self.fail(exprLoc(arg_expr), "schema parameter '{s}' requires a {d}-argument lambda (or a bare symbol of that signature)", .{ pname_text, arg_sorts.len });
                }
                const lam = arg_expr.lambda;
                if (lam.binders.len != arg_sorts.len) {
                    return self.fail(lam.tok.start, "schema parameter '{s}' expects a {d}-argument lambda, got {d}", .{ pname_text, arg_sorts.len, lam.binders.len });
                }
                // bind each lambda binder as a fresh eigenvariable (checking its
                // declared sort against the param signature); elaborate the body with
                // all N in scope, and KEEP the fvar names free in the stored body —
                // application substitutes them (no closing; see SchemaArg.lambda).
                const names = try self.arena.alloc(StrId, lam.binders.len);
                for (lam.binders, arg_sorts, names) |b, asort, *nm| {
                    const lam_sort = try self.resolveSort(b.sort);
                    if (lam_sort != asort) {
                        return self.fail(b.sort.start, "expected sort '{s}', got '{s}'", .{
                            self.sortName(asort), self.sortName(lam_sort),
                        });
                    }
                    const lam_name = try self.internTok(b.name);
                    try self.checkNoShadow(lam_name, b.name);
                    const fresh = try self.freshName();
                    nm.* = fresh;
                    try self.scope.append(self.arena, .{ .name = lam_name, .sort = asort, .fvar = fresh });
                }
                const body = try self.elaborateExpr(lam.body);
                for (0..lam.binders.len) |_| _ = self.scope.pop();
                if (body.sort != result_sort) {
                    if (result_sort == .prop) {
                        return self.fail(exprLoc(lam.body), "expected a proposition, got sort '{s}'", .{self.sortName(body.sort)});
                    }
                    return self.fail(exprLoc(lam.body), "expected sort '{s}', got '{s}'", .{
                        self.sortName(result_sort), self.sortName(body.sort),
                    });
                }
                args_map.put(self.arena, pname, .{
                    .lambda = .{ .body = body.id, .params = names, .arg_sorts = arg_sorts, .result_sort = result_sort },
                }) catch return error.OutOfMemory;
            }
        }

        return (try self.instantiateSchemaCore(stmt_id, schema, schema_ctx, &args_map)) orelse
            self.fail(name_tok.start, "instantiation of schema '{s}' failed here", .{self.text(name_tok)});
    }

    /// Monomorphize a schema's stored body/proof at a completed `args_map`
    /// (params -> value/lambda). Shared by the surface `instantiate` path
    /// (which builds args_map from written-down arguments) and synthesizing
    /// certifiers (which build a lambda arg directly from a TermId predicate —
    /// e.g. the Cooper-replay induction). Returns the monomorphized instance
    /// formula, or null on failure. The body/proof resolve in the schema's own
    /// defining file, hygienically masked from the use-site scope.
    pub fn instantiateSchemaCore(self: *Elaborator, stmt_id: StatementId, schema: *const Statement.Schema, schema_ctx: Ctx, args_map: *const SchemaArgs) ElabError!?TermId {
        const saved_scope = self.scope;
        const saved_args = self.schema_args;
        self.scope = .empty;
        self.schema_args = args_map;
        try self.instantiating.append(self.arena, stmt_id);
        defer {
            self.scope = saved_scope;
            self.schema_args = saved_args;
            _ = self.instantiating.pop();
        }

        const use_ctx = self.swapCtx(schema_ctx);
        const checked: ?TermId = blk: {
            const inst = self.requireProp(self.elaborateExpr(schema.body) catch |e| switch (e) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => break :blk null,
            }, schema.body) catch |e| switch (e) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => break :blk null,
            };
            // re-check the schema's proof at this instance (comptime-template
            // semantics). `--reckless` (recheck_schemas = false) trusts the
            // schema's stored proven-ness and skips the re-instantiation.
            if (self.verify.recheck_schemas) {
                if (schema.proof) |steps| {
                    if (try self.checkProofSteps(steps, inst.id, schema.loc) == null) break :blk null;
                }
            }
            break :blk inst.id;
        };
        _ = self.swapCtx(use_ctx);
        return checked;
    }

    fn wantRefs(self: *Elaborator, c: ast.Step.Claim, n: usize) ElabError!void {
        if (c.refs.len != n) {
            return self.fail(c.rule.start, "'{s}' expects {d} reference(s), got {d}", .{
                self.text(c.rule), n, c.refs.len,
            });
        }
    }

    // --- the `simplify` tactic: certificate emitter -------------------------
    // Synthesizes ordinary kernel steps (reflexivity / axiom or theorem
    // citation / forall_elim specialization / rewrite) into the current block
    // and returns the user's claim justification. Every step kernel-checked: no
    // accelerated step, the kernel checks everything.

    // --- universal-prefix peeling (shared by arithmetic / simplify_quantified)

    /// A goal's `forall` prefix, stripped to its body. `opened[i]` is the
    /// goal after opening the first `i` binders (opened[0] = the whole goal,
    /// opened[len] = body); `fix_vars` are the fresh eigenvariables, one per
    /// peeled binder, outermost-first.
    pub const Universal = struct {
        opened: []const TermId,
        fix_vars: []const term.Node.Fvar,
        body: TermId,
    };

    /// Strip the outer `forall` binders of `goal`, opening each as a fresh
    /// eigenvariable named `prefix`.
    pub fn peelUniversal(self: *Elaborator, goal: TermId, prefix: []const u8) ElabError!Universal {
        var opened: std.ArrayList(TermId) = .empty;
        var fix_vars: std.ArrayList(term.Node.Fvar) = .empty;
        var g = goal;
        try opened.append(self.arena, g);
        while (true) {
            const node = self.pool.get(g);
            if (node != .quant or node.quant.q != .forall) break;
            // name the eigenvariable after the binder's own hint when it has one
            // (so diagnostics read `n`, not the synthetic `<prefix>`); the `#N`
            // suffix `freshNamed` adds keeps it unique and is stripped on display.
            const hint = self.interner.stringBytes(node.quant.hint);
            const name_prefix = if (hint.len > 0) hint else prefix;
            const fv: term.Node.Fvar = .{ .name = try self.freshNamed(name_prefix), .sort = node.quant.sort };
            const fv_id = try self.pool.add(.{ .fvar = fv });
            g = try self.pool.open(node.quant.body, fv_id);
            try fix_vars.append(self.arena, fv);
            try opened.append(self.arena, g);
        }
        return .{ .opened = opened.items, .fix_vars = fix_vars.items, .body = g };
    }

    /// Like `peelUniversal`, but strips AT MOST `max` binders — the rest stay in
    /// `body`. Used when the closure prefix (caller eigenvariables) must be
    /// peeled but the goal's OWN leading binders must be left intact for the
    /// body-emit to handle. `max` greater than the available binders peels all.
    pub fn peelUniversalN(self: *Elaborator, goal: TermId, prefix: []const u8, max: usize) ElabError!Universal {
        var opened: std.ArrayList(TermId) = .empty;
        var fix_vars: std.ArrayList(term.Node.Fvar) = .empty;
        var g = goal;
        try opened.append(self.arena, g);
        while (fix_vars.items.len < max) {
            const node = self.pool.get(g);
            if (node != .quant or node.quant.q != .forall) break;
            const hint = self.interner.stringBytes(node.quant.hint);
            const name_prefix = if (hint.len > 0) hint else prefix;
            const fv: term.Node.Fvar = .{ .name = try self.freshNamed(name_prefix), .sort = node.quant.sort };
            const fv_id = try self.pool.add(.{ .fvar = fv });
            g = try self.pool.open(node.quant.body, fv_id);
            try fix_vars.append(self.arena, fv);
            try opened.append(self.arena, g);
        }
        return .{ .opened = opened.items, .fix_vars = fix_vars.items, .body = g };
    }

    /// Open one synthesized `fix` block per peeled binder; returns the block
    /// ids (outermost-first) and the innermost block, which is where the body
    /// justification should be emitted. Pair with `closeUniversal`.
    pub fn openUniversal(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, u: Universal) ElabError!struct { blocks: []const kernel.BlockId, innermost: kernel.BlockId } {
        var blocks: std.ArrayList(kernel.BlockId) = .empty;
        var parent = block_id;
        for (u.fix_vars) |fv| {
            const b = try self.newBlock(low, try self.freshNamed("forall"), parent, .{ .fix = .{ .v = fv } });
            try blocks.append(self.arena, b);
            parent = b;
        }
        return .{ .blocks = blocks.items, .innermost = parent };
    }

    /// Emit the body claim in the innermost block, then close each fix block
    /// with `forall_intro`, returning the outermost justification. When there
    /// are no binders, `body_just` is returned unchanged (nothing to close).
    pub fn closeUniversal(self: *Elaborator, low: *Lowering, loc: u32, u: Universal, blocks: []const kernel.BlockId, body_just: kernel.Justification) ElabError!kernel.Justification {
        if (blocks.len == 0) return body_just;
        _ = try self.emitStep(low, blocks[blocks.len - 1], loc, u.body, body_just);
        var i = blocks.len;
        while (i > 1) {
            i -= 1;
            self.closeBlock(low, blocks[i]);
            _ = try self.emitStep(low, blocks[i - 1], loc, u.opened[i], .{ .forall_intro = .{ .id = blocks[i], .loc = loc } });
        }
        self.closeBlock(low, blocks[0]);
        return .{ .forall_intro = .{ .id = blocks[0], .loc = loc } };
    }

    /// Append a synthesized step to the proof; returns a reference to it.
    pub fn emitStep(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, formula: TermId, just: kernel.Justification) ElabError!kernel.SRef {
        const id: kernel.StepId = @enumFromInt(low.steps.items.len);
        try low.steps.append(self.arena, .{
            .formula = formula,
            .just = just,
            .block = block_id,
            .label = try self.freshNamed("simplify"),
            .loc = loc,
        });
        return .{ .id = id, .loc = loc };
    }

    /// Emit the citation + forall_elim chain specializing `rule` at
    /// `bindings`; returns the step proving `inst_lhs = inst_rhs`.
    pub fn emitInstance(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, rule: simplify_mod.Rule, bindings: []const TermId) ElabError!kernel.SRef {
        var cur_ref: kernel.SRef = undefined;
        var cur_formula: TermId = rule.formula;
        switch (rule.source) {
            .axiom => |a| cur_ref = try self.emitStep(low, block_id, loc, rule.formula, .{ .axiom_ref = .{ .stmt = a.id, .loc = loc } }),
            .theorem => |t| cur_ref = try self.emitStep(low, block_id, loc, rule.formula, .{ .theorem_ref = .{ .stmt = t.id, .loc = loc } }),
            .step => |sref| cur_ref = sref, // already in the proof
        }
        for (bindings) |val| {
            const q = self.pool.get(cur_formula).quant;
            const opened = try self.pool.open(q.body, val);
            cur_ref = try self.emitStep(low, block_id, loc, opened, .{ .forall_elim = .{ .step = cur_ref, .with = val, .with_loc = loc } });
            cur_formula = opened;
        }
        return cur_ref;
    }

    /// Emit `eq(start, start)` then one rewrite step per trace entry;
    /// returns the step proving `eq(start, <after last entry>)`.
    /// `trace` must be non-empty.
    pub fn emitSideChain(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, rules: []const simplify_mod.Rule, start: TermId, trace: []const simplify_mod.Rewrite) ElabError!kernel.SRef {
        const refl = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = start } });
        var prev = try self.emitStep(low, block_id, loc, refl, .reflexivity);
        for (trace) |rw| {
            const inst = try self.emitInstance(low, block_id, loc, rules[rw.rule_idx], rw.bindings);
            const next = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = rw.after } });
            prev = try self.emitStep(low, block_id, loc, next, .{ .rewrite = .{ .equation = inst, .target = prev } });
        }
        return prev;
    }

    /// The simplify core on a bare equation goal `eq_goal` in `emit_block`:
    /// resolve cited refs into rules, normalize both sides, emit the join.
    pub fn simplifyEquation(self: *Elaborator, low: *Lowering, emit_block: kernel.BlockId, loc: u32, refs: []const lexer.Token, eq_goal: TermId) ElabError!kernel.Justification {
        const goal_node = self.pool.get(eq_goal);
        std.debug.assert(goal_node == .eq);

        // prepare rules from the cited facts (step labels first, then statements)
        var rules: std.ArrayList(simplify_mod.Rule) = .empty;
        for (refs) |ref| {
            const name = try self.internTok(ref);
            var formula: TermId = undefined;
            var source: simplify_mod.Source = undefined;
            if (low.labels.get(name)) |target| switch (target) {
                .step => |sid| {
                    const s = low.steps.items[@intFromEnum(sid)];
                    if (!lowAncestorOrSelf(low, s.block, emit_block)) {
                        return self.fail(ref.start, "'{s}' is not accessible from this step (closed subproof)", .{self.text(ref)});
                    }
                    formula = s.formula;
                    source = .{ .step = .{ .id = sid, .loc = ref.start } };
                },
                .block => return self.fail(ref.start, "'{s}' names a subproof; simplify takes equations", .{self.text(ref)}),
            } else {
                const stmt_id = try self.resolveStatementRef(ref);
                const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
                switch (stmt) {
                    .axiom => |a| {
                        if (a.is_hole) try self.inheritHoles(a.holes);
                        formula = a.formula;
                        source = .{ .axiom = .{ .id = stmt_id, .loc = ref.start } };
                    },
                    .theorem => |t| {
                        if (!t.proven) return self.fail(ref.start, "cites unproven theorem '{s}'", .{self.text(ref)});
                        try self.inheritAccelerated(t.accelerated);
                        try self.inheritHoles(t.holes);
                        formula = t.formula;
                        source = .{ .theorem = .{ .id = stmt_id, .loc = ref.start } };
                    },
                    .schema => return self.fail(ref.start, "'{s}' is a schema; simplify takes equations", .{self.text(ref)}),
                }
            }
            switch (try self.equationRule(formula, source)) {
                .rule => |r| try rules.append(self.arena, r),
                .not_equation => return self.fail(ref.start, "'{s}' is not an equation", .{self.text(ref)}),
                .binder_missing => return self.fail(ref.start, "'{s}': not every bound variable occurs on the left-hand side", .{self.text(ref)}),
            }
        }

        const s = goal_node.eq.lhs;
        const t = goal_node.eq.rhs;
        if (self.pool.alphaEq(s, t)) return .reflexivity;

        const rs = simplify_mod.normalize(self.arena, self.pool, self.env, rules.items, s, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "simplify: rewrite limit reached (looping rule set?)", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        const rt = simplify_mod.normalize(self.arena, self.pool, self.env, rules.items, t, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "simplify: rewrite limit reached (looping rule set?)", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        if (!self.pool.alphaEq(rs.nf, rt.nf)) {
            return self.fail(loc, "simplify: normal forms differ: '{s}' vs '{s}'", .{
                try self.renderTerm(rs.nf), try self.renderTerm(rt.nf),
            });
        }
        return self.emitJoin(low, emit_block, loc, rules.items, s, t, rs, rt);
    }

    // --- the `ac` tactic: associative-commutative reordering (emits kernel steps) ---
    // Proves s = t when both are sums (over `add`) with the same multiset of
    // opaque atoms, differing only by associativity/commutativity. Each side
    // is re-associated to a right-nested comb (via addIsAssociative as a
    // terminating rewrite), its atoms flattened and bubble-sorted into a
    // canonical order (via addLeftSwap/addIsCommutative, one fabricated
    // rewrite per transposition — the sortTrace machinery), then the two
    // canonical forms are joined. All kernel-checked; no accelerated step.

    /// Flatten an `add`-tree into its atom summands (any maximal subterm that
    /// is not itself an `add(_, _)`), left-to-right.
    pub fn flattenSum(self: *Elaborator, add_sym: term.SymId, t: TermId, out: *std.ArrayList(TermId)) ElabError!void {
        const node = self.pool.get(t);
        if (node == .app and symIs(node.app.sym, add_sym) and node.app.args_len == 2) {
            // copy arg ids before recursing: pool.args aliases pool.extra, so a
            // walk that grows the pool would dangle the slice (see polyMonomials).
            const args = self.pool.args(node.app);
            const a0 = args[0];
            const a1 = args[1];
            try self.flattenSum(add_sym, a0, out);
            try self.flattenSum(add_sym, a1, out);
            return;
        }
        try out.append(self.arena, t);
    }

    // -- the `polynomial` tactic (nonlinear identities, emits kernel steps) ---------
    //
    // Proves `s = t` when both are polynomials over add/mul with the same
    // expansion. The nonlinear analogue of `ac`: canonicalize each side to a
    // sorted sum of sorted monomials, then join. Elaborated — emits a
    // ring-rewrite certificate (no accelerated step). Reuses the ac machinery: `normalize` for the
    // terminating distribute/fold passes, `acPlan` for the two sorts.

    /// Resolve the optional `(theory)` argument, scoping `theory_file` for the
    /// duration of the caller (via the returned saved value + defer at the call
    /// site). `polynomial(<module>)` resolves the ring vocabulary + lemmas
    /// against that module's scope; bare `polynomial` resolves locally.
    pub fn enterTheory(self: *Elaborator, c: ast.Step.Claim) ElabError!void {
        if (c.schema) |theory_tok| {
            const ns = try self.internTok(theory_tok);
            self.theory_file = self.env.findNamespace(self.file, ns) orelse
                return self.fail(theory_tok.start, "unknown theory '{s}' (not an imported module)", .{self.text(theory_tok)});
        }
    }

    /// Lift a sub-term trace into whole-term context: each entry rewrites a
    /// SUBTERM (a single monomial in the sum), but `emitSideChain` states each
    /// intermediate as an equation over the WHOLE term. The kernel rewrite is
    /// by instance (`inst_lhs`→`inst_rhs`), which is context-free, so only the
    /// recorded `before`/`after` whole-terms need rebuilding: substitute the
    /// evolving subterm back into the sum at position `i`. `others` holds every
    /// monomial except `i` (already in final form for indices < i, original for
    /// indices > i); `ctx(sub)` = the sum with slot `i` = `sub`.
    pub fn liftMonoTrace(
        self: *Elaborator,
        add_symbols: presburger_mod.Symbols,
        before: []const TermId,
        after: []const TermId,
        sub_trace: []const simplify_mod.Rewrite,
        out: *std.ArrayList(simplify_mod.Rewrite),
    ) ElabError!bool {
        // scratch slot list = before ++ [hole] ++ after; the hole is filled per
        // entry to rebuild the whole-term before/after.
        var slots: std.ArrayList(TermId) = .empty;
        try slots.appendSlice(self.arena, before);
        const hole = slots.items.len;
        try slots.append(self.arena, sub_trace[0].before); // placeholder, overwritten per entry
        try slots.appendSlice(self.arena, after);
        for (sub_trace) |rw| {
            slots.items[hole] = rw.before;
            const w_before = (try self.buildComb(add_symbols, slots.items)) orelse return false;
            slots.items[hole] = rw.after;
            const w_after = (try self.buildComb(add_symbols, slots.items)) orelse return false;
            try out.append(self.arena, .{
                .before = w_before,
                .after = w_after,
                .rule_idx = rw.rule_idx,
                .bindings = rw.bindings,
                .inst_lhs = rw.inst_lhs,
                .inst_rhs = rw.inst_rhs,
            });
        }
        return true;
    }

    /// In-place insertion sort by termOrder (stable, small lists).
    pub fn sortTerms(self: *Elaborator, items: []TermId) void {
        var i: usize = 1;
        while (i < items.len) : (i += 1) {
            const v = items[i];
            var j = i;
            while (j > 0 and self.pool.termOrder(items[j - 1], v) == .gt) : (j -= 1) {
                items[j] = items[j - 1];
            }
            items[j] = v;
        }
    }

    pub fn buildRightNested(self: *Elaborator, sym: term.SymId, leaves: []const TermId) ElabError!TermId {
        var cur = leaves[leaves.len - 1];
        var i = leaves.len - 1;
        while (i > 0) {
            i -= 1;
            cur = try self.pool.addApp(.app, sym, &.{ leaves[i], cur });
        }
        return cur;
    }

    const AcPlan = struct { sorted: TermId, trace: []const simplify_mod.Rewrite };

    /// Re-associate `start` to a right-nested comb, then bubble-sort its
    /// atoms into canonical (termOrder) order, accumulating one trace.
    pub fn acPlan(self: *Elaborator, symbols: presburger_mod.Symbols, rules: []const simplify_mod.Rule, assoc_idx: usize, comm_idx: usize, swap_idx: usize, add_sym: term.SymId, start: TermId) ElabError!?AcPlan {
        // phase 1: right-nest via associativity only (terminating)
        const assoc_only = rules[assoc_idx .. assoc_idx + 1];
        const rn = simplify_mod.normalize(self.arena, self.pool, self.env, assoc_only, start, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        // phase 2: flatten the right-nested comb and bubble-sort
        var leaves: std.ArrayList(TermId) = .empty;
        try self.flattenSum(add_sym, rn.nf, &leaves);
        var trace: std.ArrayList(simplify_mod.Rewrite) = .empty;
        // phase-1 normalized over the single-rule slice `rules[assoc_idx..]`, so
        // its trace rule_idx is 0-relative; rebase it to the full-array index.
        for (rn.trace) |rw| {
            var r = rw;
            r.rule_idx = rw.rule_idx + assoc_idx;
            try trace.append(self.arena, r);
        }
        const sorted = (try self.sortTrace(symbols, rules, comm_idx, swap_idx, .{ .offset = 0, .leaves = leaves.items }, &trace)) orelse return null;
        return .{ .sorted = sorted, .trace = trace.items };
    }

    /// Resolve an `assoc_commut(assoc, comm, swap)` argument — a bare name
    /// expression — into a rewrite rule (reusing resolveRewriteRule's step /
    /// statement resolution + accelerated-tactic inheritance).
    pub fn acArgRule(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, arg: *const ast.Expr) ElabError!simplify_mod.Rule {
        if (arg.* != .name) {
            return self.fail(exprLoc(arg), "assoc_commut argument must name an equation lemma", .{});
        }
        return self.resolveRewriteRule(low, block_id, arg.name, "assoc_commut");
    }

    /// Resolve one cited ref (step label or statement) into an L→R rewrite
    /// rule, with the same accessibility/acceleration checks as simplify. `who` names
    /// the citing tactic for error messages.
    pub fn resolveRewriteRule(self: *Elaborator, low: *Lowering, emit_block: kernel.BlockId, ref: lexer.Token, comptime who: []const u8) ElabError!simplify_mod.Rule {
        const name = try self.internTok(ref);
        var formula: TermId = undefined;
        var source: simplify_mod.Source = undefined;
        if (low.labels.get(name)) |target| switch (target) {
            .step => |sid| {
                const s = low.steps.items[@intFromEnum(sid)];
                if (!lowAncestorOrSelf(low, s.block, emit_block)) {
                    return self.fail(ref.start, "'{s}' is not accessible from this step (closed subproof)", .{self.text(ref)});
                }
                formula = s.formula;
                source = .{ .step = .{ .id = sid, .loc = ref.start } };
            },
            .block => return self.fail(ref.start, "'{s}' names a subproof; " ++ who ++ " takes equation lemmas", .{self.text(ref)}),
        } else {
            const stmt_id = try self.resolveStatementRef(ref);
            switch (self.env.statements.items[@intFromEnum(stmt_id)]) {
                .axiom => |a| {
                    if (a.is_hole) try self.inheritHoles(a.holes);
                    formula = a.formula;
                    source = .{ .axiom = .{ .id = stmt_id, .loc = ref.start } };
                },
                .theorem => |t| {
                    if (!t.proven) return self.fail(ref.start, "cites unproven theorem '{s}'", .{self.text(ref)});
                    try self.inheritAccelerated(t.accelerated);
                    try self.inheritHoles(t.holes);
                    formula = t.formula;
                    source = .{ .theorem = .{ .id = stmt_id, .loc = ref.start } };
                },
                .schema => return self.fail(ref.start, "'{s}' is a schema; " ++ who ++ " takes equation lemmas", .{self.text(ref)}),
            }
        }
        return switch (try self.equationRule(formula, source)) {
            .rule => |r| r,
            .not_equation => self.fail(ref.start, "'{s}' is not an equation", .{self.text(ref)}),
            .binder_missing => self.fail(ref.start, "'{s}': not every bound variable occurs on the left-hand side", .{self.text(ref)}),
        };
    }

    pub const RulePrep = union(enum) { rule: simplify_mod.Rule, not_equation, binder_missing };

    /// Strip a fact's forall prefix (binders become pattern fvars) into a
    /// left-to-right rewrite rule.
    pub fn equationRule(self: *Elaborator, formula: TermId, source: simplify_mod.Source) ElabError!RulePrep {
        var binders: std.ArrayList(simplify_mod.Binder) = .empty;
        var body = formula;
        while (true) {
            const node = self.pool.get(body);
            if (node != .quant or node.quant.q != .forall) break;
            const fresh = try self.freshNamed("p");
            const fv = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
            body = try self.pool.open(node.quant.body, fv);
            try binders.append(self.arena, .{ .fvar = fresh, .sort = node.quant.sort });
        }
        const body_node = self.pool.get(body);
        if (body_node != .eq) return .not_equation;
        for (binders.items) |b| {
            if (!self.pool.occursFree(body_node.eq.lhs, b.fvar)) return .binder_missing;
        }
        return .{ .rule = .{
            .source = source,
            .binders = binders.items,
            .lhs = body_node.eq.lhs,
            .rhs = body_node.eq.rhs,
            .formula = formula,
        } };
    }

    /// Emit the certificate chains joining a successful two-sided
    /// normalization; returns the user's closing justification.
    pub fn emitJoin(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, rules: []const simplify_mod.Rule, s: TermId, t: TermId, rs: simplify_mod.Result, rt: simplify_mod.Result) ElabError!kernel.Justification {
        if (rt.trace.len == 0) {
            // t is already the shared normal form: the last rewrite of the
            // s-chain becomes the user's own justification
            std.debug.assert(rs.trace.len > 0); // alphaEq handled above
            const head = rs.trace[0 .. rs.trace.len - 1];
            const last = rs.trace[rs.trace.len - 1];
            const target: kernel.SRef = if (head.len > 0)
                try self.emitSideChain(low, block_id, loc, rules, s, head)
            else blk: {
                const refl = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = s } });
                break :blk try self.emitStep(low, block_id, loc, refl, .reflexivity);
            };
            const inst = try self.emitInstance(low, block_id, loc, rules[last.rule_idx], last.bindings);
            return .{ .rewrite = .{ .equation = inst, .target = target } };
        }
        // t moves: build t = NF, flip it to NF = t, and rewrite the s-side
        const t_end = try self.emitSideChain(low, block_id, loc, rules, t, rt.trace);
        const t_refl = try self.pool.add(.{ .eq = .{ .lhs = t, .rhs = t } });
        const t_refl_ref = try self.emitStep(low, block_id, loc, t_refl, .reflexivity);
        const t_sym_formula = try self.pool.add(.{ .eq = .{ .lhs = rt.nf, .rhs = t } });
        const t_sym = try self.emitStep(low, block_id, loc, t_sym_formula, .{ .rewrite = .{ .equation = t_end, .target = t_refl_ref } });
        const s_end: kernel.SRef = if (rs.trace.len > 0)
            try self.emitSideChain(low, block_id, loc, rules, s, rs.trace)
        else blk: {
            const refl = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = s } });
            break :blk try self.emitStep(low, block_id, loc, refl, .reflexivity);
        };
        return .{ .rewrite = .{ .equation = t_sym, .target = s_end } };
    }

    pub fn renderTerm(self: *Elaborator, id: TermId) ElabError![]const u8 {
        return @import("print.zig").render(self.arena, self.pool, self.env, self.interner, id) catch return error.OutOfMemory;
    }

    // --- C2: arithmetic certificates ----------------------------------------
    // Certificate stages for the `arithmetic` rule, all
    // kernel-checked. C2a: ground equations replay as simplify chains over
    // the well-known peano recursion axioms. C2b: universally-quantified
    // linear equations normalize to succ-towers over sorted sums (the
    // residual permutation is a chain of addIsCommutative/addLeftSwap
    // rewrites), and simple order goals a < b synthesize the witness
    // difference d, certify add(a, succ(d)) = b, and close with a
    // lessThanIntro instance. Anything outside — hypotheses, missing
    // lemmas, unjoinable forms — returns null and falls back to the accelerated path.

    pub const wk_term_rule_names = [_][]const u8{
        "addZeroLeft",   "addZeroRight",     "addSuccLeft", "addSuccRight",
        "mulZeroLeft",   "mulZeroRight",     "mulSuccLeft", "mulSuccRight",
        "oneIsSuccZero", "addIsAssociative",
        // ℤ elimination rules — absent (wellKnownRule → null) for ℕ theories,
        // which have no total sub/neg/prev. They rewrite sub/neg/prev away toward
        // an add-of-atoms normal form so the certifier can join ℤ linear goals.
        "definitionOfSubtraction", "negNeg",   "negAdd",
        "addNegRight",             "addNegLeft",
        "prevSucc",                "succPrev",
        // numeral-summand lifting: a `neg(succ^n(ZERO))` summand reduces (negSucc/
        // negZero) to a `prev`-tower, which addPrevLeft/Right float up to the tower
        // prefix — so `add(ONE, sub(b, ONE))` normalizes to succ/prev over {b} and
        // parseTower's signed offset matches the physical term. negPrev handles the
        // `neg(prev ...)` direction symmetrically.
        "negSucc",                 "negZero",  "negPrev",
        "addPrevLeft",             "addPrevRight",
    };

    const EqCert = struct {
        rules: []const simplify_mod.Rule,
        s: TermId,
        t: TermId,
        rs: simplify_mod.Result,
        rt: simplify_mod.Result,
    };

    const LtCert = struct {
        eq: EqCert,
        /// add(s, succ(d)) = t — the witness equation
        eq_formula: TermId,
        intro: simplify_mod.Rule,
        intro_args: []const TermId,
    };

    const ExistsCert = struct {
        witness: TermId,
        /// the body opened at the witness
        instance: TermId,
        inner: InnerPlan,
    };

    pub const InnerPlan = union(enum) { refl, eq: EqCert, lt: LtCert };

    pub const BodyPlan = union(enum) { inner: InnerPlan, exists: ExistsCert };

    /// Plan an unquantified certificate body: an equation or a less_than.
    pub fn planInner(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        term_rule_count: usize,
        comm_idx: ?usize,
        swap_idx: ?usize,
        body: TermId,
        loc: u32,
    ) ElabError!?InnerPlan {
        const node = self.pool.get(body);
        if (node == .eq) {
            if (self.pool.alphaEq(node.eq.lhs, node.eq.rhs)) return .refl;
            const eq = (try self.planEquation(symbols, rules, term_rule_count, comm_idx, swap_idx, node.eq.lhs, node.eq.rhs, loc)) orelse return null;
            return .{ .eq = eq };
        }
        if (node == .pred and symIs(node.pred.sym, symbols.less_than) and node.pred.args_len == 2) {
            const lt = (try self.planLess(symbols, rules, term_rule_count, comm_idx, swap_idx, body, loc)) orelse return null;
            return .{ .lt = lt };
        }
        return null;
    }

    pub fn emitInner(self: *Elaborator, low: *Lowering, block: kernel.BlockId, loc: u32, inner: InnerPlan) ElabError!kernel.Justification {
        return switch (inner) {
            .refl => .reflexivity,
            .eq => |eq| try self.emitJoin(low, block, loc, eq.rules, eq.s, eq.t, eq.rs, eq.rt),
            .lt => |lt| try self.emitLess(low, block, loc, lt),
        };
    }

    pub fn symIs(id: term.SymId, want: ?term.SymId) bool {
        return want != null and id == want.?;
    }

    /// Resolve a well-known fact by name in this file's scope; unproven and
    /// accelerated facts are unusable (they would poison the certificate).
    /// The scope arithmetic well-known names resolve in: the named theory
    /// module if `arithmetic(<mod>)` set one, else local scope.
    pub fn theoryScope(self: *const Elaborator) FileId {
        return self.theory_file orelse self.file;
    }

    pub fn wellKnownFact(self: *Elaborator, name_text: []const u8, loc: u32) ElabError!?struct { formula: TermId, source: simplify_mod.Source } {
        const name = self.interner.internString(name_text) catch return error.OutOfMemory;
        const stmt_id = self.env.findStatementId(self.theoryScope(), name) orelse return null;
        const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
        switch (stmt) {
            .axiom => |a| return .{ .formula = a.formula, .source = .{ .axiom = .{ .id = stmt_id, .loc = loc } } },
            .theorem => |t| return .{ .formula = t.formula, .source = .{ .theorem = .{ .id = stmt_id, .loc = loc } } },
            .schema => return null,
        }
    }

    pub fn wellKnownRule(self: *Elaborator, name_text: []const u8, loc: u32) ElabError!?simplify_mod.Rule {
        const fact = (try self.wellKnownFact(name_text, loc)) orelse return null;
        return switch (try self.equationRule(fact.formula, fact.source)) {
            .rule => |r| r,
            else => null,
        };
    }

    /// Strip a fact's forall prefix into a pseudo-rule whose lhs/rhs are
    /// both the whole stripped body (for non-equational facts that are
    /// instantiated via matchRule + emitInstance).
    pub fn strippedRule(self: *Elaborator, formula: TermId, source: simplify_mod.Source) ElabError!simplify_mod.Rule {
        var binders: std.ArrayList(simplify_mod.Binder) = .empty;
        var body = formula;
        while (true) {
            const node = self.pool.get(body);
            if (node != .quant or node.quant.q != .forall) break;
            const fresh = try self.freshNamed("p");
            const fv = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
            body = try self.pool.open(node.quant.body, fv);
            try binders.append(self.arena, .{ .fvar = fresh, .sort = node.quant.sort });
        }
        return .{ .source = source, .binders = binders.items, .lhs = body, .rhs = body, .formula = formula };
    }

    const Tower = struct { offset: i128, leaves: []const TermId };

    /// If `t` is a NUMERAL — `succ^n(ZERO)` (→ +n), `prev^n(ZERO)` (→ −n), or a
    /// `neg(...)` of one (sign flipped) — return its signed value; else null. This
    /// is how a bare constant like `ONE` = succ(ZERO) sitting as a summand folds
    /// into the tower's constant offset instead of riding as an (uncancellable)
    /// leaf. `ZERO` itself is 0.
    fn numeralValue(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId) ?i128 {
        var cur = t;
        var sign: i128 = 1;
        // peel any number of leading neg(...) (each flips the sign).
        while (true) {
            const node = self.pool.get(cur);
            if (node == .app and symIs(node.app.sym, symbols.neg) and node.app.args_len == 1) {
                sign = -sign;
                cur = self.pool.args(node.app)[0];
                continue;
            }
            break;
        }
        var mag: i128 = 0;
        while (true) {
            const node = self.pool.get(cur);
            if (node == .app and symIs(node.app.sym, symbols.succ) and node.app.args_len == 1) {
                mag += 1;
                cur = self.pool.args(node.app)[0];
                continue;
            }
            if (node == .app and symIs(node.app.sym, symbols.prev) and node.app.args_len == 1) {
                mag -= 1;
                cur = self.pool.args(node.app)[0];
                continue;
            }
            break;
        }
        const node = self.pool.get(cur);
        if (node == .app and symIs(node.app.sym, symbols.zero) and node.app.args_len == 0)
            return sign * mag;
        return null;
    }

    /// Parse succ^j(prev^k(right-nested sum of leaves)) with numeral summands
    /// folded into a signed constant offset; anything else is outside the
    /// certificate fragment. The offset accumulates the leading succ/prev prefix
    /// PLUS every numeral summand (succ^n(ZERO), prev^n(ZERO), or neg of one).
    fn parseTower(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId) ElabError!?Tower {
        var offset: i128 = 0;
        var cur = t;
        while (true) {
            const node = self.pool.get(cur);
            if (node == .app and symIs(node.app.sym, symbols.succ) and node.app.args_len == 1) {
                offset += 1;
                cur = self.pool.args(node.app)[0];
                continue;
            }
            if (node == .app and symIs(node.app.sym, symbols.prev) and node.app.args_len == 1) {
                offset -= 1;
                cur = self.pool.args(node.app)[0];
                continue;
            }
            break;
        }
        var leaves: std.ArrayList(TermId) = .empty;
        while (true) {
            const node = self.pool.get(cur);
            // a numeral summand (incl. a bare ZERO tail) folds into the offset.
            if (self.numeralValue(symbols, cur)) |v| {
                offset += v;
                break;
            }
            if (self.isTowerLeaf(symbols, cur)) {
                try leaves.append(self.arena, cur);
                break;
            }
            if (node != .app) return null;
            if (symIs(node.app.sym, symbols.add) and node.app.args_len == 2) {
                const args = self.pool.args(node.app);
                if (self.numeralValue(symbols, args[0])) |v| {
                    offset += v; // numeral summand: fold, don't emit a leaf
                    cur = args[1];
                    continue;
                }
                if (!self.isTowerLeaf(symbols, args[0])) return null; // not right-nested
                try leaves.append(self.arena, args[0]);
                cur = args[1];
                continue;
            }
            return null;
        }
        return .{ .offset = offset, .leaves = leaves.items };
    }

    /// A tower summand leaf is a free variable, an OPAQUE atom (a foreign
    /// application the arithmetic normalizer can't reduce — f(x), mod(a,b), or a
    /// surviving nonlinear mul(x,y)), or the negation `neg(<leaf>)` of either (so
    /// additive-inverse pairs x + neg(x) can meet and cancel).
    fn isTowerLeaf(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId) bool {
        const node = self.pool.get(t);
        if (node == .fvar) return true;
        if (node == .app and symIs(node.app.sym, symbols.neg) and node.app.args_len == 1) {
            return self.isTowerLeaf(symbols, self.pool.args(node.app)[0]);
        }
        return self.isOpaqueAtom(symbols, t);
    }

    /// An opaque atom at a summand position: an application whose head is NOT
    /// part of the sum structure the certifier walks (add / succ / prev / neg /
    /// sub / ZERO / ONE). A surviving nonlinear `mul(x, y)` counts, as does any
    /// foreign function app (f(x), mod(a,b)) — it rides through the sorted-tower
    /// join as one leaf.
    fn isOpaqueAtom(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId) bool {
        const node = self.pool.get(t);
        if (node != .app) return false;
        const sym = node.app.sym;
        return !(symIs(sym, symbols.add) or symIs(sym, symbols.succ) or
            symIs(sym, symbols.prev) or symIs(sym, symbols.neg) or
            symIs(sym, symbols.sub) or symIs(sym, symbols.zero) or
            symIs(sym, symbols.one));
    }

    pub fn buildComb(self: *Elaborator, symbols: presburger_mod.Symbols, leaves: []const TermId) ElabError!?TermId {
        if (leaves.len == 0) {
            const zero = symbols.zero orelse return null;
            return try self.pool.addApp(.app, zero, &.{});
        }
        var cur = leaves[leaves.len - 1];
        var i = leaves.len - 1;
        while (i > 0) {
            i -= 1;
            const add_sym = symbols.add orelse return null;
            cur = try self.pool.addApp(.app, add_sym, &.{ leaves[i], cur });
        }
        return cur;
    }

    pub fn buildTower(self: *Elaborator, symbols: presburger_mod.Symbols, succs: usize, comb: TermId) ElabError!?TermId {
        var cur = comb;
        for (0..succs) |_| {
            const succ_sym = symbols.succ orelse return null;
            cur = try self.pool.addApp(.app, succ_sym, &.{cur});
        }
        return cur;
    }

    /// A SIGNED tower: succ^n(comb) for n ≥ 0, prev^|n|(comb) for n < 0. The
    /// negative direction needs the ℤ `prev` symbol (absent for ℕ, where a
    /// negative offset is genuinely unbuildable → null). The certifier's
    /// normalizer collapses succ/prev via succPrev/prevSucc.
    pub fn buildTowerSigned(self: *Elaborator, symbols: presburger_mod.Symbols, offset: i128, comb: TermId) ElabError!?TermId {
        if (offset >= 0) return self.buildTower(symbols, @intCast(offset), comb);
        const prev_sym = symbols.prev orelse return null;
        var cur = comb;
        var n = -offset;
        while (n > 0) : (n -= 1) cur = try self.pool.addApp(.app, prev_sym, &.{cur});
        return cur;
    }

    /// Bubble-sort a tower's summands, appending one rewrite per adjacent
    /// swap (addLeftSwap inside the sum, addIsCommutative for the final
    /// pair). Returns the sorted whole term, or null when a needed sort
    /// lemma is missing or a shape assumption fails.
    pub fn sortTrace(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        comm_idx: ?usize,
        swap_idx: ?usize,
        tower: Tower,
        trace: *std.ArrayList(simplify_mod.Rewrite),
    ) ElabError!?TermId {
        const leaves = try self.arena.dupe(TermId, tower.leaves);
        var whole = (try self.buildTowerSigned(symbols, tower.offset, (try self.buildComb(symbols, leaves)) orelse return null)) orelse return null;
        if (leaves.len > 1) {
            for (0..leaves.len - 1) |pass| {
                for (0..leaves.len - 1 - pass) |i| {
                    if (self.pool.termOrder(leaves[i], leaves[i + 1]) != .gt) continue;
                    const tail_pair = i + 2 == leaves.len;
                    const rule_idx = (if (tail_pair) comm_idx else swap_idx) orelse {
                        self.arith_missing_lemma = if (tail_pair) "addIsCommutative" else "addLeftSwap";
                        return null;
                    };
                    const sub_before = (try self.buildComb(symbols, leaves[i..])) orelse return null;
                    std.mem.swap(TermId, &leaves[i], &leaves[i + 1]);
                    const sub_after = (try self.buildComb(symbols, leaves[i..])) orelse return null;
                    const after = (try self.buildTowerSigned(symbols, tower.offset, (try self.buildComb(symbols, leaves)) orelse return null)) orelse return null;
                    const rule = rules[rule_idx];
                    const bindings = (try simplify_mod.matchRule(self.arena, self.pool, self.env, rule, rule.lhs, sub_before)) orelse return null;
                    try trace.append(self.arena, .{
                        .before = whole,
                        .after = after,
                        .rule_idx = rule_idx,
                        .bindings = bindings,
                        .inst_lhs = sub_before,
                        .inst_rhs = sub_after,
                    });
                    whole = after;
                }
            }
        }
        return whole;
    }

    /// Statement id behind a rule/fact source (axiom or theorem); null for a step.
    fn sourceStatementId(src: simplify_mod.Source) ?StatementId {
        return switch (src) {
            .axiom => |a| a.id,
            .theorem => |t| t.id,
            .step => null,
        };
    }

    /// Index of the well-known rule `name` within `rules` (matched by statement
    /// id, so the certifier reuses the rewrite it already loaded). Null when the
    /// theory doesn't provide it.
    fn ruleIndex(self: *Elaborator, rules: []const simplify_mod.Rule, name_text: []const u8, loc: u32) ElabError!?usize {
        const fact = (try self.wellKnownFact(name_text, loc)) orelse {
            // the rule lemma is not imported into theory scope — record it so the
            // certifier adapter can name it (vs the generic "out of scope").
            self.arith_missing_lemma = name_text;
            return null;
        };
        const want = sourceStatementId(fact.source) orelse return null;
        for (rules, 0..) |r, i| {
            if (sourceStatementId(r.source)) |id| {
                if (id == want) return i;
            }
        }
        return null;
    }

    /// Emit one adjacent swap of `order[pos]` and `order[pos+1]` in the tower
    /// `succ^succs(sum(order))`: addIsCommutative for the tail pair (the last
    /// two summands, where the sub-term is `add(x, y)`), addLeftSwap otherwise
    /// (`add(x, add(y, r))`). Mutates `order`, appends the rewrite, returns the
    /// new whole term. Null if the needed swap lemma is absent.
    fn emitSwap(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        comm_idx: ?usize,
        swap_idx: ?usize,
        offset: i128,
        order: []TermId,
        pos: usize,
        whole: TermId,
        trace: *std.ArrayList(simplify_mod.Rewrite),
    ) ElabError!?TermId {
        const tail_pair = pos + 2 == order.len;
        const rule_idx = (if (tail_pair) comm_idx else swap_idx) orelse {
            self.arith_missing_lemma = if (tail_pair) "addIsCommutative" else "addLeftSwap";
            return null;
        };
        const sub_before = (try self.buildComb(symbols, order[pos..])) orelse return null;
        std.mem.swap(TermId, &order[pos], &order[pos + 1]);
        const sub_after = (try self.buildComb(symbols, order[pos..])) orelse return null;
        const after = (try self.buildTowerSigned(symbols, offset, (try self.buildComb(symbols, order)) orelse return null)) orelse return null;
        const rule = rules[rule_idx];
        const bindings = (try simplify_mod.matchRule(self.arena, self.pool, self.env, rule, rule.lhs, sub_before)) orelse return null;
        try trace.append(self.arena, .{ .before = whole, .after = after, .rule_idx = rule_idx, .bindings = bindings, .inst_lhs = sub_before, .inst_rhs = sub_after });
        return after;
    }

    /// Cancel additive-inverse pairs in a sorted tower `succ^k(sum)`: for each
    /// `neg(x)` leaf with a matching `x` leaf, bubble the pair to the tail
    /// (addLeftSwap/addIsCommutative), collapse it with addNegRight/addNegLeft
    /// (`add(x, neg(x)) = 0`), then drop the ZERO (addZeroLeft/addZeroRight).
    /// Every step is a trace rewrite, so the whole cancellation is kernel-
    /// checked. Returns the reduced whole term.
    pub fn cancelInverses(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        comm_idx: ?usize,
        swap_idx: ?usize,
        offset: i128,
        whole0: TermId,
        trace: *std.ArrayList(simplify_mod.Rewrite),
        loc: u32,
    ) ElabError!?TermId {
        if (symbols.neg == null or symbols.add == null or symbols.zero == null) return whole0;
        const neg_right_idx = (try self.ruleIndex(rules, "addNegRight", loc)) orelse return whole0;
        const neg_left_idx = (try self.ruleIndex(rules, "addNegLeft", loc)) orelse return whole0;
        const zero_left = try self.ruleIndex(rules, "addZeroLeft", loc);
        const zero_right = try self.ruleIndex(rules, "addZeroRight", loc);

        var whole = whole0;
        // re-derive the leaf list from the sorted whole (below the succ prefix).
        outer: while (true) {
            const tower = (try self.parseTower(symbols, whole)) orelse return whole;
            const leaves = tower.leaves;
            // find a neg(x) leaf j and a positive x leaf i (i != j)
            var pair: ?struct { i: usize, j: usize } = null;
            for (leaves, 0..) |lj, j| {
                const nj = self.pool.get(lj);
                if (nj != .app or !symIs(nj.app.sym, symbols.neg)) continue;
                const inner = self.pool.args(nj.app)[0];
                for (leaves, 0..) |li, i| {
                    if (i == j) continue;
                    if (self.pool.alphaEq(li, inner)) {
                        pair = .{ .i = i, .j = j };
                        break;
                    }
                }
                if (pair != null) break;
            }
            const p = pair orelse return whole; // no inverse pairs left

            // Bubble the paired leaves to the TAIL (positions len-2, len-1), so
            // add(x, neg(x)) (or add(neg(x), x)) is a genuine innermost subterm
            // that addNegRight/addNegLeft can rewrite in one step. Move the
            // higher-index member to the last slot, then the lower to second-last.
            var order = try self.arena.dupe(TermId, leaves);
            var lo = p.i;
            var hi = p.j;
            if (lo > hi) {
                const tmp = lo;
                lo = hi;
                hi = tmp;
            }
            const n = order.len;
            // move order[hi] rightward to n-1
            var pos = hi;
            while (pos + 1 < n) : (pos += 1) {
                whole = (try self.emitSwap(symbols, rules, comm_idx, swap_idx, offset, order, pos, whole, trace)) orelse return null;
            }
            // move order[lo] rightward to n-2 (positions below hi are unshifted)
            pos = lo;
            while (pos + 1 < n - 1) : (pos += 1) {
                whole = (try self.emitSwap(symbols, rules, comm_idx, swap_idx, offset, order, pos, whole, trace)) orelse return null;
            }
            // the pair now occupies the last two slots. Positive-first (x, neg(x)
            // → addNegRight) or negative-first (neg(x), x → addNegLeft)?
            const xpos = n - 2;
            const left = order[xpos];
            const right = order[xpos + 1];
            const rule_idx: usize = if (self.pool.alphaEq(right, try self.pool.addApp(.app, symbols.neg.?, &.{left})))
                neg_right_idx // add(x, neg(x)) = 0
            else if (self.pool.alphaEq(left, try self.pool.addApp(.app, symbols.neg.?, &.{right})))
                neg_left_idx // add(neg(x), x) = 0
            else
                return null;

            // collapse the tail pair add(left, right) → ZERO. Since the pair is
            // the innermost add, `add(left, right)` is a genuine subterm.
            const before_cancel = whole;
            const zero = try self.pool.addApp(.app, symbols.zero.?, &.{});
            const pair_term = try self.pool.addApp(.app, symbols.add.?, &.{ left, right });
            const neg_rule = rules[rule_idx];
            const neg_bindings = (try simplify_mod.matchRule(self.arena, self.pool, self.env, neg_rule, neg_rule.lhs, pair_term)) orelse return null;
            // after-term: drop the pair, leave `…+ ZERO` (reduced leaves then +0).
            const reduced = order[0..xpos];
            const comb0 = (try self.buildCombWithZeroTail(symbols, reduced)) orelse return null;
            const after_cancel = (try self.buildTowerSigned(symbols, offset, comb0)) orelse return null;
            try trace.append(self.arena, .{ .before = before_cancel, .after = after_cancel, .rule_idx = rule_idx, .bindings = neg_bindings, .inst_lhs = pair_term, .inst_rhs = zero });
            whole = after_cancel;

            // drop the ZERO: add(0, rest) → rest (addZeroLeft) or add(rest, 0) →
            // rest (addZeroRight). Normalize the whole with just the zero rules.
            const zl = zero_left orelse return null;
            const zr = zero_right orelse return null;
            const zero_rules = [_]simplify_mod.Rule{ rules[zl], rules[zr] };
            const zres = simplify_mod.normalize(self.arena, self.pool, self.env, &zero_rules, whole, 1000) catch return null;
            // zres.trace's rule_idx is relative to the 2-element `zero_rules`
            // (0 = addZeroLeft, 1 = addZeroRight); rebase to the caller's full
            // `rules` array (zl/zr) before appending, or the join cites the
            // wrong rule (only accidentally correct when zl,zr == 0,1).
            for (zres.trace) |rw| {
                var r = rw;
                r.rule_idx = if (rw.rule_idx == 0) zl else zr;
                try trace.append(self.arena, r);
            }
            whole = zres.nf;
            continue :outer;
        }
    }

    /// buildComb but with a trailing ZERO base: l0 + (l1 + ... + (l_{n-1} + 0)).
    fn buildCombWithZeroTail(self: *Elaborator, symbols: presburger_mod.Symbols, leaves: []const TermId) ElabError!?TermId {
        const zero = try self.pool.addApp(.app, symbols.zero orelse return null, &.{});
        var cur = zero;
        var i = leaves.len;
        while (i > 0) {
            i -= 1;
            cur = try self.pool.addApp(.app, symbols.add orelse return null, &.{ leaves[i], cur });
        }
        return cur;
    }

    /// Plan a kernel-checked proof of s = t: normalize both sides with the
    /// terminating rules, then sort the residual sums. Null when the sides
    /// do not join.
    pub fn planEquation(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        term_rule_count: usize,
        comm_idx: ?usize,
        swap_idx: ?usize,
        s: TermId,
        t: TermId,
        loc: u32,
    ) ElabError!?EqCert {
        const rs = simplify_mod.normalize(self.arena, self.pool, self.env, rules[0..term_rule_count], s, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        const rt = simplify_mod.normalize(self.arena, self.pool, self.env, rules[0..term_rule_count], t, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        const tower_s = (try self.parseTower(symbols, rs.nf)) orelse return null;
        const tower_t = (try self.parseTower(symbols, rt.nf)) orelse return null;
        if (tower_s.offset != tower_t.offset) return null;

        var trace_s: std.ArrayList(simplify_mod.Rewrite) = .empty;
        try trace_s.appendSlice(self.arena, rs.trace);
        var sorted_s = (try self.sortTrace(symbols, rules, comm_idx, swap_idx, tower_s, &trace_s)) orelse return null;
        var trace_t: std.ArrayList(simplify_mod.Rewrite) = .empty;
        try trace_t.appendSlice(self.arena, rt.trace);
        var sorted_t = (try self.sortTrace(symbols, rules, comm_idx, swap_idx, tower_t, &trace_t)) orelse return null;
        // cancel additive-inverse pairs (x + neg(x) → 0) in each sorted sum, so
        // e.g. {a, b, neg(a)} reduces to {b}. Emits addNegRight + zero-drop
        // rewrites into the trace (kernel-checked like every other rewrite).
        sorted_s = (try self.cancelInverses(symbols, rules, comm_idx, swap_idx, tower_s.offset, sorted_s, &trace_s, loc)) orelse return null;
        sorted_t = (try self.cancelInverses(symbols, rules, comm_idx, swap_idx, tower_t.offset, sorted_t, &trace_t, loc)) orelse return null;
        // same multiset of variables (and same tower) iff the sorted forms agree
        if (!self.pool.alphaEq(sorted_s, sorted_t)) return null;
        return .{
            .rules = rules,
            .s = s,
            .t = t,
            .rs = .{ .nf = sorted_s, .trace = trace_s.items },
            .rt = .{ .nf = sorted_t, .trace = trace_t.items },
        };
    }

    /// Plan a kernel-checked proof of less_than(s, t): synthesize the difference
    /// witness d from the normalized towers, certify add(s, succ(d)) = t,
    /// and instantiate lessThanIntro.
    fn planLess(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        term_rule_count: usize,
        comm_idx: ?usize,
        swap_idx: ?usize,
        body: TermId,
        loc: u32,
    ) ElabError!?LtCert {
        const pred = self.pool.get(body).pred;
        const pred_args = self.pool.args(pred);
        const s = pred_args[0];
        const t = pred_args[1];
        const rs = simplify_mod.normalize(self.arena, self.pool, self.env, rules[0..term_rule_count], s, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        const rt = simplify_mod.normalize(self.arena, self.pool, self.env, rules[0..term_rule_count], t, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        const tower_s = (try self.parseTower(symbols, rs.nf)) orelse return null;
        const tower_t = (try self.parseTower(symbols, rt.nf)) orelse return null;
        if (tower_t.offset < tower_s.offset + 1) return null;

        // multiset difference t - s: every s-leaf must be consumed
        var remaining: std.ArrayList(TermId) = .empty;
        try remaining.appendSlice(self.arena, tower_t.leaves);
        for (tower_s.leaves) |sl| {
            const found = for (remaining.items, 0..) |rl, i| {
                if (self.pool.termOrder(rl, sl) == .eq) break i;
            } else return null;
            _ = remaining.swapRemove(found);
        }

        const d_comb = (try self.buildComb(symbols, remaining.items)) orelse return null;
        const d = (try self.buildTowerSigned(symbols, tower_t.offset - tower_s.offset - 1, d_comb)) orelse return null;
        const succ_sym = symbols.succ orelse return null;
        const add_sym = symbols.add orelse return null;
        const succ_d = try self.pool.addApp(.app, succ_sym, &.{d});
        const eq_lhs = try self.pool.addApp(.app, add_sym, &.{ s, succ_d });
        const eq = (try self.planEquation(symbols, rules, term_rule_count, comm_idx, swap_idx, eq_lhs, t, loc)) orelse return null;
        const eq_formula = try self.pool.add(.{ .eq = .{ .lhs = eq_lhs, .rhs = t } });

        // lessThanIntro, matched structurally so any binder order works
        const intro_fact = (try self.wellKnownFact("lessThanIntro", loc)) orelse return null;
        const intro = try self.strippedRule(intro_fact.formula, intro_fact.source);
        const implication = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = eq_formula, .rhs = body } });
        const intro_args = (try simplify_mod.matchRule(self.arena, self.pool, self.env, intro, intro.lhs, implication)) orelse return null;
        return .{ .eq = eq, .eq_formula = eq_formula, .intro = intro, .intro_args = intro_args };
    }

    fn emitLess(self: *Elaborator, low: *Lowering, block: kernel.BlockId, loc: u32, lt: LtCert) ElabError!kernel.Justification {
        const eq_just = try self.emitJoin(low, block, loc, lt.eq.rules, lt.eq.s, lt.eq.t, lt.eq.rs, lt.eq.rt);
        const eq_ref = try self.emitStep(low, block, loc, lt.eq_formula, eq_just);
        const imp_ref = try self.emitInstance(low, block, loc, lt.intro, lt.intro_args);
        return .{ .modus_ponens = .{ .implication = imp_ref, .antecedent = eq_ref } };
    }

    // --- the `tautology` accelerated tactic: propositional consequence ------
    // The engine (src/smt.zig) decides; a `.valid` verdict becomes an
    // `.accelerated` kernel step the kernel accepts without a derivation. The
    // accelerated-tactic name marks the enclosing theorem accelerated; see
    // ACCELERATION.md.

    /// Record that the current proof leans on accelerated tactic `name`. By
    /// default this is a hard error — the goal must certify; the accelerated
    /// verdict is only accepted in `--fast` (verify.certify_arithmetic = false),
    /// where it marks the theorem accelerated.
    pub fn recordAccelerated(self: *Elaborator, name: StrId, loc: u32) ElabError!void {
        if (self.verify.certify_arithmetic) {
            return self.fail(loc, "'{s}' could not be emitted as kernel steps here; use --fast to accept the accelerated verdict", .{self.interner.stringBytes(name)});
        }
        for (self.accelerated_used.items) |o| {
            if (o == name) return;
        }
        try self.accelerated_used.append(self.arena, name);
    }

    /// Register a synthetic (mangled-name, count-suppressed) theorem as UNPROVEN
    /// and return its id. Split from `finishSyntheticTheorem` so a caller can bind
    /// the id BEFORE building the proof steps (needed when the steps cite the
    /// theorem itself — model's recursive materialization). `$` in the name is
    /// lexically impossible for a user, so no collision.
    pub fn beginSyntheticTheorem(self: *Elaborator, name: StrId, formula: TermId, loc: u32) ElabError!StatementId {
        return try self.env.addStatement(self.file, name, .{ .theorem = .{
            .name = name,
            .formula = formula,
            .loc = loc,
            .proven = false,
            .synthetic = true,
        } });
    }

    /// Kernel-check a synthetic theorem's proof `{steps, blocks}` against its
    /// stated `formula`, and on success mark it proven, retain the lowered proof
    /// (so an outer materialization can re-use it), and record its provenance
    /// (`accelerated`/`holes` it leans on). The `k.check` here is the soundness
    /// anchor — it ALWAYS runs when a synthetic theorem is produced, and is never
    /// skipped by `--faster`/`--reckless` (those imply `certify_arithmetic=false`,
    /// so no synthetic theorem is produced at all). `on_fail` is the located error.
    pub fn finishSyntheticTheorem(
        self: *Elaborator,
        id: StatementId,
        steps: []const kernel.Step,
        blocks: []const kernel.Block,
        accelerated: []const StrId,
        holes: []const StrId,
        loc: u32,
        on_fail: []const u8,
    ) ElabError!void {
        const formula = self.env.statements.items[@intFromEnum(id)].theorem.formula;
        var k: kernel.Kernel = .{
            .arena = self.arena,
            .pool = self.pool,
            .env = self.env,
            .interner = self.interner,
            .sink = self.sink,
        };
        const ok = try k.check(.{ .steps = steps, .blocks = blocks }, formula, loc);
        if (!ok) return self.fail(loc, "{s}", .{on_fail});
        const fact = &self.env.statements.items[@intFromEnum(id)].theorem;
        fact.proven = true;
        fact.accelerated = accelerated;
        fact.holes = holes;
        fact.proof = .{ .steps = steps, .blocks = blocks };
    }

    /// The one-shot form: register + check + finalize a synthetic theorem whose
    /// proof does NOT cite itself. Returns the id (caller cites it via
    /// `theorem_ref`, or `forall_elim` of it). This is the shared "wrap kernel
    /// steps into a named theorem" primitive — used by accelerant certificate
    /// production (the steps an accelerant would have spliced inline become this
    /// theorem's proof). See MODEL-DESIGN.md / the accelerant-unification plan.
    pub fn wrapAsTheorem(
        self: *Elaborator,
        name: StrId,
        formula: TermId,
        steps: []const kernel.Step,
        blocks: []const kernel.Block,
        accelerated: []const StrId,
        holes: []const StrId,
        loc: u32,
        on_fail: []const u8,
    ) ElabError!StatementId {
        const id = try self.beginSyntheticTheorem(name, formula, loc);
        try self.finishSyntheticTheorem(id, steps, blocks, accelerated, holes, loc, on_fail);
        return id;
    }

    /// Citing a fact inherits its accelerated-tactic names.
    pub fn inheritAccelerated(self: *Elaborator, names: []const StrId) Allocator.Error!void {
        outer: for (names) |name| {
            for (self.accelerated_used.items) |o| {
                if (o == name) continue :outer;
            }
            try self.accelerated_used.append(self.arena, name);
        }
    }

    /// Record hole dependence for the current theorem: `names` are the holes a
    /// cited fact rests on (a hole is [its own name]; a theorem is its `holes`).
    pub fn inheritHoles(self: *Elaborator, names: []const StrId) Allocator.Error!void {
        outer: for (names) |name| {
            for (self.holes_used.items) |o| {
                if (o == name) continue :outer;
            }
            try self.holes_used.append(self.arena, name);
        }
    }

    /// Resolve an accelerated tactic's premise refs to formulas (accessible step
    /// labels first, then statements); theorem citations inherit accelerated-tactic names.
    pub fn resolvePremises(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, c: ast.Step.Claim, comptime rule: []const u8) ElabError![]const TermId {
        const premises = try self.arena.alloc(TermId, c.refs.len);
        for (c.refs, premises) |ref, *out| {
            const name = try self.internTok(ref);
            if (low.labels.get(name)) |target| switch (target) {
                .step => |sid| {
                    const s = low.steps.items[@intFromEnum(sid)];
                    if (!lowAncestorOrSelf(low, s.block, block_id)) {
                        return self.fail(ref.start, "'{s}' is not accessible from this step (closed subproof)", .{self.text(ref)});
                    }
                    out.* = s.formula;
                },
                .block => return self.fail(ref.start, "'{s}' names a subproof; " ++ rule ++ " takes formulas", .{self.text(ref)}),
            } else {
                const stmt_id = try self.resolveStatementRef(ref);
                const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
                switch (stmt) {
                    .axiom => |a| out.* = a.formula,
                    .theorem => |t| {
                        if (!t.proven) return self.fail(ref.start, "cites unproven theorem '{s}'", .{self.text(ref)});
                        try self.inheritAccelerated(t.accelerated);
                        out.* = t.formula;
                    },
                    .schema => return self.fail(ref.start, "'{s}' is a schema; " ++ rule ++ " takes formulas", .{self.text(ref)}),
                }
            }
        }
        return premises;
    }

    /// Prove `goal` propositionally from already-emitted premise steps (each a
    /// `{formula, ref}`), replaying the truth search as kernel steps. Returns
    /// null (rolling back to the marks) when the step budget runs out. Shared by
    /// the surface `tautology` cert and any tactic that synthesizes premises
    /// then wants a propositional close (e.g. `ext`'s set residue).
    pub fn emitTautologyFrom(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, premise_steps: []const TautCert.Premise, loc: u32, steps_mark: usize, blocks_mark: usize) ElabError!?kernel.Justification {
        var atoms: std.ArrayList(TermId) = .empty;
        for (premise_steps) |p| try smt_mod.collectAtoms(self.arena, self.pool, &atoms, p.formula);
        try smt_mod.collectAtoms(self.arena, self.pool, &atoms, goal);

        const assignment = try self.arena.alloc(?bool, atoms.items.len);
        @memset(assignment, null);
        const lits = try self.arena.alloc(?TautCert.Lit, atoms.items.len);
        @memset(lits, null);
        var cert: TautCert = .{
            .elab = self,
            .low = low,
            .loc = loc,
            .goal = goal,
            .premises = premise_steps,
            .atoms = atoms.items,
            .assignment = assignment,
            .lits = lits,
        };
        const just = cert.goalJust(block_id) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return error.Recover,
            error.Budget => {
                low.steps.shrinkRetainingCapacity(steps_mark);
                low.blocks.shrinkRetainingCapacity(blocks_mark);
                return null;
            },
        };
        return just;
    }

    pub const TautCert = struct {
        elab: *Elaborator,
        low: *Lowering,
        loc: u32,
        goal: TermId,
        premises: []const Premise,
        atoms: []const TermId,
        assignment: []?bool,
        /// per atom: the assume block whose hypothesis is the literal
        lits: []?Lit,
        budget: usize = 2000,
        /// D2: with the arithmetic vocabulary present, a branch whose goal
        /// is boolean-false may still close by deriving a false-assigned
        /// theory atom from the true-assigned literals (absurd)
        symbols: ?presburger_mod.Symbols = null,

        pub const Premise = struct { formula: TermId, ref: kernel.SRef };
        pub const Lit = struct { block: kernel.BlockId, positive: bool };
        const CertError = error{ Budget, Recover, OutOfMemory };

        fn emit(self: *TautCert, block: kernel.BlockId, formula: TermId, just: kernel.Justification) CertError!kernel.SRef {
            if (self.budget == 0) return error.Budget;
            self.budget -= 1;
            return self.elab.emitStep(self.low, block, self.loc, formula, just);
        }

        fn openAssume(self: *TautCert, parent: kernel.BlockId, formula: TermId) CertError!kernel.BlockId {
            return self.elab.newBlock(self.low, try self.elab.freshNamed("tautology"), parent, .{ .assume = formula });
        }

        fn bref(self: *const TautCert, block: kernel.BlockId) kernel.BRef {
            return .{ .id = block, .loc = self.loc };
        }

        fn eval(self: *const TautCert, f: TermId) ?bool {
            return smt_mod.eval(self.elab.pool, self.atoms, self.assignment, f);
        }

        fn litOf(self: *const TautCert, f: TermId) Lit {
            for (self.atoms, self.lits) |a, lit| {
                if (self.elab.pool.alphaEq(a, f)) return lit.?; // assigned, or eval could not have decided
            }
            unreachable; // every leaf is a collected atom
        }

        /// Justification for a step claiming the goal in `block` (the step
        /// itself is not emitted — the caller owns the claim).
        pub fn goalJust(self: *TautCert, block: kernel.BlockId) CertError!kernel.Justification {
            for (self.premises) |p| {
                if (self.eval(p.formula) == false) {
                    const refuted = try self.deriveFalse(block, p.formula);
                    return .{ .absurd = .{ .s1 = p.ref, .s2 = refuted } };
                }
            }
            if (self.eval(self.goal) == true) {
                return self.trueJust(block, self.goal);
            }
            if (self.eval(self.goal) == false) {
                // boolean dead end: only a theory conflict can close it
                if (try self.theoryLeaf(block)) |just| return just;
                if (std.mem.indexOfScalar(?bool, self.assignment, null) == null) {
                    return error.Budget; // fully assigned and underivable
                }
                // more literals may make the conflict derivable: keep splitting
            }
            // split on the first unassigned atom with an inline excluded
            // middle and recurse into both branches
            const idx = for (self.assignment, 0..) |v, i| {
                if (v == null) break i;
            } else unreachable; // an unassigned atom exists here
            const atom = self.atoms[idx];
            const not_atom = try self.pool().add(.{ .not = atom });
            const disj = try self.pool().add(.{ .bin = .{ .op = .or_op, .lhs = atom, .rhs = not_atom } });
            const lem = try self.emitLem(block, atom, not_atom, disj);

            const left = try self.openAssume(block, atom);
            self.assignment[idx] = true;
            self.lits[idx] = .{ .block = left, .positive = true };
            const left_just = try self.goalJust(left);
            _ = try self.emit(left, self.goal, left_just);
            self.elab.closeBlock(self.low, left);

            const right = try self.openAssume(block, not_atom);
            self.assignment[idx] = false;
            self.lits[idx] = .{ .block = right, .positive = false };
            const right_just = try self.goalJust(right);
            _ = try self.emit(right, self.goal, right_just);
            self.elab.closeBlock(self.low, right);

            self.assignment[idx] = null;
            self.lits[idx] = null;
            return .{ .or_elim = .{ .disj = lem, .left = self.bref(left), .right = self.bref(right) } };
        }

        fn pool(self: *const TautCert) *term.Pool {
            return self.elab.pool;
        }

        /// Is this atom usable by the arithmetic certificate core?
        fn arithAtom(self: *const TautCert, atom: TermId) bool {
            const symbols = self.symbols orelse return false;
            const node = self.pool().get(atom);
            return node == .eq or
                (node == .pred and symIs(node.pred.sym, symbols.less_than) and node.pred.args_len == 2);
        }

        /// D2 leaf: derive some false-assigned theory atom from the
        /// true-assigned literals, then explode it against its assumption.
        fn theoryLeaf(self: *TautCert, block: kernel.BlockId) CertError!?kernel.Justification {
            const symbols = self.symbols orelse return null;
            // the true-assigned arithmetic literals, restated as steps
            var cert_premises: std.ArrayList(accel_arithmetic.CertPremise) = .empty;
            for (self.atoms, self.assignment, self.lits) |atom, value, lit| {
                if (value != true or !self.arithAtom(atom)) continue;
                const ref = try self.emit(block, atom, .{ .hypothesis = self.bref(lit.?.block) });
                try cert_premises.append(self.elab.arena, .{
                    .formula = atom,
                    .step = ref,
                    .statement = null,
                    .rule_idx = undefined,
                    .elim = null,
                });
            }
            // rule premises that hold on this branch participate too
            for (self.premises) |p| {
                if (self.eval(p.formula) != true or !self.arithAtom(p.formula)) continue;
                try cert_premises.append(self.elab.arena, .{
                    .formula = p.formula,
                    .step = p.ref,
                    .statement = null,
                    .rule_idx = undefined,
                    .elim = null,
                });
            }
            for (self.atoms, self.assignment, 0..) |atom, value, idx| {
                if (value != false or !self.arithAtom(atom)) continue;
                const just = (try accel_arithmetic.arithCertCore(self.elab, self.low, block, atom, cert_premises.items, symbols, self.loc)) orelse continue;
                const derived = try self.emit(block, atom, just);
                const not_atom = try self.pool().add(.{ .not = atom });
                const refuted = try self.emit(block, not_atom, .{ .hypothesis = self.bref(self.lits[idx].?.block) });
                return .{ .absurd = .{ .s1 = derived, .s2 = refuted } };
            }
            return null;
        }

        /// atom or not atom, the classical way: not_intro on the negated
        /// disjunction, then double_negation
        fn emitLem(self: *TautCert, block: kernel.BlockId, atom: TermId, not_atom: TermId, disj: TermId) CertError!kernel.SRef {
            const not_disj = try self.pool().add(.{ .not = disj });
            const outer = try self.openAssume(block, not_disj);
            const hyp_outer = try self.emit(outer, not_disj, .{ .hypothesis = self.bref(outer) });
            const inner = try self.openAssume(outer, atom);
            const hyp_inner = try self.emit(inner, atom, .{ .hypothesis = self.bref(inner) });
            const or_left = try self.emit(inner, disj, .{ .or_intro_left = hyp_inner });
            self.elab.closeBlock(self.low, inner);
            const derived_not = try self.emit(outer, not_atom, .{ .not_intro = .{ .block = self.bref(inner), .s1 = or_left, .s2 = hyp_outer } });
            const or_right = try self.emit(outer, disj, .{ .or_intro_right = derived_not });
            self.elab.closeBlock(self.low, outer);
            const not_not = try self.pool().add(.{ .not = not_disj });
            const nn = try self.emit(block, not_not, .{ .not_intro = .{ .block = self.bref(outer), .s1 = or_right, .s2 = hyp_outer } });
            return self.emit(block, disj, .{ .double_negation = nn });
        }

        /// Emit a step proving `f` (which evaluates true) in `block`.
        fn deriveTrue(self: *TautCert, block: kernel.BlockId, f: TermId) CertError!kernel.SRef {
            const just = try self.trueJust(block, f);
            return self.emit(block, f, just);
        }

        fn trueJust(self: *TautCert, block: kernel.BlockId, f: TermId) CertError!kernel.Justification {
            switch (self.pool().get(f)) {
                .bin => |b| switch (b.op) {
                    .and_op => return .{ .and_intro = .{
                        .left = try self.deriveTrue(block, b.lhs),
                        .right = try self.deriveTrue(block, b.rhs),
                    } },
                    .or_op => {
                        if (self.eval(b.lhs) == true) {
                            return .{ .or_intro_left = try self.deriveTrue(block, b.lhs) };
                        }
                        return .{ .or_intro_right = try self.deriveTrue(block, b.rhs) };
                    },
                    .implies => {
                        const blk = try self.openAssume(block, b.lhs);
                        if (self.eval(b.rhs) == true) {
                            _ = try self.deriveTrue(blk, b.rhs);
                        } else {
                            // the antecedent is false: assume it and explode
                            const hyp = try self.emit(blk, b.lhs, .{ .hypothesis = self.bref(blk) });
                            const refuted = try self.deriveFalse(blk, b.lhs);
                            _ = try self.emit(blk, b.rhs, .{ .absurd = .{ .s1 = hyp, .s2 = refuted } });
                        }
                        self.elab.closeBlock(self.low, blk);
                        return .{ .implies_intro = self.bref(blk) };
                    },
                },
                // f = not inner, true: exactly a proof that inner is false
                .not => |inner| return self.falseJust(block, inner),
                // an atom assigned true: restate its assumption
                else => return .{ .hypothesis = self.bref(self.litOf(f).block) },
            }
        }

        /// Emit a step proving `not f` (f evaluates false) in `block`.
        fn deriveFalse(self: *TautCert, block: kernel.BlockId, f: TermId) CertError!kernel.SRef {
            const just = try self.falseJust(block, f);
            const nf = try self.pool().add(.{ .not = f });
            return self.emit(block, nf, just);
        }

        fn falseJust(self: *TautCert, block: kernel.BlockId, f: TermId) CertError!kernel.Justification {
            switch (self.pool().get(f)) {
                .bin => |b| switch (b.op) {
                    .and_op => {
                        // a false conjunct refutes the conjunction
                        const left_false = self.eval(b.lhs) == false;
                        const side = if (left_false) b.lhs else b.rhs;
                        const refuted = try self.deriveFalse(block, side);
                        const blk = try self.openAssume(block, f);
                        const hyp = try self.emit(blk, f, .{ .hypothesis = self.bref(blk) });
                        const elim = try self.emit(blk, side, if (left_false)
                            .{ .and_elim_left = hyp }
                        else
                            .{ .and_elim_right = hyp });
                        self.elab.closeBlock(self.low, blk);
                        return .{ .not_intro = .{ .block = self.bref(blk), .s1 = elim, .s2 = refuted } };
                    },
                    .or_op => {
                        // both disjuncts are false; case-split to reproduce
                        // the left one, contradicting its refutation
                        const not_left = try self.deriveFalse(block, b.lhs);
                        const not_right = try self.deriveFalse(block, b.rhs);
                        const blk = try self.openAssume(block, f);
                        const hyp = try self.emit(blk, f, .{ .hypothesis = self.bref(blk) });
                        const left = try self.openAssume(blk, b.lhs);
                        _ = try self.emit(left, b.lhs, .{ .hypothesis = self.bref(left) });
                        self.elab.closeBlock(self.low, left);
                        const right = try self.openAssume(blk, b.rhs);
                        const rh = try self.emit(right, b.rhs, .{ .hypothesis = self.bref(right) });
                        _ = try self.emit(right, b.lhs, .{ .absurd = .{ .s1 = rh, .s2 = not_right } });
                        self.elab.closeBlock(self.low, right);
                        const conc = try self.emit(blk, b.lhs, .{ .or_elim = .{ .disj = hyp, .left = self.bref(left), .right = self.bref(right) } });
                        self.elab.closeBlock(self.low, blk);
                        return .{ .not_intro = .{ .block = self.bref(blk), .s1 = conc, .s2 = not_left } };
                    },
                    .implies => {
                        // true antecedent, false consequent
                        const ante = try self.deriveTrue(block, b.lhs);
                        const not_conseq = try self.deriveFalse(block, b.rhs);
                        const blk = try self.openAssume(block, f);
                        const hyp = try self.emit(blk, f, .{ .hypothesis = self.bref(blk) });
                        const conseq = try self.emit(blk, b.rhs, .{ .modus_ponens = .{ .implication = hyp, .antecedent = ante } });
                        self.elab.closeBlock(self.low, blk);
                        return .{ .not_intro = .{ .block = self.bref(blk), .s1 = conseq, .s2 = not_conseq } };
                    },
                },
                .not => |inner| {
                    // not f = not not inner, with inner true
                    const truth = try self.deriveTrue(block, inner);
                    const blk = try self.openAssume(block, f);
                    const hyp = try self.emit(blk, f, .{ .hypothesis = self.bref(blk) });
                    self.elab.closeBlock(self.low, blk);
                    return .{ .not_intro = .{ .block = self.bref(blk), .s1 = truth, .s2 = hyp } };
                },
                // an atom assigned false: its assumption IS the negation
                else => return .{ .hypothesis = self.bref(self.litOf(f).block) },
            }
        }
    };

    pub fn wellKnownSym(self: *Elaborator, name: []const u8) ElabError!?term.SymId {
        const id = self.interner.internString(name) catch return error.OutOfMemory;
        return self.env.findSym(self.theoryScope(), id);
    }

    fn checkFreshName(self: *Elaborator, name: StrId, tok: lexer.Token) ElabError!void {
        if (std.mem.indexOfScalar(u8, self.text(tok), '.') != null) {
            return self.fail(tok.start, "declared names cannot be qualified", .{});
        }
        if (self.env.nameTaken(self.file, name)) {
            return self.fail(tok.start, "duplicate declaration of '{s}'", .{self.text(tok)});
        }
    }

    pub fn resolveSort(self: *Elaborator, tok: lexer.Token) ElabError!SortId {
        const target = try self.resolveTarget(tok);
        return self.env.findSort(target.file, target.base) orelse
            self.fail(tok.start, "unknown sort '{s}'", .{self.text(tok)});
    }

    /// The guard qualifiers of a (possibly refined) sort — the predicates that a
    /// value of this sort satisfies. Empty for a base sort. Used to inject guards
    /// at binders and obligations at applications.
    fn sortQualifiers(self: *Elaborator, id: SortId) ElabError![]const term.SymId {
        return self.env.qualifiersOf(self.arena, id) catch return error.OutOfMemory;
    }

    /// Resolve a binder's sort, minting an ANONYMOUS refined sort when the binder
    /// carries an inline `where inH` (`x: G where inH`). The anonymous sort refines
    /// the base sort by the guard predicate (validated unary over the base); it is
    /// unnamed (no scope binding) but carries the same ECS refinement component as a
    /// named `sort H = G where inH`, so all downstream (carrierOf/qualifiersOf) works.
    fn resolveBinderSort(self: *Elaborator, b: ast.Binder) ElabError!SortId {
        const base = try self.resolveSort(b.sort);
        const g = b.guard orelse return base;
        const gname = try self.internTok(g);
        const gsym = self.env.findSym(self.file, gname) orelse
            return self.fail(g.start, "sort refinement '{s}' is not a predicate in scope", .{self.text(g)});
        const sym = self.env.sym(gsym);
        // A define'd guard is REIFIED (task #125): it rides along as a qualifier
        // symbol and its uses expand to the inlined body (see qualifierApp). The
        // unary-pred check below still applies.
        const arg_ok = sym.arg_sorts.len == 1 and
            self.env.carrierOf(sym.arg_sorts[0]) == self.env.carrierOf(base);
        if (sym.kind != .pred or !arg_ok) {
            return self.fail(g.start, "sort refinement '{s}' must be a unary predicate over '{s}'", .{ self.text(g), self.text(b.sort) });
        }
        const quals = try self.arena.dupe(term.SymId, &.{gsym});
        // anonymous: name it by its literal surface syntax (`G where inH`) — spaces
        // make it collision-proof, and if it ever surfaces in a diagnostic it reads
        // exactly as the source. No scope binding.
        const label = std.fmt.allocPrint(self.arena, "{s} where {s}", .{ self.text(b.sort), self.text(g) }) catch return error.OutOfMemory;
        const nm = self.interner.internString(label) catch return error.OutOfMemory;
        return self.env.addAnonymousRefinedSort(nm, b.sort.start, base, quals) catch return error.OutOfMemory;
    }

    /// Apply a unary qualifier predicate `qpred` to argument `arg`, yielding the
    /// guard proposition `qpred(arg)`. If `qpred` is a transparent (`define`d)
    /// predicate, this EXPANDS its body with `arg` substituted for the sole param
    /// (`where`-reification, task #125) — a define carries no kernel symbol, so the
    /// guard must be its inlined body, exactly as a call-site expansion. An opaque
    /// pred builds the ordinary application.
    fn qualifierApp(self: *Elaborator, qpred: term.SymId, arg: TermId) ElabError!TermId {
        const sym = self.env.sym(qpred);
        if (sym.definition) |body| {
            // a where-guard pred is validated unary, so exactly one param to bind.
            return self.pool.substFvar(body, sym.param_names[0], arg);
        }
        return self.pool.addApp(.pred, qpred, &.{arg});
    }

    /// The guard formula for a predicated fix/unpack eigenvariable `v` of sort
    /// `sort_tok`: the conjunction of `qual(v)` over the sort's qualifiers, or null
    /// if the sort is unrefined. (`v.sort` is already the carrier.)
    fn fixGuard(self: *Elaborator, sort_tok: lexer.Token, v: term.Node.Fvar) ElabError!?TermId {
        const quals = try self.sortQualifiers(try self.resolveSort(sort_tok));
        if (quals.len == 0) return null;
        const fv = try self.pool.add(.{ .fvar = v });
        var g: ?TermId = null;
        for (quals) |qpred| {
            const app = try self.qualifierApp(qpred, fv);
            g = if (g) |prev| try self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = prev, .rhs = app } }) else app;
        }
        return g;
    }

    const Target = struct { file: FileId, base: StrId };

    /// The elaboration context that must follow an AST across files: which
    /// source its tokens index, which file scope resolves its names, and
    /// which file its diagnostics blame.
    pub const Ctx = struct { source: []const u8, file: FileId, diag: u32 };

    fn swapCtx(self: *Elaborator, ctx: Ctx) Ctx {
        const old: Ctx = .{ .source = self.source, .file = self.file, .diag = self.sink.current_file };
        self.source = ctx.source;
        self.file = ctx.file;
        self.sink.current_file = ctx.diag;
        return old;
    }

    /// Split an (optionally) qualified name: `peano.Nat` resolves the
    /// namespace to its file; a bare name resolves in the current file.
    fn resolveTarget(self: *Elaborator, tok: lexer.Token) ElabError!Target {
        const text_ = self.text(tok);
        const i = std.mem.indexOfScalar(u8, text_, '.') orelse
            return .{ .file = self.file, .base = try self.internTok(tok) };
        const rest = text_[i + 1 ..];
        if (std.mem.indexOfScalar(u8, rest, '.') != null) {
            return self.fail(tok.start, "only one level of namespace qualification is allowed", .{});
        }
        const ns = self.interner.internString(text_[0..i]) catch return error.OutOfMemory;
        const file = self.env.findNamespace(self.file, ns) orelse
            return self.fail(tok.start, "unknown namespace '{s}'", .{text_[0..i]});
        const base = self.interner.internString(rest) catch return error.OutOfMemory;
        return .{ .file = file, .base = base };
    }

    fn resolveParams(self: *Elaborator, params: []const ast.Binder) ElabError!struct { []const SortId, []const StrId } {
        const sorts = try self.arena.alloc(SortId, params.len);
        const names = try self.arena.alloc(StrId, params.len);
        for (params, sorts, names, 0..) |p, *s, *n, i| {
            // a param may be a predicated sort (named `H` or inline `G where inH`);
            // the stored (kernel) arg sort is its carrier. (Obligations from
            // H-typed args are folded into the func guard in the func decl.)
            s.* = self.env.carrierOf(try self.resolveBinderSort(p));
            n.* = try self.internTok(p.name);
            try self.checkNoShadow(n.*, p.name);
            for (names[0..i]) |prev| {
                if (prev == n.*) {
                    return self.fail(p.name.start, "duplicate parameter '{s}'", .{self.text(p.name)});
                }
            }
        }
        return .{ sorts, names };
    }

    fn requireProp(self: *Elaborator, typed: Typed, e: *const ast.Expr) ElabError!Typed {
        if (typed.sort != .prop) {
            return self.fail(exprLoc(e), "expected a proposition, got sort '{s}'", .{self.sortName(typed.sort)});
        }
        return typed;
    }

    pub fn exprLoc(e: *const ast.Expr) u32 {
        return switch (e.*) {
            .name => |t| t.start,
            .call => |c| c.callee.start,
            .binary => |b| exprLoc(b.lhs),
            .not => |n| n.tok.start,
            .quant => |q| q.tok.start,
            .lambda => |l| l.tok.start,
        };
    }

    /// No-shadowing rule (checker-enforced): a newly introduced variable or
    /// parameter may not reuse any visible name — a variable in scope, a
    /// schema parameter, or any declared symbol.
    fn checkNoShadow(self: *Elaborator, name: StrId, tok: lexer.Token) ElabError!void {
        for (self.scope.items) |entry| {
            if (entry.name == name) {
                return self.fail(tok.start, "'{s}' shadows a variable in scope; choose a fresh name", .{self.text(tok)});
            }
        }
        if (self.schema_args) |sa| {
            if (sa.contains(name)) {
                return self.fail(tok.start, "'{s}' shadows a schema parameter; choose a fresh name", .{self.text(tok)});
            }
        }
        if (self.env.findSym(self.file, name) != null) {
            return self.fail(tok.start, "'{s}' shadows a declaration; choose a fresh name", .{self.text(tok)});
        }
    }

    fn freshName(self: *Elaborator) ElabError!StrId {
        return self.freshNamed("b");
    }

    /// The name to SHOW for an interned identifier: everything up to the first
    /// `#`. Eigenvariables and other hygienic names carry a `#<n>` disambiguator
    /// (see `bindProofVar` / `freshNamed`); `#` is not a legal identifier
    /// character, so trimming there recovers exactly what the author wrote. Used
    /// by diagnostics that print a bare fvar name outside the `print.zig`
    /// Printer (which strips independently via its own `displayName`).
    pub fn displayName(interned: []const u8) []const u8 {
        return if (std.mem.indexOfScalar(u8, interned, '#')) |i| interned[0..i] else interned;
    }

    /// hygienic '#'-name with a readable prefix ("simplify#3" in diagnostics,
    /// or a disambiguated eigenvariable "x#7"). The prefix may be an arbitrary
    /// user identifier, so allocate rather than risk truncation.
    pub fn freshNamed(self: *Elaborator, prefix: []const u8) ElabError!StrId {
        self.fresh_counter += 1;
        const s = std.fmt.allocPrint(self.arena, "{s}#{d}", .{ prefix, self.fresh_counter }) catch return error.OutOfMemory;
        return self.interner.internString(s) catch error.OutOfMemory;
    }

    pub fn elaborateExpr(self: *Elaborator, e: *const ast.Expr) ElabError!Typed {
        switch (e.*) {
            .name => |tok| return self.elaborateName(tok),
            .call => |c| return self.elaborateCall(c),
            .binary => |b| switch (b.op) {
                .implies, .and_op, .or_op => {
                    const lhs = try self.requireProp(try self.elaborateExpr(b.lhs), b.lhs);
                    const tcc_start = self.pending_tccs.items.len;
                    const rhs = try self.requireProp(try self.elaborateExpr(b.rhs), b.rhs);
                    // context collection: obligations inside the RHS of an
                    // implication hold under its antecedent; inside the RHS of
                    // a conjunction, under its left conjunct. Disjunction and
                    // negation contribute nothing (conservative).
                    if (b.op == .implies or b.op == .and_op) {
                        for (self.pending_tccs.items[tcc_start..]) |*t| {
                            t.formula = try self.pool.add(.{ .bin = .{
                                .op = .implies,
                                .lhs = lhs.id,
                                .rhs = t.formula,
                            } });
                        }
                    }
                    const op: term.BinOp = switch (b.op) {
                        .implies => .implies,
                        .and_op => .and_op,
                        .or_op => .or_op,
                        else => unreachable,
                    };
                    const id = try self.pool.add(.{ .bin = .{ .op = op, .lhs = lhs.id, .rhs = rhs.id } });
                    return .{ .id = id, .sort = .prop };
                },
                .iff => {
                    // SURFACE SUGAR: `P iff Q` desugars to `(P -> Q) and (Q -> P)`.
                    // The kernel never sees an iff — it sees the conjunction of
                    // implications (so `tautology` and the like handle it for free,
                    // and `iff_rewrite` reads this exact shape). TCC context is
                    // conservative (like disjunction): no antecedent threading.
                    const lhs = try self.requireProp(try self.elaborateExpr(b.lhs), b.lhs);
                    const rhs = try self.requireProp(try self.elaborateExpr(b.rhs), b.rhs);
                    const fwd = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = lhs.id, .rhs = rhs.id } });
                    const bwd = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = rhs.id, .rhs = lhs.id } });
                    const id = try self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = fwd, .rhs = bwd } });
                    return .{ .id = id, .sort = .prop };
                },
                .equal, .not_equal => {
                    const lhs = try self.elaborateExpr(b.lhs);
                    const rhs = try self.elaborateExpr(b.rhs);
                    if (lhs.sort == .prop) {
                        return self.fail(exprLoc(b.lhs), "'=' compares terms, not propositions", .{});
                    }
                    if (rhs.sort != lhs.sort) {
                        return self.fail(exprLoc(b.rhs), "expected sort '{s}', got '{s}'", .{
                            self.sortName(lhs.sort), self.sortName(rhs.sort),
                        });
                    }
                    const eq = try self.pool.add(.{ .eq = .{ .lhs = lhs.id, .rhs = rhs.id } });
                    const id = if (b.op == .not_equal) try self.pool.add(.{ .not = eq }) else eq;
                    return .{ .id = id, .sort = .prop };
                },
            },
            .not => |n| {
                const inner = try self.requireProp(try self.elaborateExpr(n.operand), n.operand);
                const id = try self.pool.add(.{ .not = inner.id });
                return .{ .id = id, .sort = .prop };
            },
            .quant => |q| {
                // binders become fresh fvars so every intermediate term stays
                // locally closed (capture-proof schema substitution depends on
                // this); the fvars are closed into de Bruijn form right here.
                // The binder sort may be a PREDICATED sort `H = G where inH`: the
                // KERNEL sort is its carrier (`G`), and its qualifiers become guards
                // injected into the body — `∀h; inH(h) -> …`, `∃h; inH(h) and …`.
                const refined = try self.resolveBinderSort(q.binders[0]);
                const sort = self.env.carrierOf(refined);
                const quals = try self.sortQualifiers(refined);
                const fresh = try self.arena.alloc(StrId, q.binders.len);
                for (q.binders, fresh) |b, *fr| {
                    const bname = try self.internTok(b.name);
                    try self.checkNoShadow(bname, b.name);
                    fr.* = try self.freshName();
                    try self.scope.append(self.arena, .{
                        .name = bname,
                        .sort = sort,
                        .fvar = fr.*,
                    });
                }
                const tcc_start = self.pending_tccs.items.len;
                const rf_start = self.result_facts.items.len;
                const body = try self.requireProp(try self.elaborateExpr(q.body), q.body);
                // close innermost binder first
                var id = body.id;
                var i = q.binders.len;
                while (i > 0) {
                    i -= 1;
                    // inject each qualifier guard on the binder's FVAR (before closing),
                    // then close guard+body together. Building the guard on an fvar
                    // (not a raw bvar 0) is what lets qualifierApp splice a define'd
                    // guard's body — whose OWN inner binders would recapture a bvar —
                    // capture-free, since substFvar handles fvar substitution correctly.
                    for (quals) |qpred| {
                        const bfv = try self.pool.add(.{ .fvar = .{ .name = fresh[i], .sort = sort } });
                        const guard_app = try self.qualifierApp(qpred, bfv);
                        const connective: term.BinOp = if (q.q == .forall) .implies else .and_op;
                        id = try self.pool.add(.{ .bin = .{ .op = connective, .lhs = guard_app, .rhs = id } });
                    }
                    id = try self.pool.close(id, fresh[i]);
                    id = try self.pool.add(.{ .quant = .{
                        .q = if (q.q == .forall) .forall else .exists,
                        .sort = sort,
                        .hint = try self.internTok(q.binders[i].name),
                        .body = id,
                    } });
                    // obligations under a binder are universally closed over it.
                    // For a PREDICATED binder, the guard `inH(h)` is an available
                    // hypothesis, so the obligation is `∀h; inH(h) -> <tcc>` (guard as
                    // antecedent) — matching how the body receives the guard.
                    for (self.pending_tccs.items[tcc_start..]) |*t| {
                        var f = t.formula;
                        for (quals) |qpred| {
                            const bound = try self.pool.add(.{ .fvar = .{ .name = fresh[i], .sort = sort } });
                            const guard_app = try self.qualifierApp(qpred, bound);
                            f = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = guard_app, .rhs = f } });
                        }
                        const closed = try self.pool.close(f, fresh[i]);
                        t.formula = try self.pool.add(.{ .quant = .{
                            .q = .forall,
                            .sort = sort,
                            .hint = try self.internTok(q.binders[i].name),
                            .body = closed,
                        } });
                    }
                    // surfaced result-facts under a predicated binder are closed the
                    // SAME way (`∀h; inH(h) -> <fact>`), so they α-match the
                    // identically-shaped obligations after the binder closes them.
                    for (self.result_facts.items[rf_start..]) |*rf| {
                        var f = rf.*;
                        for (quals) |qpred| {
                            const bound = try self.pool.add(.{ .fvar = .{ .name = fresh[i], .sort = sort } });
                            const guard_app = try self.qualifierApp(qpred, bound);
                            f = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = guard_app, .rhs = f } });
                        }
                        const closed = try self.pool.close(f, fresh[i]);
                        rf.* = try self.pool.add(.{ .quant = .{
                            .q = .forall,
                            .sort = sort,
                            .hint = try self.internTok(q.binders[i].name),
                            .body = closed,
                        } });
                    }
                    _ = self.scope.pop();
                }
                return .{ .id = id, .sort = .prop };
            },
            .lambda => |l| {
                return self.fail(l.tok.start, "lambda literals are only valid as schema arguments", .{});
            },
        }
    }

    fn elaborateName(self: *Elaborator, tok: lexer.Token) ElabError!Typed {
        // qualified names bypass locals entirely (locals are never qualified)
        if (std.mem.indexOfScalar(u8, self.text(tok), '.') != null) {
            const target = try self.resolveTarget(tok);
            return self.elaborateSymRef(tok, target);
        }
        const name = try self.internTok(tok);
        // scope lookup, innermost first (locals shadow schema params)
        var i = self.scope.items.len;
        while (i > 0) {
            i -= 1;
            const entry = self.scope.items[i];
            if (entry.name == name) {
                const id = try self.pool.add(.{ .fvar = .{ .name = entry.fvar, .sort = entry.sort } });
                return .{ .id = id, .sort = entry.sort };
            }
        }
        // schema parameter (only while elaborating a schema body/proof)
        if (self.schema_args) |sa| {
            if (sa.get(name)) |arg| switch (arg) {
                .value => |v| return v,
                .lambda => return self.fail(tok.start, "schema parameter '{s}' requires an argument", .{self.text(tok)}),
            };
        }
        return self.elaborateSymRef(tok, .{ .file = self.file, .base = name });
    }

    /// 0-ary symbol reference (possibly namespace-qualified)
    fn elaborateSymRef(self: *Elaborator, tok: lexer.Token, target: Target) ElabError!Typed {
        if (self.env.findSym(target.file, target.base)) |sym_id| {
            const sym = self.env.sym(sym_id);
            if (sym.arg_sorts.len != 0) {
                return self.fail(tok.start, "'{s}' expects {d} argument(s), got 0", .{ self.text(tok), sym.arg_sorts.len });
            }
            // a define is transparent: every use IS its term
            if (sym.definition) |def| {
                return .{ .id = def, .sort = sym.result };
            }
            const id = try self.pool.addApp(if (sym.kind == .pred) .pred else .app, sym_id, &.{});
            // a predicated-result CONST (`const E: H`) surfaces `inH(E)` — asserting
            // E ∈ H by its signature, so `f(E)` (f needs an H arg) composes.
            try self.surfaceResultFact(sym, id);
            return .{ .id = id, .sort = sym.result };
        }
        return self.fail(tok.start, "unknown identifier '{s}'", .{self.text(tok)});
    }

    /// If `sym`'s result sort is PREDICATED (`… : H`), surface `inH(sym(args))` as
    /// an available fact — the signature asserts the result is in H. Shared by
    /// 0-ary references (const) and applications (func).
    fn surfaceResultFact(self: *Elaborator, sym: Symbol, term_id: TermId) ElabError!void {
        if (sym.result_refined == sym.result) return;
        for (try self.sortQualifiers(sym.result_refined)) |qpred| {
            const fact = try self.qualifierApp(qpred, term_id);
            try self.result_facts.append(self.arena, fact);
        }
    }

    fn elaborateCall(self: *Elaborator, c: ast.Expr.Call) ElabError!Typed {
        const target = try self.resolveTarget(c.callee);
        const name = target.base;
        // schema parameter application: beta-reduce at the term level
        // (schema params are never qualified, but a stray hit is harmless:
        // qualified callee text never equals a bare param name)
        if (self.schema_args) |sa| {
            if (sa.get(name)) |arg| switch (arg) {
                .lambda => |l| {
                    if (c.args.len != l.arg_sorts.len) {
                        return self.fail(c.callee.start, "schema parameter '{s}' expects {d} argument(s), got {d}", .{ self.text(c.callee), l.arg_sorts.len, c.args.len });
                    }
                    // beta-reduce: substitute each parameter fvar with its argument.
                    // Simultaneous by construction — the argument terms are closed and
                    // the param fvars are fresh/distinct, so order is irrelevant.
                    var reduced = l.body;
                    for (c.args, l.arg_sorts, l.params) |arg_expr, expected, param| {
                        const t = try self.elaborateExpr(arg_expr);
                        if (t.sort != expected) {
                            return self.fail(exprLoc(arg_expr), "expected sort '{s}', got '{s}'", .{
                                self.sortName(expected), self.sortName(t.sort),
                            });
                        }
                        reduced = try self.pool.substFvar(reduced, param, t.id);
                    }
                    return .{ .id = reduced, .sort = l.result_sort };
                },
                .value => return self.fail(c.callee.start, "schema parameter '{s}' takes no arguments", .{self.text(c.callee)}),
            };
        }
        const sym_id = self.env.findSym(target.file, name) orelse {
            return self.fail(c.callee.start, "unknown identifier '{s}'", .{self.text(c.callee)});
        };
        const sym = self.env.sym(sym_id);
        if (sym.arg_sorts.len != c.args.len) {
            return self.fail(c.callee.start, "'{s}' expects {d} argument(s), got {d}", .{
                self.text(c.callee), sym.arg_sorts.len, c.args.len,
            });
        }
        const arg_ids = try self.arena.alloc(TermId, c.args.len);
        for (c.args, sym.arg_sorts, arg_ids) |arg, expected, *out| {
            const typed = try self.elaborateExpr(arg);
            if (typed.sort != expected) {
                return self.fail(exprLoc(arg), "expected sort '{s}', got '{s}'", .{
                    self.sortName(expected), self.sortName(typed.sort),
                });
            }
            out.* = typed.id;
        }
        // guarded application: owe the guard at the actual arguments.
        // Emitted AFTER the args are elaborated, so inner obligations of
        // nested guarded applications precede outer ones.
        if (sym.guard) |guard| {
            // simultaneous substitution via fresh intermediates: a user
            // variable spelled like a later param must not be re-substituted
            var g = guard;
            const fresh = try self.arena.alloc(StrId, sym.param_names.len);
            for (sym.param_names, fresh) |pn, *fr| {
                fr.* = try self.freshName();
                // placeholder fvar; its sort is irrelevant (replaced below)
                const fv = try self.pool.add(.{ .fvar = .{ .name = fr.*, .sort = .prop } });
                g = try self.pool.substFvar(g, pn, fv);
            }
            for (fresh, arg_ids) |fr, actual| {
                g = try self.pool.substFvar(g, fr, actual);
            }
            try self.pending_tccs.append(self.arena, .{ .formula = g, .loc = c.callee.start });
        }
        // a `define` is a MACRO: expand the call to its stored body with each
        // actual substituted for the corresponding param fvar (like a schema-lambda
        // beta-reduction). The kernel never sees the define'd symbol.
        //
        // The substitution MUST be simultaneous: param fvars are named after their
        // source name, and an actual may itself be an fvar named after an OUTER
        // define/func param (defines nest — `outer(n,x) = inner(n,x)`). A naive
        // sequential subst would then CAPTURE: substituting `inner.d := fvar_n`
        // introduces `fvar_n`, which the later `inner.n := …` pass would wrongly
        // rewrite too. So substitute in two phases through FRESH temporaries that
        // cannot collide with any actual: params → temps, then temps → actuals.
        if (sym.definition) |body| {
            var expanded = body;
            const temps = try self.arena.alloc(StrId, sym.param_names.len);
            for (sym.param_names, temps) |pn, *t| {
                t.* = try self.freshName();
                const tv = try self.pool.add(.{ .fvar = .{ .name = t.*, .sort = .prop } });
                expanded = try self.pool.substFvar(expanded, pn, tv);
            }
            for (temps, arg_ids) |t, actual| {
                expanded = try self.pool.substFvar(expanded, t, actual);
            }
            return .{ .id = expanded, .sort = sym.result };
        }
        const id = try self.pool.addApp(if (sym.kind == .pred) .pred else .app, sym_id, arg_ids);
        // a predicated-result func (`op(...): H`) surfaces `inH(op(args))` — the same
        // mechanism as a predicated-result const, via the shared helper.
        try self.surfaceResultFact(sym, id);
        return .{ .id = id, .sort = sym.result };
    }
};

// --- tests ---

const testing = std.testing;
const parser_mod = @import("parser.zig");

pub const TestCtx = struct {
    arena_state: *std.heap.ArenaAllocator,
    interner: *InternPool,
    pool: *term.Pool,
    env: *Env,
    sink: *Diagnostics.Sink,
    file: ast.File,
    source: []const u8,

    pub fn run(gpa: Allocator, source: []const u8) !TestCtx {
        return runVerify(gpa, source, .{});
    }

    /// Like `run`, but with an explicit `Verify` mode (to exercise --fast /
    /// --faster / --reckless / --draft paths, which `run` (strict) cannot reach).
    pub fn runVerify(gpa: Allocator, source: []const u8, verify: Verify) !TestCtx {
        const arena_state = try gpa.create(std.heap.ArenaAllocator);
        arena_state.* = .init(gpa);
        const arena = arena_state.allocator();

        const interner = try arena.create(InternPool);
        interner.* = .init(arena);
        const pool = try arena.create(term.Pool);
        pool.* = .init(arena);
        const sink = try arena.create(Diagnostics.Sink);
        sink.* = .init(arena);
        const env = try arena.create(Env);
        env.* = try .init(arena, interner);
        const file_id = try env.newFile();

        var p: parser_mod.Parser = .init(arena, source, sink);
        const file = try p.parseFile();
        var elab: Elaborator = .init(arena, source, interner, pool, env, sink, file_id);
        elab.verify = verify;
        try elab.elaborateFile(file);
        return .{
            .arena_state = arena_state,
            .interner = interner,
            .pool = pool,
            .env = env,
            .sink = sink,
            .file = file,
            .source = source,
        };
    }

    pub fn deinit(self: *TestCtx, gpa: Allocator) void {
        self.arena_state.deinit();
        gpa.destroy(self.arena_state);
    }

    pub fn firstMessage(self: *const TestCtx) []const u8 {
        return self.sink.list.items[0].message;
    }
};

test "well-sorted declarations elaborate cleanly" {
    const source =
        \\sort Nat
        \\const ZERO: Nat
        \\func succ(n: Nat): Nat
        \\func div(a: Nat, b: Nat): Nat requires b != ZERO
        \\pred even(n: Nat)
        \\axiom evenZero: even(ZERO)
        \\axiom addForm: forall a, b: Nat; exists c: Nat; succ(a) = c
        \\axiom induction(prop: Nat -> Prop):
        \\  prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)
    ;
    var ctx = try TestCtx.run(testing.allocator, source);
    defer ctx.deinit(testing.allocator);
    try testing.expectEqual(0, ctx.sink.list.items.len);

    // div stored its guard: not (eq (fvar b) ZERO)
    const div = ctx.env.sym(ctx.env.findSym(@enumFromInt(0), try ctx.interner.internString("div")).?);
    const guard = ctx.pool.get(div.guard.?);
    try testing.expect(guard == .not);
    // schema stored lazily as a form
    const ind = ctx.env.findStatement(@enumFromInt(0), try ctx.interner.internString("induction")).?;
    try testing.expect(ind.* == .schema);
}

test "define expansion is capture-avoiding across nested defines" {
    // outer(n, x) = inner(n, x), inner(d, n) = mul(d, n). The inner formal `n`
    // collides with outer's argument `n`; a naive sequential subst captures →
    // mul(x, x). Simultaneous (through fresh temps) keeps it mul(n, x), so the
    // reflexivity proof of `outer(n, x) = mul(n, x)` checks with no diagnostics.
    const source =
        \\sort T
        \\func mul(a: T, b: T): T
        \\define inner(d: T, n: T) = mul(d, n)
        \\define outer(n: T, x: T) = inner(n, x)
        \\theorem outerIsMul: forall n, x: T; outer(n, x) = mul(n, x)
        \\proof
        \\  @generalize-n |
        \\    fix n: T {
        \\      @generalize-x |
        \\        fix x: T {
        \\          @body | outer(n, x) = mul(n, x) [by reflexivity]
        \\        }
        \\      @discharge-x | forall x: T; outer(n, x) = mul(n, x) [by forall_intro generalize-x]
        \\    }
        \\  @conclusion | forall n, x: T; outer(n, x) = mul(n, x) [by forall_intro generalize-n]
        \\qed
    ;
    var ctx = try TestCtx.run(testing.allocator, source);
    defer ctx.deinit(testing.allocator);
    if (ctx.sink.list.items.len != 0) std.debug.print("unexpected diagnostic: {s}\n", .{ctx.firstMessage()});
    try testing.expectEqual(0, ctx.sink.list.items.len);
}

test "use-all-facts: schema instantiate does not clobber outer accelerant roots (--fast)" {
    // Under --fast (certify_arithmetic = false) an accelerant emits no kernel
    // citation edge, so the dead-step walk relies on `extra_reachable_steps` to
    // see an accelerant premise's use. A later schema `instantiate` step re-enters
    // checkProofSteps (recheck_schemas) and MUST NOT reset that per-proof
    // accumulator, or `@premise` below is falsely reported "unused fact".
    const source =
        \\sort Nat
        \\const Z: Nat
        \\func s(n: Nat): Nat
        \\func add(a: Nat, b: Nat): Nat
        \\axiom addZ: forall b: Nat; add(Z, b) = b
        \\axiom addS: forall a, b: Nat; add(s(a), b) = s(add(a, b))
        \\theorem sch(x: Nat): add(Z, x) = x
        \\proof
        \\  @c | add(Z, x) = x [by simplify addZ]
        \\qed
        \\theorem t: (add(s(Z), Z) = s(Z)) and (add(Z, Z) = Z)
        \\proof
        \\  @premise | add(Z, Z) = Z [by simplify addZ]
        \\  @use | add(s(Z), Z) = s(Z) [by simplify addS premise]
        \\  @via | add(Z, Z) = Z [by instantiate sch(Z)]
        \\  @conclusion | (add(s(Z), Z) = s(Z)) and (add(Z, Z) = Z) [by and_intro use via]
        \\qed
    ;
    var ctx = try TestCtx.runVerify(testing.allocator, source, .{ .certify_arithmetic = false });
    defer ctx.deinit(testing.allocator);
    if (ctx.sink.list.items.len != 0) std.debug.print("unexpected diagnostic: {s}\n", .{ctx.firstMessage()});
    try testing.expectEqual(0, ctx.sink.list.items.len);
}

test "sort errors are precise" {
    const cases = [_]struct { src: []const u8, msg: []const u8 }{
        .{ .src = "sort Nat\nfunc succ(n: Nat): Nat\npred p\naxiom bad: succ(p) = succ(p)", .msg = "expected sort 'Nat', got 'Prop'" },
        .{ .src = "sort Nat\nconst ZERO: Nat\naxiom bad: ZERO", .msg = "expected a proposition, got sort 'Nat'" },
        .{ .src = "sort Nat\naxiom bad: missing = missing", .msg = "unknown identifier 'missing'" },
        .{ .src = "sort Nat\nfunc succ(n: Nat): Nat\nconst ZERO: Nat\naxiom bad: succ(ZERO, ZERO) = ZERO", .msg = "'succ' expects 1 argument(s), got 2" },
        .{ .src = "pred p\npred q\naxiom bad: p = q", .msg = "'=' compares terms, not propositions" },
        .{ .src = "sort Nat\nsort Nat", .msg = "duplicate declaration of 'Nat'" },
        .{ .src = "const ZERO: natt", .msg = "unknown sort 'natt'" },
        .{ .src = "sort Nat\nfunc bad(n: Nat): Prop", .msg = "a func cannot return 'Prop'; declare a pred instead" },
        .{ .src = "sort Nat\naxiom bad: forall x: Nat; fun k: Nat => k = x", .msg = "lambda literals are only valid as schema arguments" },
        // guards must be guard-free (no obligation regress)
        .{ .src = "sort Nat\nconst ZERO: Nat\nfunc div(a: Nat, b: Nat): Nat requires b != ZERO\nfunc f(a: Nat): Nat requires div(a, a) = a", .msg = "a 'requires' clause may only mention total functions" },
        // disjunction contributes NO context to obligations (conservative):
        // the guard must hold outright even under p \/ ...
        .{ .src = "sort Nat\nconst ZERO: Nat\nfunc div(a: Nat, b: Nat): Nat requires b != ZERO\npred p\naxiom a1: p or div(ZERO, ZERO) = ZERO", .msg = "unproved obligation: 'ZERO != ZERO'" },
        // no-shadowing: nothing shadows anything
        .{ .src = "sort Nat\nconst ZERO: Nat\naxiom bad: forall ZERO: Nat; ZERO = ZERO", .msg = "'ZERO' shadows a declaration; choose a fresh name" },
        .{ .src = "sort Nat\naxiom bad: forall a: Nat; forall a: Nat; a = a", .msg = "'a' shadows a variable in scope; choose a fresh name" },
        .{ .src = "sort Nat\nfunc succ(n: Nat): Nat\nfunc bad(succ: Nat): Nat", .msg = "'succ' shadows a declaration; choose a fresh name" },
    };
    for (cases) |case| {
        var ctx = try TestCtx.run(testing.allocator, case.src);
        defer ctx.deinit(testing.allocator);
        try testing.expectEqual(1, ctx.sink.list.items.len);
        try testing.expectEqualStrings(case.msg, ctx.firstMessage());
    }
}

test "de Bruijn indices correct under nested binders" {
    const source =
        \\sort Nat
        \\const ZERO: Nat
        \\func add(a: Nat, b: Nat): Nat
        \\axiom nested: forall a: Nat; forall b: Nat; add(a, b) = add(b, a)
    ;
    var ctx = try TestCtx.run(testing.allocator, source);
    defer ctx.deinit(testing.allocator);
    try testing.expectEqual(0, ctx.sink.list.items.len);

    // nested: add(a, b) under two binders = app(bvar1, bvar0)
    const nested = ctx.env.findStatement(@enumFromInt(0), try ctx.interner.internString("nested")).?.axiom;
    const q1 = ctx.pool.get(nested.formula).quant;
    const q2 = ctx.pool.get(q1.body).quant;
    const neq = ctx.pool.get(q2.body).eq;
    const lhs_app = ctx.pool.get(neq.lhs).app;
    try testing.expectEqual(term.Node{ .bvar = 1 }, ctx.pool.get(ctx.pool.args(lhs_app)[0]));
    try testing.expectEqual(term.Node{ .bvar = 0 }, ctx.pool.get(ctx.pool.args(lhs_app)[1]));
}

// --- arithmetic equation-certifier (planEquation) regression harness ------
//
// The `[by arithmetic]` equation certifier normalizes both sides to a sorted
// tower of leaves and joins them. These tests pin the SHAPE CATEGORIES that
// occur across the whole std/aata corpus (captured by instrumenting
// planEquation), so a change to parseTower / sortTrace / cancelInverses can't
// silently regress them. Each theorem below certifies STRICT today (empty sink).

/// A ℤ-flavoured vocabulary + the exact rewrite lemmas the arithmetic certifier
/// pulls in (wk_term_rule_names + addIsCommutative/addLeftSwap), so `[by
/// arithmetic]` can build kernel certificates for equation goals.
const arith_prelude =
    \\sort Int
    \\const ZERO: Int
    \\const ONE: Int
    \\func succ(n: Int): Int
    \\func prev(n: Int): Int
    \\func add(a: Int, b: Int): Int
    \\func mul(a: Int, b: Int): Int
    \\func neg(a: Int): Int
    \\func sub(a: Int, b: Int): Int
    \\func f(x: Int): Int
    \\pred less_than(a: Int, b: Int)
    \\axiom definitionOfSubtraction: forall a, b: Int; sub(a, b) = add(a, neg(b))
    \\axiom addZeroLeft: forall b: Int; add(ZERO, b) = b
    \\axiom addZeroRight: forall n: Int; add(n, ZERO) = n
    \\axiom addSuccLeft: forall a, b: Int; add(succ(a), b) = succ(add(a, b))
    \\axiom addSuccRight: forall a, b: Int; add(a, succ(b)) = succ(add(a, b))
    \\axiom mulZeroLeft: forall b: Int; mul(ZERO, b) = ZERO
    \\axiom mulZeroRight: forall n: Int; mul(n, ZERO) = ZERO
    \\axiom mulSuccLeft: forall a, b: Int; mul(succ(a), b) = add(mul(a, b), b)
    \\axiom mulSuccRight: forall a, b: Int; mul(a, succ(b)) = add(mul(a, b), a)
    \\axiom oneIsSuccZero: ONE = succ(ZERO)
    \\axiom addIsAssociative: forall a, b, c: Int; add(add(a, b), c) = add(a, add(b, c))
    \\axiom addIsCommutative: forall a, b: Int; add(a, b) = add(b, a)
    \\axiom addLeftSwap: forall x, y, r: Int; add(x, add(y, r)) = add(y, add(x, r))
    \\axiom addNegRight: forall n: Int; add(n, neg(n)) = ZERO
    \\axiom addNegLeft: forall n: Int; add(neg(n), n) = ZERO
    \\axiom negNeg: forall n: Int; neg(neg(n)) = n
    \\axiom addPrevLeft: forall a, b: Int; add(prev(a), b) = prev(add(a, b))
    \\axiom addPrevRight: forall a, b: Int; add(a, prev(b)) = prev(add(a, b))
    \\axiom negZero: neg(ZERO) = ZERO
    \\axiom negSucc: forall n: Int; neg(succ(n)) = prev(neg(n))
    \\axiom negPrev: forall n: Int; neg(prev(n)) = succ(neg(n))
    \\axiom prevSucc: forall n: Int; prev(succ(n)) = n
    \\axiom succPrev: forall n: Int; succ(prev(n)) = n
    \\
;

fn expectCertifies(source: []const u8) !void {
    var ctx = try TestCtx.run(testing.allocator, source);
    defer ctx.deinit(testing.allocator);
    if (ctx.sink.list.items.len != 0) {
        std.debug.print("unexpected diagnostic: {s}\n", .{ctx.firstMessage()});
        return error.CertifierRegressed;
    }
}

test "arith certifier: reassociation and commutation of a plain add-sum" {
    // the dominant corpus shape: pure fvar sums reordered by assoc/comm/swap.
    try expectCertifies(arith_prelude ++
        \\theorem t: forall a, b, c: Int; add(add(a, b), c) = add(b, add(c, a))
        \\proof
        \\  @ga | fix a: Int { @gb | fix b: Int { @gc | fix c: Int {
        \\    @c | add(add(a, b), c) = add(b, add(c, a)) [by arithmetic]
        \\  } @dc | forall c: Int; add(add(a, b), c) = add(b, add(c, a)) [by forall_intro gc] }
        \\    @db | forall b, c: Int; add(add(a, b), c) = add(b, add(c, a)) [by forall_intro gb] }
        \\  @conclusion | forall a, b, c: Int; add(add(a, b), c) = add(b, add(c, a)) [by forall_intro ga]
        \\qed
    );
}

test "arith certifier: succ-tower + mul-by-constant fold" {
    // succ prefixes and mul(2, n) → n + n (a constant-coefficient product).
    try expectCertifies(arith_prelude ++
        \\theorem t: forall n: Int; mul(succ(succ(ZERO)), n) = add(n, n)
        \\proof
        \\  @gn | fix n: Int {
        \\    @c | mul(succ(succ(ZERO)), n) = add(n, n) [by arithmetic]
        \\  }
        \\  @conclusion | forall n: Int; mul(succ(succ(ZERO)), n) = add(n, n) [by forall_intro gn]
        \\qed
    );
}

test "arith certifier: sub fully cancels (sub(add(a,b),b) = a)" {
    // sub unfolds to add(·, neg ·); the neg leaf cancels its positive, leaving a.
    try expectCertifies(arith_prelude ++
        \\theorem t: forall a, b: Int; sub(add(a, b), b) = a
        \\proof
        \\  @ga | fix a: Int { @gb | fix b: Int {
        \\    @c | sub(add(a, b), b) = a [by arithmetic]
        \\  } @db | forall b: Int; sub(add(a, b), b) = a [by forall_intro gb] }
        \\  @conclusion | forall a, b: Int; sub(add(a, b), b) = a [by forall_intro ga]
        \\qed
    );
}

test "arith certifier: additive-inverse pair cancels across a separated leaf" {
    // add(a, sub(b, a)) → {a, b, neg(a)} reduces to {b}: the a/neg(a) pair must
    // cancel across the intervening b (cancelInverses).
    try expectCertifies(arith_prelude ++
        \\theorem t: forall a, b: Int; add(a, sub(b, a)) = b
        \\proof
        \\  @ga | fix a: Int { @gb | fix b: Int {
        \\    @c | add(a, sub(b, a)) = b [by arithmetic]
        \\  } @db | forall b: Int; add(a, sub(b, a)) = b [by forall_intro gb] }
        \\  @conclusion | forall a, b: Int; add(a, sub(b, a)) = b [by forall_intro ga]
        \\qed
    );
}

test "arith certifier: opaque compound leaf cancels (one opaque leaf)" {
    // an opaque compound subterm f(x) must ride the sorted-tower join as an atom.
    // add(f(x), sub(g, f(x))) → {f(x), g, neg(f(x))} reduces to {g}, cancelling
    // f(x) with neg(f(x)). g is a plain fvar so only ONE opaque leaf is involved.
    try expectCertifies(arith_prelude ++
        \\theorem t: forall x, g: Int; add(f(x), sub(g, f(x))) = g
        \\proof
        \\  @gx | fix x: Int { @gg | fix g: Int {
        \\    @c | add(f(x), sub(g, f(x))) = g [by arithmetic]
        \\  } @dg | forall g: Int; add(f(x), sub(g, f(x))) = g [by forall_intro gg] }
        \\  @conclusion | forall x, g: Int; add(f(x), sub(g, f(x))) = g [by forall_intro gx]
        \\qed
    );
}

test "arith certifier: TWO opaque leaves, one cancels (the gcd-step shape)" {
    // add(f(x), sub(h(y), f(x))) → {f(x), h(y), neg(f(x))} reduces to {h(y)}.
    // TWO opaque leaves (f(x), h(y)) — the gcd step's mul(b,q) + mod(a,b) shape.
    // The cancelled pair must be bubbled to the TAIL so add(·) is an innermost
    // subterm the addNeg lemma can rewrite.
    try expectCertifies(arith_prelude ++
        \\func h(x: Int): Int
        \\theorem t: forall x, y: Int; add(f(x), sub(h(y), f(x))) = h(y)
        \\proof
        \\  @gx | fix x: Int { @gy | fix y: Int {
        \\    @c | add(f(x), sub(h(y), f(x))) = h(y) [by arithmetic]
        \\  } @dy | forall y: Int; add(f(x), sub(h(y), f(x))) = h(y) [by forall_intro gy] }
        \\  @conclusion | forall x, y: Int; add(f(x), sub(h(y), f(x))) = h(y) [by forall_intro gx]
        \\qed
    );
}

test "arith certifier: numeral summand cancels (add(ONE, sub(b, ONE)) = b)" {
    // ONE = succ(ZERO) appears as an INNER summand of the sum, not the top-level
    // succ prefix. add(ONE, sub(b, ONE)) → {ONE, b, neg(ONE)} must reduce to {b}
    // by cancelling ONE with neg(ONE) — the tower parser folds the numeral summand
    // into the constant offset so the pair meets. Same shape as the separated-leaf
    // test but with a numeral in the fvar's place.
    try expectCertifies(arith_prelude ++
        \\theorem t: forall b: Int; add(ONE, sub(b, ONE)) = b
        \\proof
        \\  @gb | fix b: Int {
        \\    @c | add(ONE, sub(b, ONE)) = b [by arithmetic]
        \\  }
        \\  @conclusion | forall b: Int; add(ONE, sub(b, ONE)) = b [by forall_intro gb]
        \\qed
    );
}

test "arith certifier: net-nonzero numeral offset (add(ONE, n) = succ(n))" {
    // a numeral summand that does NOT cancel: add(ONE, n) = succ(n). ONE=succ(ZERO)
    // contributes +1 to the tower's (signed) constant offset; the RHS succ(n) is a
    // +1 prefix over {n}. Both sides normalize to offset +1 over {n}. Distinguishes
    // the signed-offset fold from a mere numeral-as-cancellable-leaf.
    try expectCertifies(arith_prelude ++
        \\theorem t: forall n: Int; add(ONE, n) = succ(n)
        \\proof
        \\  @gn | fix n: Int {
        \\    @c | add(ONE, n) = succ(n) [by arithmetic]
        \\  }
        \\  @conclusion | forall n: Int; add(ONE, n) = succ(n) [by forall_intro gn]
        \\qed
    );
}
