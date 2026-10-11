# Decoding `Schema{<hash>}` back into meaningful information

**Status: DESIGNED, not built.** User direction 2026-10-11: being able to reverse a hash into
meaningful, deterministic information is wanted; it need not be solved immediately, and a slow
linear search is acceptable because *the error path does not need to be fast*.

## What a reader sees today

A schema instance is named by hashing its arguments:

```zig
// Prove.zig ~2072
const hash = Schema.instanceHash(interner, pool, schema_name, pnames, args);
const inst_name_bytes = try std.fmt.allocPrint(arena, "{s}{{{x}}}", .{ schema_name_bytes, hash });
```

so `--trace-facts` prints lines like

```
[prove] task#11 = aSchema{635ffcad5c91c77c} in ns#68 (model#0)
```

`635ffcad5c91c77c` is opaque. It says *which* instance only in the sense that two identical
instantiations collide and two different ones (almost surely) do not.

**Reproducibility is a precondition, and it now holds.** Before `cc800fe` the hash folded
InternPool `Index`es and `StrId`s, both allocation-ordered, so the same instantiation hashed
differently run to run — four distinct values in five runs. It now hashes `(name bytes, loc)`,
so the same source yields the same hash every time. Decoding an unstable hash would have been
meaningless.

## The preimage is already retained — it is just not addressable from the name

Everything the hash is computed from is still live at the naming site and is **reified durably**
immediately after:

```zig
// Prove.zig ~2094
const durable = try self.reifyArgs(pnames, args);
_ = try self.h.rackIndexed(try ProveTask.new(arena, .{
    .name = inst_name,
    .instance = .{ .schema_name = rs.name, .params = pnames, .args = durable, … },
}));
```

So `ProveTask.instance` carries `(schema_name, params, args)` — the exact preimage. The gap is
that this lives on the **in-flight task** and nothing maps `inst_name -> that payload`. After
the run the association is gone, even though the args themselves are durable in the pool.

## Two routes, and why the cheap one is right

### A. Re-derivation (recommended)

Do not store anything. On demand, enumerate candidate instantiations, recompute
`instanceHash` for each, and report the ones that match. Candidates come from the AST, which is
fully enumerable after a run:

- `Context.ast_index` is a by-name registry of every named decl in every parsed file, including
  synthetic (accelerant-generated) schemas — so every schema is reachable.
- Each `[using instantiation S(args…)]` step in a proof names its schema and its argument
  expressions syntactically. Walking proofs for instantiation steps yields the candidate set
  directly, without needing to enumerate minted instances.

Cost is a scan over citation sites per query. That is exactly the tradeoff the user approved:
**no new data structure, no bookkeeping to keep in sync, and slow is fine on an error path.**

It also degrades honestly: if nothing matches, the answer is "no instantiation in this run
hashes to that", which is itself information (a stale hash, or a different model).

### B. A reverse side table

`Context` gains `instance_preimage: AutoHashMapUnmanaged(InternPool.Index, Preimage)`, written
at the naming site.

Rejected as the primary route. It adds a side table to a Context that already has a documented
lock-discipline hazard around exactly these (`[[side-table-lock-discipline]]`: four unguarded
reads during proving, one of which segfaulted), for a path that is allowed to be slow. Worth
revisiting only if re-derivation proves unable to reconstruct something — the obvious candidate
being an instance minted under a model transfer, where `args_source` differs from `args`.

## What to build

1. **`2b4m query instance <file> <hash>`** — or accept the full `Schema{hash}` spelling. Prints
   the schema's name and declaration site, each parameter bound to its argument (rendered as
   surface syntax, via the same `renderTerm` diagnostics use), the citing proof and step, and
   the model if not `.universe`.
2. **Make `--trace-facts` self-describing.** The hash's job in a trace is identity, which it
   does well; a one-line expansion on first appearance would remove most of the need to decode
   anything by hand.
3. **A test** that instantiates one schema twice at different arguments, decodes both hashes,
   and asserts the recovered arguments match what was written — plus one that a hash from a
   *different* argument set does not resolve.

## Watch out for

- **Model transfers.** The payload keeps BOTH `args` and `args_source`; the hash is over
  `args`. A decoder reporting only one of them would mislead on a transferred instance.
- **`freeFvarParams`.** Under a model, `pnames` is EXTENDED beyond the schema's declared
  params (Prove.zig ~2064) by the args' free variables of refined image sort. Any re-derivation
  must reproduce that extension or it will hash the wrong parameter list.
- **Reserved slots.** `hashEntity` treats non-named Items (`Index.none`, `SortId.prop`) as
  fixed values rather than resolving a name. A decoder must mirror that, not assume every
  entity has a name.
- **`termHash` has the same shape** and names synthetic accelerant schemas. Whatever decodes
  one should decode the other; the two sites are `Prove.zig` ~2073 and ~2570.
