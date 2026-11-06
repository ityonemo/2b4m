# Decoding `Schema{<hash>}` back into meaningful information

**Status: DESIGNED, not built** (`2b4m query` has no `instance` subcommand). A slow linear
search is acceptable — the error path does not need to be fast.

## What a reader sees today

A schema instance is named by hashing its arguments
(`Schema.instanceHash`, `Prove.zig` ~2409), so `--trace-facts` prints

```
[prove] task#11 = aSchema{635ffcad5c91c77c} in ns#68 (model#0)
```

`635ffcad5c91c77c` says *which* instance only in the sense that two identical instantiations
collide and two different ones (almost surely) do not.

The hash is **reproducible** — it hashes `(name bytes, loc)`, not allocation-ordered
`Index`es — which is the precondition for decoding it at all.

## The preimage is retained, just not addressable from the name

`ProveTask.instance` carries `(schema_name, params, args)` — the exact preimage, reified
durably right after the naming site (`Prove.zig` ~2431). The gap is that it lives on the
**in-flight task** and nothing maps `inst_name -> that payload`. After the run the
association is gone, though the args themselves are still durable in the pool.

## What to build: re-derivation, not a side table

Store nothing. On demand, enumerate candidate instantiations, recompute `instanceHash` for
each, and report the matches. Candidates are fully enumerable after a run: `Context.ast_index`
is a by-name registry of every named decl in every parsed file, synthetic
accelerant-generated schemas included, and each `[using instantiation S(args…)]` step names
its schema and argument expressions syntactically.

Cost is a scan over citation sites per query — no new data structure, no bookkeeping to keep
in sync. It also degrades honestly: no match means "no instantiation in this run hashes to
that", which is itself information (a stale hash, or a different model).

*(A reverse side table on `Context` was the alternative, and is rejected as the primary
route: it adds a side table where there is already a documented lock-discipline hazard
(`[[side-table-lock-discipline]]`), for a path allowed to be slow. Worth revisiting only if
re-derivation cannot reconstruct something — the candidate being an instance minted under a
model transfer, where `args_source` differs from `args`.)*

1. **`2b4m query instance <file> <hash>`** — or accept the full `Schema{hash}` spelling.
   Prints the schema's name and declaration site, each parameter bound to its argument
   (rendered via the same `renderTerm` diagnostics use), the citing proof and step, and the
   model if not `.universe`.
2. **Make `--trace-facts` self-describing** — a one-line expansion on first appearance
   removes most of the need to decode anything by hand.
3. **A test** instantiating one schema twice at different arguments, decoding both, and
   asserting the recovered arguments match what was written — plus one asserting a hash from
   a *different* argument set does not resolve.

## Watch out for

- **Model transfers.** The payload keeps BOTH `args` and `args_source`; the hash is over
  `args`. A decoder reporting only one would mislead on a transferred instance.
- **`freeFvarParams`.** Under a model, `pnames` is EXTENDED beyond the schema's declared
  params (`Prove.zig` ~2397) by the args' free variables of refined image sort. Any
  re-derivation must reproduce that extension or it hashes the wrong parameter list.
- **Reserved slots.** `hashEntity` (`Schema.zig:91`) treats non-named Items (`Index.none`,
  `SortId.prop`) as fixed values rather than resolving a name. Mirror that; do not assume
  every entity has a name.
- **`termHash` has the same shape** and names synthetic accelerant schemas, so whatever
  decodes one should decode the other. It is called at THREE sites (`Prove.zig` ~3484,
  ~3925, ~4650), and the first mixes in an arg count and a head-local flavour on top of the
  term hash — reproduce that or it will not match. (The flavour is load-bearing: omitting it
  caused a keep-first collision, see `[[schema-instance-crosstalk]]`.)
