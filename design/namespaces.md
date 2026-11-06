# Namespaces — the `{model, file}` pair

A namespace in 2b4m is **a file scoped by a model**. Not a file, not a model: the pair.

```zig
/// A namespace: a file scoped by a model. Two references to the same `(model, file)`
/// pair collapse to one `Index`.
namespace: Namespace,
```

Both halves are needed because the same declarations mean different things under different
interpretations. `std/group.b4m` read in the universe is the abstract group theory; read
under `ZnGroup` it is ℤ_n's group structure. One file, two namespaces — and a name resolved
in each lands on a different entity.

## Identity is by ORIGIN, not by path or alias

Two references to the same `(model, file)` collapse to one `Index`. The consequences are
worth stating because they are easy to get wrong:

- **Aliasing does not mint a new thing.** `sort Grp = group.Grp` binds a local name to the
  target's existing `Index`. There is no second sort, so the two names are
  interchangeable, transitively.
- **A file reached by two spellings is ONE namespace only if the path canonicalizes to
  one.** Importing a chapter by an absolute path and the same file by a relative path gives
  two different origins, and a sort from each is a *different* sort — producing the
  genuinely confusing `expected sort 'Fn', got 'Fn'`. Import everything the same way.
- **The universe is a model too** — the empty overlay, hence the identity. So an ordinary
  proof and a transferred proof take the same code path, with `model = .universe` in the
  ordinary case. There is no separate "unmodelled" mode to maintain.

## The two axes: `import` and `model`

They are orthogonal, and conflating them is the usual confusion.

| | `import` | `model` |
|---|---|---|
| what it is | a namespace VALUE bound to a name | a universe of discourse over a source theory |
| what it changes | where names are looked up | what the names MEAN |
| surface | `import g <<< "std/group.b4m"`, then `g.Grp` | `model M { … }`, then `[using model(M) g.thm]` |
| bulk open | never — references stay qualified | n/a |

`import` is Zig-like: it yields a value you qualify through, with no bulk open and no
transitive exposure (importing X does not give you X's imports as bare namespaces). `model`
is the interpretation axis — see `model-design.md`.

Re-export is a third thing again: `fact X = ns.y` is the keyword for making an imported
fact citable onward under a local name. An alias is a binding, not a copy.

## Why qualified names are never rewritten

A qualified name `ns.name` belongs to the SOURCE theory, so any mechanical rename over the
corpus must leave it alone — the same class of hazard as a model block's left-hand keys,
which are source-theory names too. A regex that rewrites bare tokens will silently corrupt
both if it is not taught to skip them.

## See also

- `model-design.md` — the interpretation axis in full.
- `lazy-eval.md` — how import resolution interacts with demand-driven checking.
