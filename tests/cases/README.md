# `tests/cases` — integration fixtures, grouped by what they test

Each file is a small `.b4m` (or literate `.md`) that the gates in `tests/*.zig` run
through the real CLI. A `_bad` suffix means the fixture is expected to FAIL, and its
diagnostic is pinned byte-for-byte in the gate — so a fixture and its expected error
are one unit.

| directory | what lives here |
|---|---|
| `kernel/` | the kernel inference rules — `modus_ponens`, `iff*`, `rewrite*`, `symmetry`, `forall_*`, `case_*`, induction |
| `tactics/<word>/` | one directory per accelerated tactic: `arithmetic`, `polynomial`, `simplify`, `assoc`, `ac`, `specialize`, `tautology`, `extensionality`, `chain`, `farkas`, `cooper`, `smt` |
| `model/` | the `model` mechanism. Subdirs for the big families: `guarded/` (relativization), `definition/` (definitional discharge), `schema/` (schema transfer), `accel/` (an accelerant under a model), `alias/` (borrowed namespaces) |
| `schema/` | theorem/axiom schemas — instantiation, wellformedness, lambda args, `instance_crosstalk/` |
| `sorts/` | sorts, predicated/refined sorts, guard (TCC) obligations, `div_*` |
| `define/` | the `define` and `definition` keywords |
| `namespaces/` | `import`, `fact`, alias, `forward`, `hole` — plus `imports/` for multi-file import graphs |
| `fast/` | the `--fast` trust boundary. A `*_false_fast` fixture asserts `--fast` still REFUSES a false goal |
| `syntax/` | parse and proof-structure errors — shadowing, labels, missing conclusion, lint |
| `cli/` | the command surface: `query`, `--axioms`, `--trace-facts`, smoke, and `directory-mode/` |

## Two rules for adding or moving a fixture

**1. A fixture that imports a sibling must live in the same directory as it.** Import
paths inside a fixture are written relative to the importing file (`import src <<<
"model_source.b4m"`), so a cluster — `model_guarded.b4m` and
`model_guarded_source.b4m`, say — moves together or not at all. Imports of the real
library are spelled from the repo root (`"std/peano/order.b4m"`), never with `../`, so
they survive any nesting.

**2. Wire it to a gate.** A fixture nothing references is not a test. Four
`refined_discharge_*` fixtures sat here unreferenced from `8bd72be` until the
2026-11-06 reorganization surfaced them — including a soundness negative. To check:

    rg -q "$(basename FILE)" tests/*.zig

## `cli/directory-mode/`

These are directories because *being a directory is the fixture* — they exercise
`check <dir>` (recursive discovery, `.md` alongside `.b4m`, a subdirectory),
`--library`, and `query search <dir>`:

- `ok/` — a healthy tree: two `.b4m`, a literate `.md`, a non-2b4m `.md`, and `sub/`
- `broken/` — one good file and one that must fail, so the sweep reports the failure
- `unused-axiom/` — passes plain `check`, fails `--library` on an axiom no theorem uses

Do not flatten them, and keep the file counts in mind: `cli/directory-mode/ok`'s
declaration and theorem totals are pinned in `tests/test_cli.zig`.
