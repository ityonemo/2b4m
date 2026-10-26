# `--fast` accepts false statements: three probes

Repros for the `--fast` trust boundary (catalogued in `ACCELERATION.md`). Each passes `--fast` and fails
strict, which violates the both-ways agreement the `--fast` contract claims.

| file | `--fast` | strict |
|---|---|---|
| `arithmetic-false-accepted.b4m` | `OK: 1 theorems proven` | `arithmetic: the statement is false` |
| `simplify-false-accepted.b4m` | `OK: 1 theorems proven` | rejected |
| `model-partial-accepted.b4m` | `OK: 3 theorems proven` | `PartialNames@isomorphismIsAnEquivalence: step claims …` |

The first two assert plain falsehoods (`1 = 2`, `0 + 1 = 2`). The third is subtler and is the
one that prompted the note: a model of `std/isomorphism.b4m` that maps the identity and
inverse obligations but NOT the composite one, then cites the equivalence theorem — whose
proof needs the composite. Strict refuses; `--fast` reports an equivalence relation whose
transitivity nothing supplied.

Run each both ways to confirm before changing any producer's admit branch.
