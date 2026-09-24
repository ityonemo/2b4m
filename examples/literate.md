# A literate proof

`bpa check` runs on Markdown: it checks the proofs inside ` ```bpa ` fenced
blocks and ignores everything else. This document *is* a checkable bpa file —
the prose you're reading is masked out, the code blocks concatenate into one
proof in order, and a later block can cite an earlier one.

## Setting up the vocabulary

We work over a tiny theory: a sort with a binary operation `op` and two
axioms — `op` is commutative, and it has a right identity `E`.

```bpa
sort T
const E: T
func op(a: T, b: T) => T

axiom opComm: forall a, b: T; op(a, b) = op(b, a)
axiom opIdRight: forall a: T; op(a, E) = a
```

## The theorem

From those two axioms, `E` is *also* a left identity — `op(E, a) = a` — because
commuting turns the right identity into the left. Note the proof below cites
`opComm` and `opIdRight`, declared in the earlier block: the blocks share one
scope.

```bpa
theorem opIdLeft: forall a: T; op(E, a) = a
proof
  @generalize-a |
    fix a: T {
      @commute |
        op(E, a) = op(a, E)
        [using specialize opComm(E, a)]
      @a-op-e |
        op(a, E) = a
        [using specialize opIdRight(a)]
      @conclusion-inner |
        op(E, a) = a
        [by rewrite a-op-e commute]
    }
  @conclusion |
    forall a: T; op(E, a) = a
    [by forall_intro generalize-a]
qed
```

That's it — `bpa check examples/literate.md` verifies the proof above, and any
error would report a line number pointing straight into this `.md` file.
