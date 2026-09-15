# A literate file in the directory

Its one theorem counts like any other.

```bpa
pred p
axiom pHolds: p

theorem pIsTrue: p
proof
  @conclusion |
    p
    [by cite pHolds]
qed
```
