# Convolution reindexing — the spike that found the proof shape

These two files are the scratch work behind `std/ring/polynomial.b4m`'s reindexing lemmas.
They are kept because the DEAD ENDS are the useful part: three plausible induction shapes
fail, and the failures are not obvious until measured.

| route | why it fails |
|---|---|
| induction on `i` of `conv(p,q,i,i) = conv(q,p,i,i)` | every term's q-index is `i - j`, so the whole index set SHIFTS; the hypothesis at `i` says nothing about `i + 1` |
| induction on `k` of `conv(p,q,i,k) = conv(q,p,i,k)` | that equation is FALSE for every `k < i` — the partial sums genuinely differ until the range closes |
| a one-bound "reversed accumulation" sum | reversal of accumulation ORDER is just commutativity, and does NOT reach the reindexed TERMS (`segment.b4m` proves it and the `--axioms` report shows the prepend lemma unused) |

What works carries a **second bound**: `segment(p,q,i,m,n)`, the `n+1` terms from index `m`.
It can be grown at the top (its definition) and peeled at the base (`segmentPeelsAtTheBase`,
derived — positing it would beg the question), and those two directions are what let a sum
accumulated from one end be re-read from the other.

`segment.b4m` is the abstract-term version; `reindex.b4m` is the shifted-base version. Both
were proved before touching the committed theory, so the real file got the shape that works
rather than the first one tried.
