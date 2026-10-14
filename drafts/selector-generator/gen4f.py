import itertools
# Generate the five pointwise lemmas + extensionality for
#   T(ar,a2) T(ar,a1) T(a1,a2) T(a1,a3)  =  T(a1,ar) T(a1,a3)      [ = (a1,a3,ar) ]
LHS="compose(compose(transposition(ar, a2), transposition(ar, a1)),\n  compose(transposition(a1, a2), transposition(a1, a3)))"
RHS="compose(transposition(a1, ar), transposition(a1, a3))"
PTS=["a1","a2","a3","ar"]
HY=[("a1 != a2","given-a1-not-a2","a1-not-a2"),("a1 != a3","given-a1-not-a3","a1-not-a3"),
    ("a1 != ar","given-a1-not-ar","a1-not-ar"),("a2 != a3","given-a2-not-a3","a2-not-a3"),
    ("a2 != ar","given-a2-not-ar","a2-not-ar"),("a3 != ar","given-a3-not-ar","a3-not-ar")]
HYP=" -> ".join(h[0] for h in HY)

def T(u,v): return lambda x: v if x==u else (u if x==v else x)
def comp(*fs):
    def g(x):
        for f in reversed(fs): x=f(x)
        return x
    return g

def trace(point, factors):
    """factors right-to-left; return list of (factorname, argin, argout)"""
    cur=point; out=[]
    for (u,v) in factors:
        nxt=T(u,v)(cur); out.append(((u,v),cur,nxt)); cur=nxt
    return out,cur

LFAC=[("a1","a3"),("a1","a2"),("ar","a1"),("ar","a2")]   # right to left
RFAC=[("a1","a3"),("a1","ar")]

def value_step(lbl, u,v, arg, res, flips):
    """emit the right transposition lemma for apply(T(u,v), arg) = res"""
    if arg==u:  return (lbl, f"apply(transposition({u}, {v}), {arg}) = {res}",
                        f"[using specialize permutation.transpositionAtFirst({u}, {v})]", [])
    if arg==v:  return (lbl, f"apply(transposition({u}, {v}), {arg}) = {res}",
                        f"[using specialize permutation.transpositionAtSecond({u}, {v})]", [])
    need=[(arg,u),(arg,v)]
    return (lbl, f"apply(transposition({u}, {v}), {arg}) = {res}",
            f"[using specialize permutation.transpositionElsewhere({u}, {v}, {arg}) "
            f"{arg}-not-{u} {arg}-not-{v}]", need)
