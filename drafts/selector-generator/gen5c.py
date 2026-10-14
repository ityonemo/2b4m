import itertools
def T(u,v): return lambda x: v if x==u else (u if x==v else x)
def comp(*fs):
    def g(x):
        for f in reversed(fs): x=f(x)
        return x
    return g
# Case 2's identity.  LHS factors outermost-first; applied right to left.
LFAC=[("a3","a6"),("a3","a1"),("a1","a2"),("a1","a4")]
RFAC=[("a1","a3"),("a1","a6"),("a1","a2"),("a1","a4")]
PTS=["a1","a2","a3","a4","a6"]
# ONLY these two disequalities are needed (verified over 2000 assignments)
# all five points distinct: Judson's case 2 has sigma = tau (a1a2a3)(a4a5a6) with
# the two 3-cycles DISJOINT, so a1,a2,a3,a4,a6 are distinct by construction.
HY=[("a1 != a2","given-a1-not-a2","a1-not-a2"),("a1 != a3","given-a1-not-a3","a1-not-a3"),("a1 != a4","given-a1-not-a4","a1-not-a4"),("a1 != a6","given-a1-not-a6","a1-not-a6"),("a2 != a3","given-a2-not-a3","a2-not-a3"),("a2 != a4","given-a2-not-a4","a2-not-a4"),("a2 != a6","given-a2-not-a6","a2-not-a6"),("a3 != a4","given-a3-not-a4","a3-not-a4"),("a3 != a6","given-a3-not-a6","a3-not-a6"),("a4 != a6","given-a4-not-a6","a4-not-a6")]

def tr(point, factors):
    cur=point; out=[]
    for (u,v) in reversed(factors):
        nxt=T(u,v)(cur); out.append(((u,v),cur,nxt)); cur=nxt
    return out,cur
