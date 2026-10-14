import sys; sys.path.insert(0,'.')
from gen5c import *

LHSTXT=("compose(compose(transposition(a3, a6), transposition(a3, a1)),\n"
        "      compose(transposition(a1, a2), transposition(a1, a4)))")
RHSTXT=("compose(compose(transposition(a1, a3), transposition(a1, a6)),\n"
        "      compose(transposition(a1, a2), transposition(a1, a4)))")

def emit_point(p, extra=None):
    lt,lv=tr(p,LFAC); rt,rv=tr(p,RFAC)
    assert lv==rv, (p,lv,rv)
    pts=PTS+([extra] if extra else [])
    hy=list(HY)
    if extra:
        hy += [(f"{extra} != {v}", f"given-{extra}-not-{v}", f"{extra}-not-{v}") for v in PTS]
    HYPl=" -> ".join(h[0] for h in hy)
    name="fiveCycleAgreesAt"+(("Elsewhere") if extra else p.capitalize())
    L=[]
    def w(ind,t=""): L.append((" "*ind+t).rstrip()+"\n")
    w(0)
    w(0,f"theorem {name}: forall {', '.join(pts)}: Element;")
    w(2,f"{HYPl} ->")
    w(2,f"apply({LHSTXT}, {p})")
    w(4,f"= apply({RHSTXT}, {p})")
    w(0,"proof")
    ind=2
    for v in pts:
        w(ind,f"@generalize-{v} |"); w(ind+2,f"fix {v}: Element {{"); ind+=4
    for txt,blk,_ in hy:
        w(ind,f"@{blk} |"); w(ind+2,f"assume {txt} {{"); ind+=4
    emitted={}
    def need(a,b):
        lbl=f"{a}-not-{b}"
        if lbl in emitted: return lbl
        d=[h for h in hy if h[0]==f"{a} != {b}"]
        if d:
            w(ind,f"@{lbl} |"); w(ind+2,f"{a} != {b}"); w(ind+2,f"[by hypothesis {d[0][1]}]")
            emitted[lbl]=1; return lbl
        r=[h for h in hy if h[0]==f"{b} != {a}"]
        assert r, f"no source for {a} != {b} in {name}"
        src=need(b,a)
        w(ind,f"@{lbl} |"); w(ind+2,f"{a} != {b}")
        w(ind+2,f"[using specialize alternating.disequalityIsSymmetric({b}, {a}) {src}]")
        emitted[lbl]=1; return lbl
    refs=[]; seen=set()
    for side,trc in (("l",lt),("r",rt)):
        for n,((u,v),a,b) in enumerate(trc):
            if (u,v,a) in seen: continue
            seen.add((u,v,a))
            lbl=f"{side}{n}-at-{a}"
            if a==u:
                just=f"[using specialize transpositionAtFirst({u}, {v})]"
            elif a==v:
                just=f"[using specialize transpositionAtSecond({u}, {v})]"
            else:
                need(a,u); need(a,v)
                just=f"[using specialize transpositionElsewhere({u}, {v}, {a}) {a}-not-{u} {a}-not-{v}]"
            w(ind,f"@{lbl} |"); w(ind+2,f"apply(transposition({u}, {v}), {a}) = {b}"); w(ind+2,just)
            refs.append(lbl)
    w(ind,"@conclusion-at-this-point |")
    w(ind+2,f"apply({LHSTXT}, {p})")
    w(ind+4,f"= apply({RHSTXT}, {p})")
    w(ind+2,f"[using simplify function.composeApply {' '.join(refs)}]")
    for k in range(len(hy)-1,-1,-1):
        ind-=4; w(ind,"}")
        w(ind,f"@{hy[k][1].replace('given-','')}-implies |")
        w(ind+2," -> ".join(h[0] for h in hy[k:])+" ->")
        w(ind+4,f"apply({LHSTXT}, {p})")
        w(ind+6,f"= apply({RHSTXT}, {p})")
        w(ind+2,f"[by discharge {hy[k][1]}]")
    for k in range(len(pts)-1,-1,-1):
        ind-=4; w(ind,"}")
        lbl="conclusion" if k==0 else f"discharge-{pts[k]}"
        w(ind,f"@{lbl} |")
        w(ind+2,f"forall {', '.join(pts[k:])}: Element; {HYPl} ->")
        w(ind+4,f"apply({LHSTXT}, {p})")
        w(ind+6,f"= apply({RHSTXT}, {p})")
        w(ind+2,f"[by generalize generalize-{pts[k]}]")
    w(0,"qed")
    return "".join(L), name
