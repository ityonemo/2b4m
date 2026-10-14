import sys; sys.path.insert(0,'.')
from gen4f import *

LHSTXT=("compose(compose(transposition(ar, a2), transposition(ar, a1)),\n"
        "      compose(transposition(a1, a2), transposition(a1, a3)))")
RHSTXT="compose(transposition(a1, ar), transposition(a1, a3))"
SYM={}   # (a,b) -> label for a != b, derived by symmetry when needed

def emit_point(p, extra_var=None):
    """Return (text, thmname) for the pointwise lemma at p."""
    lt,lv=trace(p,LFAC); rt,rv=trace(p,RFAC)
    assert lv==rv
    pts = PTS + ([extra_var] if extra_var else [])
    hy = list(HY) + ([(f"{extra_var} != {v}", f"given-{extra_var}-not-{v}", f"{extra_var}-not-{v}")
                      for v in PTS] if extra_var else [])
    HYPl=" -> ".join(h[0] for h in hy)
    name = "fourFactorAgreesAt" + (p.capitalize() if p!=extra_var else "Elsewhere")
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
    emitted=set()
    def need_dis(a,b):
        """ensure a != b; returns its label"""
        lbl=f"{a}-not-{b}"
        if lbl in emitted: return lbl
        direct=[h for h in hy if h[0]==f"{a} != {b}"]
        if direct:
            w(ind,f"@{lbl} |"); w(ind+2,f"{a} != {b}"); w(ind+2,f"[by hypothesis {direct[0][1]}]")
            emitted.add(lbl); return lbl
        rev=[h for h in hy if h[0]==f"{b} != {a}"]
        assert rev, f"no source for {a} != {b}"
        src=need_dis(b,a)
        w(ind,f"@{lbl} |"); w(ind+2,f"{a} != {b}")
        w(ind+2,f"[using specialize alternating.disequalityIsSymmetric({b}, {a}) {src}]")
        emitted.add(lbl); return lbl
    refs=[]
    seen_vals=set()
    for side,tr in (("l",lt),("r",rt)):
        for n,((u,v),a,b) in enumerate(tr):
            if (u,v,a) in seen_vals: continue     # the same factor value already emitted
            seen_vals.add((u,v,a))
            lbl=f"{side}{n}-at-{a}"
            if a not in (u,v):
                need_dis(a,u); need_dis(a,v)
            tup=value_step(lbl,u,v,a,b,None)
            w(ind,f"@{lbl} |"); w(ind+2,tup[1]); w(ind+2,tup[2])
            refs.append(lbl)
    w(ind,"@conclusion-at-this-point |")
    w(ind+2,f"apply({LHSTXT}, {p})")
    w(ind+4,f"= apply({RHSTXT}, {p})")
    w(ind+2,f"[using simplify function.composeApply {' '.join(refs)}]")
    # tails
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
