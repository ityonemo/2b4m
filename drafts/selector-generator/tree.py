import sys,re; sys.path.insert(0,'.')
import final
POS=final.POS; GOAL=final.GOAL
HYPS=[("i != j","given-i-not-j","i-is-not-j"),("x != y","given-x-not-y","x-is-not-y"),
      ("x != z","given-x-not-z","x-is-not-z"),("y != z","given-y-not-z","y-is-not-z")]
HYP=" -> ".join(h[0] for h in HYPS)
COORDS=[0,1,2,None]
def af(fp,c):
    return f"{POS[c]} = {fp}" if c is not None else " and ".join(f"{v} != {fp}" for v in "xyz")
def armlbl(fp,c): return f"when-{'no-'+fp if c is None else POS[c]+'-is-'+fp}"
L=[]
def w(ind,t=""): L.append((" "*ind+t).rstrip()+"\n")

def disj(fp):
    return " or ".join([f"{POS[c]} = {fp}" for c in [0,1,2]] +
                       ["(" + " and ".join(f"{v} != {fp}" for v in "xyz") + ")"])

def clash_arm(ind, c, fp_outer="i", fp_inner="j"):
    """both i and j claim coordinate c: derive i = j and discharge."""
    v=POS[c]
    w(ind,f"@{v}-is-i-clash |"); w(ind+2,f"{v} = i"); w(ind+2,f"[by hypothesis {armlbl('i',c)}]")
    w(ind,f"@{v}-is-j-clash |"); w(ind+2,f"{v} = j"); w(ind+2,f"[by hypothesis {armlbl('j',c)}]")
    w(ind,f"@i-is-{v}-clash |"); w(ind+2,f"i = {v}"); w(ind+2,f"[by symmetry {v}-is-i-clash]")
    w(ind,f"@i-equals-j-clash |"); w(ind+2,"i = j")
    w(ind+2,f"[by rewrite i-is-{v}-clash {v}-is-j-clash]")
    w(ind,f"@i-is-not-j-clash |"); w(ind+2,"i != j"); w(ind+2,"[by hypothesis given-i-not-j]")
    w(ind,f"@conclusion-clash-at-{v} |"); w(ind+2,GOAL)
    w(ind+2,"[by ex_falso i-equals-j-clash i-is-not-j-clash]")

def emit():
    w(0)
    w(0,"// The selector assembled: from the fixed family to every 3-cycle on distinct points.")
    w(0,"//")
    w(0,"// A 4 x 4 case tree on where the fixed pair sits — which coordinate of (x,y,z) equals i,")
    w(0,"// crossed with the same for j. Thirteen arms are real leaves, each closing by one shape")
    w(0,"// theorem proved above (the table is in CHAPTER10-PAINPOINTS, checked by script against")
    w(0,"// this file). The three same-coordinate arms close by deriving i = j and discharging.")
    w(0,"//")
    w(0,"// Nested rather than one flat 13-way split because the flat disjunction is NOT a")
    w(0,"// propositional tautology: it admits x = i and x = j both true, `tautology` seeing those")
    w(0,"// and i != j as unrelated atoms. Each level here is a genuine tautology over its own three.")
    w(0,"theorem everyThreeCycleIsInANormalSubgroupWithTheFamily(inN(Fn)):")
    w(2,"(forall g, h: Fn; inN(g) -> inN(h) -> inN(compose(g, h))) ->")
    w(2,"(forall i2, j2, k: Element; i2 != j2 -> k != i2 -> k != j2 ->")
    w(4,"inN(compose(transposition(i2, k), transposition(i2, j2)))) ->")
    w(2,"forall i, j, x, y, z: Element;")
    w(2,f"{HYP} ->")
    w(2,GOAL)
    w(0,"proof")
    w(2,"@given-closure |")
    w(4,"assume forall g, h: Fn; inN(g) -> inN(h) -> inN(compose(g, h)) {")
    w(6,"@closure |"); w(8,"forall g, h: Fn; inN(g) -> inN(h) -> inN(compose(g, h))")
    w(8,"[by hypothesis given-closure]")
    w(6,"@given-family |")
    w(8,"assume forall i2, j2, k: Element; i2 != j2 -> k != i2 -> k != j2 ->")
    w(10,"inN(compose(transposition(i2, k), transposition(i2, j2))) {")
    w(12,"@family |")
    w(14,"forall i2, j2, k: Element; i2 != j2 -> k != i2 -> k != j2 ->")
    w(16,"inN(compose(transposition(i2, k), transposition(i2, j2)))")
    w(14,"[by hypothesis given-family]")
    ind=12
    for v,blk in [("i","generalize-i"),("j","generalize-j"),("x","generalize-x"),
                  ("y","generalize-y"),("z","generalize-z")]:
        w(ind,f"@{blk} |"); w(ind+2,f"fix {v}: Element {{"); ind+=4
    for txt,blk,_ in HYPS:
        w(ind,f"@{blk} |"); w(ind+2,f"assume {txt} {{"); ind+=4
    # the four outer hypotheses, restated once for the whole tree
    for txt,blk,lbl in HYPS:
        w(ind,f"@{lbl} |"); w(ind+2,txt); w(ind+2,f"[by hypothesis {blk}]")
    w(ind,"@where-i-sits |"); w(ind+2,disj("i")); w(ind+2,"[using tautology]")
    w(ind,"@where-j-sits |"); w(ind+2,disj("j")); w(ind+2,"[using tautology]")
    w(ind,"@conclusion-by-position |"); w(ind+2,GOAL)
    w(ind+2,"case where-i-sits {")
    oi=ind+4
    for ci in COORDS:
        w(oi,f"@{armlbl('i',ci)} |"); w(oi+2,f"assume {af('i',ci)} {{")
        ii=oi+4
        w(ii,f"@inner-split-{'no-i' if ci is None else POS[ci]+'-is-i'} |"); w(ii+2,GOAL)
        w(ii+2,"case where-j-sits {")
        ji=ii+4
        for cj in COORDS:
            w(ji,f"@{armlbl('j',cj)} |"); w(ji+2,f"assume {af('j',cj)} {{")
            bi=ji+4
            if ci is not None and cj is not None and ci==cj:
                clash_arm(bi, ci)
            else:
                final.OUT=[]
                final.emit_leaf_body(bi, ci, cj)
                L.extend(final.OUT)
            w(ji+2,"}")
        w(ji-2,"}")
        w(oi+2,"}")
    w(ind+2,"}")
    return ind
ind=emit()
# tails
for k in range(len(HYPS)-1,-1,-1):
    ind-=4; w(ind,"}")
    w(ind,f"@{HYPS[k][1].replace('given-','')}-implies |")
    w(ind+2," -> ".join(h[0] for h in HYPS[k:])+" ->"); w(ind+4,GOAL)
    w(ind+2,f"[by discharge {HYPS[k][1]}]")
pts=["i","j","x","y","z"]; blks=["generalize-"+p for p in pts]
for k in range(len(pts)-1,-1,-1):
    ind-=4; w(ind,"}")
    lbl="all-triples" if k==0 else f"discharge-{pts[k]}"
    w(ind,f"@{lbl} |"); w(ind+2,f"forall {', '.join(pts[k:])}: Element; {HYP} ->"); w(ind+4,GOAL)
    w(ind+2,f"[by generalize {blks[k]}]")
w(8,"}")
w(6,"@family-implies |")
w(8,"(forall i2, j2, k: Element; i2 != j2 -> k != i2 -> k != j2 ->")
w(10,"inN(compose(transposition(i2, k), transposition(i2, j2)))) ->")
w(10,f"forall {', '.join(pts)}: Element; {HYP} ->"); w(12,GOAL)
w(8,"[by discharge given-family]")
w(4,"}")
w(2,"@conclusion |")
w(4,"(forall g, h: Fn; inN(g) -> inN(h) -> inN(compose(g, h))) ->")
w(6,"(forall i2, j2, k: Element; i2 != j2 -> k != i2 -> k != j2 ->")
w(8,"inN(compose(transposition(i2, k), transposition(i2, j2)))) ->")
w(8,f"forall {', '.join(pts)}: Element; {HYP} ->"); w(10,GOAL)
w(4,"[by discharge given-closure]")
w(0,"qed")
out="".join(L)
out=re.sub(r"\[using instantiation (a[A-Za-z]+)\(\(fun g: Fn => inN\(g\)\)\)",
           r"[using instantiation \1((fun g: Fn => inN(g)))", out)
print("braces:", out.count("{"), out.count("}"), "lines:", out.count("\n"))
open('assembly.b4m','w').write(out)
