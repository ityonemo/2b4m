import sys,re; sys.path.insert(0,'.')
import final
def wrap(ci,cj,thmname="probeLeaf"):
    HYPS=[("i != j","h1","i-is-not-j"),("x != y","h2","x-is-not-y"),
          ("x != z","h3","x-is-not-z"),("y != z","h4","y-is-not-z")]
    arm=f"{final.iarm(ci)}-and-{final.jarm(cj)}"
    HYP=" -> ".join(h[0] for h in HYPS)
    def af0(fp,c):
        return f"{final.POS[c]} = {fp}" if c is not None else " and ".join(f"{v} != {fp}" for v in "xyz")
    ALLH=HYP+f" -> ({af0('i',ci)}) -> ({af0('j',cj)})"
    L=[]
    def w(ind,t=""): L.append((" "*ind+t).rstrip()+"\n")
    for l in ['import permutation <<< "std/permutation.b4m"',
              'import alternating <<< "std/permutation/alternating.b4m"',
              'import ai <<< "std/permutation/alternating-identities.b4m"',
              "sort Element = permutation.Element","sort Fn = permutation.Fn",
              "func compose = permutation.compose","func transposition = permutation.transposition",""]:
        w(0,l)
    w(0,f"theorem {thmname}(inN(Fn)):")
    w(2,"(forall g, h: Fn; inN(g) -> inN(h) -> inN(compose(g, h))) ->")
    w(2,"(forall i2, j2, k: Element; i2 != j2 -> k != i2 -> k != j2 ->")
    w(4,"inN(compose(transposition(i2, k), transposition(i2, j2)))) ->")
    w(2,"forall i, j, x, y, z: Element;")
    w(2,f"{ALLH} ->")
    w(2,final.GOAL)
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
    for v,blk in [("i","gi"),("j","gj"),("x","gx"),("y","gy"),("z","gz")]:
        w(ind,f"@{blk} |"); w(ind+2,f"fix {v}: Element {{"); ind+=4
    for txt,blk,lbl in HYPS:
        w(ind,f"@{blk} |"); w(ind+2,f"assume {txt} {{"); ind+=4
    def af(fp,c):
        return f"{final.POS[c]} = {fp}" if c is not None else " and ".join(f"{v} != {fp}" for v in "xyz")
    w(ind,f"@when-{final.iarm(ci)} |"); w(ind+2,f"assume {af('i',ci)} {{"); ind+=4
    w(ind,f"@when-{final.jarm(cj)} |"); w(ind+2,f"assume {af('j',cj)} {{"); ind+=4
    final.OUT=[]; final.emit_leaf_body(ind,ci,cj); body=final.OUT
    bodytext="".join(body)
    for txt,blk,lbl in HYPS:
        if re.search(r"\b"+re.escape(lbl)+r"\b", bodytext):
            w(ind,f"@{lbl} |"); w(ind+2,txt); w(ind+2,f"[by hypothesis {blk}]")
    L+=body
    needs_closure = "closure]" in bodytext
    for k in range(len(HYPS)+1,-1,-1):
        ind-=4; w(ind,"}")
        if k==len(HYPS)+1:
            w(ind,"@j-arm-implies |"); w(ind+2,f"({af('j',cj)}) ->"); w(ind+4,final.GOAL)
            w(ind+2,f"[by discharge when-{final.jarm(cj)}]")
        elif k==len(HYPS):
            w(ind,"@i-arm-implies |"); w(ind+2,f"({af('i',ci)}) -> ({af('j',cj)}) ->"); w(ind+4,final.GOAL)
            w(ind+2,f"[by discharge when-{final.iarm(ci)}]")
        else:
            w(ind,f"@{HYPS[k][1]}-implies |")
            w(ind+2," -> ".join(h[0] for h in HYPS[k:])+f" -> ({af('i',ci)}) -> ({af('j',cj)}) ->")
            w(ind+4,final.GOAL); w(ind+2,f"[by discharge {HYPS[k][1]}]")
    pts=["i","j","x","y","z"]; blks=["gi","gj","gx","gy","gz"]
    for k in range(len(pts)-1,-1,-1):
        ind-=4; w(ind,"}")
        lbl="all-points" if k==0 else f"d-{pts[k]}"
        w(ind,f"@{lbl} |"); w(ind+2,f"forall {', '.join(pts[k:])}: Element; {ALLH} ->"); w(ind+4,final.GOAL)
        w(ind+2,f"[by generalize {blks[k]}]")
    w(8,"}")
    w(6,"@family-implies |")
    w(8,"(forall i2, j2, k: Element; i2 != j2 -> k != i2 -> k != j2 ->")
    w(10,"inN(compose(transposition(i2, k), transposition(i2, j2)))) ->")
    w(10,f"forall {', '.join(pts)}: Element; {ALLH} ->"); w(12,final.GOAL)
    w(8,"[by discharge given-family]")
    w(4,"}")
    w(2,"@conclusion |")
    w(4,"(forall g, h: Fn; inN(g) -> inN(h) -> inN(compose(g, h))) ->")
    w(6,"(forall i2, j2, k: Element; i2 != j2 -> k != i2 -> k != j2 ->")
    w(8,"inN(compose(transposition(i2, k), transposition(i2, j2)))) ->")
    w(8,f"forall {', '.join(pts)}: Element; {ALLH} ->"); w(10,final.GOAL)
    w(4,"[by discharge given-closure]")
    w(0,"qed")
    out="".join(L)
    # strip the `closure` restatement if no step cites it
    if not re.search(r"(?<![-\w])closure\]", out):
        out=re.sub(r"\n *@closure \|(?:\n[^\n]*)*?\[by hypothesis given-closure\]", "", out)
    out=re.sub(r"\[using instantiation (a[A-Za-z]+)\(\(fun g: Fn => inN\(g\)\)\)", r"[using instantiation ai.\1((fun g: Fn => inN(g)))", out)
    # concrete instantiation
    stmt=re.search(r"theorem "+thmname+r"\(inN\(Fn\)\):\n(.*?)\nproof", out, re.S).group(1)
    # drop the closure premise: the instantiation discharges it with `closed`
    lines=[l for l in stmt.split("\n")]
    assert "inN(g) -> inN(h)" in lines[0], lines[0]
    A="\n".join(lines[1:]).replace("inN(","alternating.inAlternating(")
    out += f"""
theorem {thmname}Concrete:
{A}
proof
  @closed |
    forall g, h: Fn; alternating.inAlternating(g) -> alternating.inAlternating(h) ->
      alternating.inAlternating(compose(g, h))
    [by cite alternating.theAlternatingGroupIsClosedUnderComposition]
  @conclusion |
{A}
    [using instantiation {thmname}((fun g: Fn => alternating.inAlternating(g))) closed]
qed
"""
    return out
