import sys,re; sys.path.insert(0,'.')
from gen_assembly import SCHEMAS
POS={0:"x",1:"y",2:"z"}
LEAF={(0,1):None,(0,2):"twist",(0,None):"offpair",(1,0):"twistsecond",(1,2):"famend",
 (1,None):"firstmiddle",(2,0):"famsecond",(2,1):"twistoff",(2,None):"firstend",
 (None,0):"secondpoint",(None,1):"secondmid",(None,2):"secondend",(None,None):"disjoint"}
OUTER={("i","j"):"i-is-not-j",("x","y"):"x-is-not-y",("x","z"):"x-is-not-z",("y","z"):"y-is-not-z"}
GOALT=("x","y","z")
def tri(t): return f"compose(transposition({t[0]}, {t[2]}), transposition({t[0]}, {t[1]}))"
GOAL=f"inN({tri(GOALT)})"
def ct(d):
    m=re.match(r"inN\(compose\(transposition\((\w+), (\w+)\), transposition\((\w+), (\w+)\)\)\)",d)
    A,C,A2,B=m.groups(); return (A,B,C)
def gt(ci,cj):
    t=list(GOALT)
    if ci is not None: t[ci]="i"
    if cj is not None: t[cj]="j"
    return tuple(t)
def bind(d): return [v.strip() for v in re.match(r"forall ([^:]+): Element;",d[0]).group(1).split(",")]
def FAMX(k): return f"compose(transposition(i, {k}), transposition(i, j))"

def plan(ci,cj,project=None):
    eq={}
    if ci is not None: eq[POS[ci]]="i"
    if cj is not None: eq[POS[cj]]="j"
    inv={v:k for k,v in eq.items()}
    frees=[v for v in "xyz" if v not in eq]
    have=dict(OUTER)
    if ci is None:
        for v in "xyz": have[(v,"i")]=f"{v}-is-not-i"
    if cj is None:
        for v in "xyz": have[(v,"j")]=f"{v}-is-not-j"
    steps=[]
    if project is None: project=lambda l: l
    def ensure(a,b):
        if (a,b) in have: return have[(a,b)]   # caller projects if it is an arm conjunct
        lbl=f"{a}-is-not-{b}"
        if (b,a) in have:
            steps.append((lbl,f"{a} != {b}",
              f"[using specialize alternating.disequalityIsSymmetric({b}, {a}) {have[(b,a)]}]"))
            have[(a,b)]=lbl; return lbl
        for (A,B,sub) in [(eq.get(a,a),b,f"{a}-is-{eq[a]}" if a in eq else None),
                          (a,eq.get(b,b),f"{b}-is-{eq[b]}" if b in eq else None),
                          (inv.get(a,a),b,f"{inv[a]}-is-{a}" if a in inv else None),
                          (a,inv.get(b,b),f"{inv[b]}-is-{b}" if b in inv else None)]:
            if sub and (A,B)!=(a,b):
                project(sub)
                base=project(ensure(A,B))
                steps.append((lbl,f"{a} != {b}",f"[by rewrite {sub} {base}]"))
                have[(a,b)]=lbl; return lbl
        raise SystemExit(f"STUCK {a}!={b} arm({ci},{cj})")
    # Nothing is pre-ensured: the leaf body calls ensure() for exactly the
    # orientations its cited theorem consumes, so no unused fact is emitted.
    return eq,inv,frees,steps,have,ensure

OUT=[]
def w(ind,t=""): OUT.append((" "*ind+t).rstrip()+"\n")

def arm_formula(ci,cj):
    p=[]
    if ci is not None: p.append(f"{POS[ci]} = i")
    else: p += [f"{v} != i" for v in "xyz"]
    if cj is not None: p.append(f"{POS[cj]} = j")
    else: p += [f"{v} != j" for v in "xyz"]
    return " and ".join(p)
def iarm(ci): return "no-i" if ci is None else f"{POS[ci]}-is-i"
def jarm(cj): return "no-j" if cj is None else f"{POS[cj]}-is-j"

def emit_leaf_body(ind, ci, cj):
    """Emit a real leaf's steps, ending with a step labelled conclusion-<arm> proving GOAL."""
    arm=f"{iarm(ci)}-and-{jarm(cj)}"
    # each position fact comes straight from the arm that assumes it
    conj={}; owner={}
    iarmlbl=f"when-{iarm(ci)}"; jarmlbl=f"when-{jarm(cj)}"
    if ci is not None:
        conj[f"{POS[ci]}-is-i"]=f"{POS[ci]} = i"; owner[f"{POS[ci]}-is-i"]=iarmlbl
    else:
        for v in "xyz":
            conj[f"{v}-is-not-i"]=f"{v} != i"; owner[f"{v}-is-not-i"]=iarmlbl
    if cj is not None:
        conj[f"{POS[cj]}-is-j"]=f"{POS[cj]} = j"; owner[f"{POS[cj]}-is-j"]=jarmlbl
    else:
        for v in "xyz":
            conj[f"{v}-is-not-j"]=f"{v} != j"; owner[f"{v}-is-not-j"]=jarmlbl
    projected=set(); held=set()
    def armform(armlbl):
        fp = "i" if armlbl.endswith("no-i") else "j"
        return " and ".join(f"{v} != {fp}" for v in "xyz")
    def project(lbl):
        if lbl in conj and lbl not in projected:
            src=owner[lbl]
            bundled = src.endswith(("no-i","no-j"))
            if bundled and src not in held:
                w(ind,f"@{src}-holds |"); w(ind+2,armform(src))
                w(ind+2,f"[by hypothesis {src}]"); held.add(src)
            w(ind,f"@{lbl} |"); w(ind+2,conj[lbl])
            w(ind+2,f"[using tautology {src}-holds]" if bundled else f"[by hypothesis {src}]")
            projected.add(lbl)
        return lbl
    eq,inv,frees,steps,have,ensure=plan(ci,cj,project)
    emitted=set()
    def flush():
        while steps:
            lbl,stmt,just=steps.pop(0)
            if lbl in emitted: continue
            w(ind,f"@{lbl} |"); w(ind+2,stmt); w(ind+2,just); emitted.add(lbl)
    key=LEAF[(ci,cj)]
    g=gt(ci,cj)
    if key is None:
        k=frees[0]
        r1=project(ensure(k,'i')); r2=project(ensure(k,'j')); flush()
        w(ind,f"@the-family-member |"); w(ind+2,f"inN({FAMX(k)})")
        w(ind+2,f"[using specialize family(i, j, {k}) i-is-not-j {r1} {r2}]")
        src="the-family-member"; cur=("i","j",k)
    else:
        name,decl,needs_closure=SCHEMAS[key]
        bs=bind(decl); sub=dict(zip(ct(decl[-1]),g))
        for b in bs: sub.setdefault(b, {"i2":"i","j2":"j"}.get(b))
        args=[sub[b] for b in bs]
        def ap(s):
            for b in sorted(bs,key=len,reverse=True): s=re.sub(r"\b"+b+r"\b",sub[b],s)
            return s
        prem=[]
        for line in decl[1:-1]:
            for cl in line.split("->"):
                cl=cl.strip()
                if cl: prem.append(ap(cl))
        refs=[]
        for p in prem:
            if "!=" in p:
                a,b=[t.strip() for t in p.split("!=")]
                refs.append(project(ensure(a,b))); flush()
            else:
                m=re.match(r"inN\(compose\(transposition\((\w+), (\w+)\), transposition\((\w+), (\w+)\)\)\)",p)
                kk=m.group(2)
                lbl=f"family-at-{kk}"
                if lbl not in refs:
                    r1=project(ensure(kk,'i')); r2=project(ensure(kk,'j')); flush()
                    w(ind,f"@{lbl} |"); w(ind+2,f"inN({FAMX(kk)})")
                    w(ind+2,f"[using specialize family(i, j, {kk}) i-is-not-j {r1} {r2}]")
                refs.append(lbl)
        flush()
        w(ind,f"@{arm}-shape |")
        for line in decl: w(ind+2,line)
        extra=" closure" if needs_closure else ""
        w(ind+2,f"[using instantiation {name}((fun g: Fn => inN(g))){extra}]")
        w(ind,f"@the-shaped-member |"); w(ind+2,f"inN({tri(g)})")
        w(ind+2,f"[using specialize {arm}-shape({', '.join(args)}) {' '.join(refs)}]")
        src="the-shaped-member"; cur=g
    # rewrite the position equalities back to (x,y,z)
    for coord,fixed in eq.items():
        project(f"{coord}-is-{fixed}")
        nxt=tuple(coord if t==fixed else t for t in cur)
        lbl=f"{arm}-back-{coord}" if nxt!=GOALT else f"conclusion-{arm}"
        w(ind,f"@{lbl} |"); w(ind+2,f"inN({tri(nxt)})")
        w(ind+2,f"[by rewrite {coord}-is-{fixed} {src}]")
        src=lbl; cur=nxt
    if cur!=GOALT:
        w(ind,f"@conclusion-{arm} |"); w(ind+2,GOAL); w(ind+2,f"[by rewrite reflexivity {src}]")
    return f"conclusion-{arm}"
