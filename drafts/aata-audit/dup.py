import re, os, glob, json, collections, subprocess

ROOT = "/home/ityonemo/code/2b4m"
os.chdir(ROOT)

# ---- collect theorem declarations + statements straight from source ----
# A declaration is `theorem NAME: <stmt>` or `theorem NAME(params): <stmt>`, and the
# statement may continue over following lines until the `proof` keyword.
DECL = re.compile(r'^\s*(theorem|schema)\s+([A-Za-z_]\w*)\s*(\([^)]*\))?\s*:\s*(.*)$')

def decls(path, literate):
    rows, infence = [], not literate
    lines = open(path, errors="replace").read().split("\n")
    i = 0
    while i < len(lines):
        ln = lines[i]
        if literate:
            s = ln.strip()
            if s.startswith("```2b4m"): infence = True;  i += 1; continue
            if s.startswith("```"):     infence = False; i += 1; continue
        if infence:
            m = DECL.match(ln)
            if m:
                name, stmt = m.group(2), m.group(4).strip()
                j = i + 1
                while j < len(lines):
                    nxt = lines[j].strip()
                    if not nxt or nxt.startswith("//"): j += 1; continue
                    if re.match(r'^(proof|qed)\b', nxt): break
                    if DECL.match(lines[j]) or re.match(r'^\s*(axiom|fact|hole|sort|const|func|pred|import|model|define|intheory)\b', lines[j]): break
                    stmt += " " + nxt
                    j += 1
                rows.append((name, re.sub(r'\s+', ' ', stmt).strip(), i + 1))
                i = j; continue
        i += 1
    return rows

BINDER = re.compile(r'\b(forall|exists)\s+([A-Za-z_]\w*(?:\s*,\s*[A-Za-z_]\w*)*)\s*:\s*([A-Za-z_]\w*)')

def normalize(stmt):
    """Alpha-normalize binder VARIABLES and SORTS positionally. Function/predicate/
    constant symbols are left alone -- aata aliases std's, so they coincide."""
    varmap, sortmap = {}, {}
    for _q, vs, srt in BINDER.findall(stmt):
        for v in [x.strip() for x in vs.split(",")]:
            if v not in varmap: varmap[v] = f"\x00v{len(varmap)}\x00"
        if srt not in sortmap: sortmap[srt] = f"\x01S{len(sortmap)}\x01"
    s = stmt
    for name, repl in sorted(varmap.items(), key=lambda kv: -len(kv[0])):
        s = re.sub(r'\b' + re.escape(name) + r'\b', repl, s)
    for name, repl in sorted(sortmap.items(), key=lambda kv: -len(kv[0])):
        s = re.sub(r'\b' + re.escape(name) + r'\b', repl, s)
    s = s.replace("\x00", "").replace("\x01", "")
    return re.sub(r'\s+', ' ', s).strip().rstrip(".")

std_files  = sorted(set(glob.glob("std/**/*.b4m", recursive=True)))
aata_files = sorted(glob.glob("aata/*.md"))

std_index = collections.defaultdict(list)
std_decls = {}
for f in std_files:
    for name, stmt, line in decls(f, literate=False):
        std_index[normalize(stmt)].append((f, line, name))
        std_decls[(f, name)] = stmt

results = []
for f in aata_files:
    for name, stmt, line in decls(f, literate=True):
        key = normalize(stmt)
        hits = std_index.get(key)
        if hits:
            results.append({"aata_file": f, "aata_line": line, "aata_theorem": name,
                            "statement": stmt, "std": [{"file": a, "line": b, "name": c} for a, b, c in hits]})

json.dump(results, open("/tmp/claude-1000/-home-ityonemo-code-2b4m/4009e7e2-f067-4ec6-b5d7-6bbea4ad67e1/scratchpad/audit/duplicates.json", "w"), indent=1)
print("std theorem/schema decls indexed:", sum(len(v) for v in std_index.values()))
print("aata decls scanned:", sum(len(decls(f, True)) for f in aata_files))
print("aata theorems with an exact std twin (modulo var/sort/thm names):", len(results))
print("aata files involved:", len({r['aata_file'] for r in results}))
