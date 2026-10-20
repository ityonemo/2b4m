"""Insert the duplicate-catalog cross-reference asides into aata/*.md.

Each aside goes in PROSE, immediately above the ```2b4m fence whose block declares the
theorem -- never inside the fence (it would be parsed as 2b4m) and never above the prose
that introduces the theorem (the aside annotates the code, not the exercise statement).

Idempotent: a theorem that already carries its aside is skipped, so a re-run after `std`
line numbers drift updates nothing it should not.

Usage:  python3 drafts/aata-audit/insert_asides.py           # dry run, prints a plan
        python3 drafts/aata-audit/insert_asides.py --apply   # writes the files
"""
import re, os, sys, json, subprocess, collections

ROOT = "/home/ityonemo/code/2b4m"
os.chdir(ROOT)
APPLY = "--apply" in sys.argv
CATALOG = "/tmp/claude-1000/-home-ityonemo-code-2b4m/4009e7e2-f067-4ec6-b5d7-6bbea4ad67e1/scratchpad/audit/duplicates.json"

os.makedirs(os.path.dirname(CATALOG), exist_ok=True)
subprocess.run([sys.executable, "drafts/aata-audit/dup.py"], check=True,
               stdout=subprocess.DEVNULL)
rows = json.load(open(CATALOG))

MARKER = "NB: This theorem exists in std"

def aside_for(r):
    """One blockquote. Two std rows = the statement lives in two theories; list both."""
    if len(r["std"]) == 1:
        s = r["std"][0]
        return [f'> {MARKER} in `{s["file"]}:{s["line"]}:{s["name"]}`.']
    out = [f"> {MARKER} in more than one theory — cite whichever this chapter is layered on:"]
    out += [f'> - `{s["file"]}:{s["line"]}:{s["name"]}`' for s in r["std"]]
    return out

def fence_open_above(lines, decl_idx):
    """Walk up from the declaration to the ```2b4m that opens its block."""
    for i in range(decl_idx, -1, -1):
        if lines[i].strip().startswith("```2b4m"):
            return i
    return None

by_file = collections.defaultdict(list)
for r in rows:
    by_file[r["aata_file"]].append(r)

planned = skipped = 0
plan = []
for path, rs in sorted(by_file.items()):
    lines = open(path, errors="replace").read().split("\n")
    # Group by the fence each theorem belongs to: several catalogued theorems can share one
    # block, and they must all land above that single fence, in declaration order.
    per_fence = collections.defaultdict(list)
    for r in sorted(rs, key=lambda r: r["aata_line"]):
        decl = r["aata_line"] - 1
        f = fence_open_above(lines, decl)
        if f is None:
            plan.append(("WARN", path, r["aata_theorem"], "no opening fence found")); continue
        per_fence[f].append(r)

    inserts = []
    for fence, group in sorted(per_fence.items()):
        # already annotated? look at the prose directly above the fence
        probe = fence - 1
        seen = []
        while probe >= 0 and (lines[probe].strip().startswith(">") or not lines[probe].strip()):
            seen.append(lines[probe]); probe -= 1
        existing = "\n".join(seen)
        block = []
        for r in group:
            # Probe on the STD reference, which is what the aside actually writes -- the
            # aata theorem name is often a chapter rename (theCanonicalMapIsAHomomorphism
            # vs clsPreservesOp) and would never match, re-inserting on every run.
            if all(f'`{x["file"]}:{x["line"]}:{x["name"]}`' in existing for x in r["std"]):
                skipped += 1; continue
            # A bare `>` between entries: without it a following single-line aside reads as
            # another bullet of the preceding multi-theory list, inside one blockquote.
            if block: block.append(">")
            block += aside_for(r)
        if not block: continue
        # Exactly one blank line on each side. `probe` sits on the last non-blank prose
        # line; `fence-1-probe` counts the blanks already between it and the fence, so a
        # leading blank is added only when the prose butts straight up against the fence.
        text = block + [""]
        if probe >= 0 and (fence - 1 - probe) == 0:
            text = [""] + text
        inserts.append((fence, text, [r["aata_theorem"] for r in group]))
        planned += len(group)

    for fence, text, names in reversed(inserts):   # bottom-up: keeps earlier offsets valid
        if APPLY:
            lines[fence:fence] = text
        plan.append(("INS", path, ",".join(names), f"above fence at line {fence+1}"))
    if APPLY and inserts:
        open(path, "w").write("\n".join(lines))

for kind, path, who, note in plan:
    print(f"  {kind:4} {path:52} {who[:44]:46} {note}")
print()
print(f"{'INSERTED' if APPLY else 'would insert'}: {planned} asides"
      f"{'' if APPLY else ' (dry run)'} | already present: {skipped}"
      f" | files: {len({p for k,p,_,_ in plan if k=='INS'})}")
