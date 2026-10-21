"""Demote a body-prose paragraph to a `>` blockquote aside, in italics.

These paragraphs are OUR commentary on the formalization, written in Judson's register and
sitting in the transliterated flow as though they were his. The content is legitimately
needed (each introduces an imported std lemma, or describes an induction our encoding
forces); the defect is only that a reader cannot tell it from the source text.

Usage:  python3 demote.py <file> <line> [<line> ...]        # dry run
        python3 demote.py --apply <file> <line> [...]
A line number may point anywhere inside the target paragraph.
"""
import sys, pathlib, re

def para_bounds(lines, ln):
    """Expand from a 1-based line to its blank-delimited paragraph, refusing to cross a fence."""
    i = ln - 1
    while i > 0 and lines[i-1].strip() and not lines[i-1].strip().startswith('```'):
        i -= 1
    j = ln - 1
    while j + 1 < len(lines) and lines[j+1].strip() and not lines[j+1].strip().startswith('```'):
        j += 1
    return i, j

def demote(path, lns, apply=False):
    p = pathlib.Path(path)
    lines = p.read_text(errors='replace').split('\n')
    # work bottom-up so earlier line numbers stay valid
    for ln in sorted(set(lns), reverse=True):
        i, j = para_bounds(lines, ln)
        block = lines[i:j+1]
        if any(x.strip().startswith('>') for x in block):
            print(f"  SKIP {path}:{ln} — already an aside"); continue
        if any(x.strip().startswith('```') for x in block):
            print(f"  SKIP {path}:{ln} — touches a fence"); continue
        if any(re.match(r'\s*(\*\*(Theorem|Lemma|Proposition|Corollary|Definition|Proof|Example)|#)', x) for x in block):
            print(f"  SKIP {path}:{ln} — looks like a result/heading, needs hand review"); continue
        text = ' '.join(x.strip() for x in block)
        # italicize the whole aside, as the file's other asides do
        out = []
        words = text.split(' ')
        cur = '> *'
        for w in words:
            if len(cur) + len(w) + 1 > 94:
                out.append(cur); cur = '> ' + w
            else:
                cur = (cur + ' ' + w) if cur not in ('> *',) else cur + w
        out.append(cur + '*')
        print(f"  {path}:{ln}  ({j-i+1} lines -> {len(out)})  {text[:62]}...")
        if apply: lines[i:j+1] = out
    if apply:
        p.write_text('\n'.join(lines))

if __name__ == '__main__':
    a = sys.argv[1:]
    apply = '--apply' in a
    a = [x for x in a if x != '--apply']
    demote(a[0], [int(x) for x in a[1:]], apply=apply)
