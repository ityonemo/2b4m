"""For each prose paragraph in aata/*.md, find its best match among Judson's paragraphs and
proofs, and classify.

The question is NOT "is our wording similar" but "are we TRANSLITERATING or PARAPHRASING".
So the signal is an asymmetric one:
  - coverage  = fraction of Judson's words present in ours (how much we dropped: TRUNCATION)
  - fidelity  = fraction of our words present in Judson's (how much we invented: PARAPHRASE)
A transliteration scores high on both. Dropping his sentences lowers coverage; writing our
own lowers fidelity.
"""
import re, sys, json, glob, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from extract import words

def our_paras(path):
    """Prose paragraphs OUTSIDE 2b4m fences, with blockquote asides marked."""
    out, buf, infence = [], [], False
    start = 0
    for i, l in enumerate(open(path, errors='replace').read().split('\n'), 1):
        s = l.strip()
        if s.startswith('```'):
            infence = not infence
            if buf: out.append((start, buf)); buf = []
            continue
        if infence: continue
        if not s:
            if buf: out.append((start, buf)); buf = []
            continue
        if not buf: start = i
        buf.append(l)
    if buf: out.append((start, buf))
    res = []
    for ln, lines in out:
        txt = ' '.join(lines)
        aside = all(x.strip().startswith('>') for x in lines)
        w = words(txt)
        if len(w) >= 8: res.append((ln, txt, w, aside))
    return res

def score(ours, theirs):
    so, st = set(ours), set(theirs)
    if not st or not so: return 0.0, 0.0
    cov = len(so & st) / len(st)   # how much of HIS text we carry
    fid = len(so & st) / len(so)   # how much of OURS is his
    return cov, fid

if __name__ == '__main__':
    J = json.load(open(sys.argv[1]))
    blocks = []
    for fn, v in J.items():
        for w in v['proofs']: blocks.append((fn, 'proof', w))
        for w in v['paras']:  blocks.append((fn, 'para', w))
    rows = []
    for f in sorted(glob.glob('aata/*.md')):
        for ln, txt, w, aside in our_paras(f):
            best = (0.0, 0.0, None, None)
            for fn, kind, jw in blocks:
                cov, fid = score(w, jw)
                if cov + fid > best[0] + best[1]: best = (cov, fid, fn, kind)
            rows.append({'file': os.path.basename(f), 'line': ln, 'aside': aside,
                         'words': len(w), 'cov': round(best[0],3), 'fid': round(best[1],3),
                         'src': best[2], 'kind': best[3], 'text': txt[:300]})
    json.dump(rows, open(sys.argv[2],'w'), indent=1)
    import statistics
    nonaside=[r for r in rows if not r['aside']]
    print(f"our prose paragraphs: {len(rows)} ({len(nonaside)} non-aside)")
    print(f"median fidelity: {statistics.median(r['fid'] for r in nonaside):.2f}")
    print(f"paragraphs with fidelity < 0.5 (likely OUR OWN words): {sum(1 for r in nonaside if r['fid']<0.5)}")
    print(f"paragraphs with fidelity < 0.3: {sum(1 for r in nonaside if r['fid']<0.3)}")
