"""Extract Judson's prose (per <proof> and per <p>) from the vendored XML, normalized for
comparison against our aata/*.md transliterations.

Normalization is deliberately AGGRESSIVE on notation and PRESERVING on words: the chapters
legitimately rename symbols (the transcription exception covers names and notation), so a
conformance check must compare the WORDS. Latex, markup, entities and whitespace all go;
word sequence stays.
"""
import re, sys, json, glob, os

def strip_markup(t):
    t = re.sub(r'<idx>.*?</idx>', ' ', t, flags=re.S)       # index entries are not prose
    t = re.sub(r'<title>.*?</title>', ' ', t, flags=re.S)
    t = re.sub(r'<sage>.*?</sage>', ' ', t, flags=re.S)     # sage cells are not prose
    t = re.sub(r'<[^>]+>', ' ', t)
    t = t.replace('&amp;','&').replace('&lt;','<').replace('&gt;','>').replace('&quot;','"')
    return t

WORD = re.compile(r"[A-Za-z][A-Za-z'-]*")
# Latex control words and single letters carry notation, not prose. Drop them so that
# `\lambda_g(a) = ga` does not masquerade as five words.
LATEX = re.compile(r'\\[A-Za-z]+|\\[^A-Za-z]')

def words(t):
    t = LATEX.sub(' ', t)
    out = [w.lower() for w in WORD.findall(t)]
    # single letters are variable names, not vocabulary
    return [w for w in out if len(w) > 1]

def proofs_and_paras(path):
    s = open(path, errors='replace').read()
    proofs = [words(strip_markup(m.group(1))) for m in re.finditer(r'<proof[^>]*>(.*?)</proof>', s, re.S)]
    # paragraphs OUTSIDE proofs/exercises: the inter-theorem exposition
    body = re.sub(r'<proof[^>]*>.*?</proof>', ' ', s, flags=re.S)
    body = re.sub(r'<exercises?[^>]*>.*?</exercises?>', ' ', body, flags=re.S)
    paras = [words(strip_markup(m.group(1))) for m in re.finditer(r'<p[^>]*>(.*?)</p>', body, re.S)]
    return proofs, [p for p in paras if len(p) >= 8]

if __name__ == '__main__':
    out = {}
    for f in sorted(glob.glob('vendor/aata/src/*.xml')):
        pr, pa = proofs_and_paras(f)
        if pr or pa:
            out[os.path.basename(f)] = {'proofs': pr, 'paras': pa}
    json.dump(out, open(sys.argv[1], 'w'))
    print(f"{len(out)} xml files: {sum(len(v['proofs']) for v in out.values())} proofs, "
          f"{sum(len(v['paras']) for v in out.values())} paragraphs")
