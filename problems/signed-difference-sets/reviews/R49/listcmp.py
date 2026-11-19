"""Own vector lists vs the rows' `w` (TomographyFlatRows and Part B TomographyQuotRows): equal as sets?"""
import re, glob, os, sys, math, ast
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from rows import inst, valid_vectors, ROOT
from partb import vectors
def wlist(txt):
    m = re.search(r'def w : List \(List ℤ\) :=\s*\n\s*(\[.*?\]\])\s*\n', txt, re.S)
    return None if not m else sorted(tuple(x) for x in ast.literal_eval(m[1].replace('\n', ' ')))
bad = 0; n = 0
for fn in sorted(glob.glob(ROOT + '/lean/SignedDifferenceSets/TomographyFlatRows/N*.lean')):
    nid = os.path.basename(fn)[:-5]; txt = open(fn, encoding='utf-8').read()
    v, k, lam, inv, st = inst[nid]; p = int(re.search(r'\(p := (\d+)\)', txt)[1])
    s = math.isqrt(k + lam * (v - 1)); own = sorted(valid_vectors(p, v // p, k, lam, s, s % p != 0))
    w = wlist(txt); n += 1
    if w != own: bad += 1; print('DIFF', nid, w, own)
ids = [l.split()[0] for l in open(HERE + '/partB_state.txt') if 'BUILT' in l]
for nid in ids:
    txt = open(ROOT + '/lean/SignedDifferenceSets/TomographyQuotRows/%s.lean' % nid, encoding='utf-8').read()
    v, k, lam, inv, st = inst[nid]
    p = int(re.search(r'not_hasSDS_grp \(ms := \[[\d, ]*\]\) (\d+)', txt)[1])
    tm = re.search(r'\(t := (\d+)\)', txt); t = int(tm[1]) if tm else 1
    c = v // (p * p); s = math.isqrt(k + lam * (v - 1))
    own = sorted(vectors(p, c * p, k, lam, s, s % p != 0, t))
    w = wlist(txt); n += 1
    if w is None: print('nolist', nid, 'own', len(own)); continue
    if w != own: bad += 1; print('DIFF', nid, len(w), len(own))
print('compared', n, 'differ', bad)
