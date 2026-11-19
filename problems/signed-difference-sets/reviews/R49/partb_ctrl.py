"""Controls for partb.py: known sets (objects/) with a Z_p^2 quotient must SURVIVE, with t = 1 and with the
smallest valid multiplier t (C10 condition), centred when p !| s, nc otherwise."""
import sys, os, math, glob
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from partb import vectors, search, mult_ok
from objmath import load
ROOT = HERE + '/../../..'
for fn in sorted(glob.glob(ROOT + '/objects/O*.txt')):
    ns, v, k, lam, D = load(fn)
    s = abs(sum(D.values()))
    for p in (3, 5, 7, 11):
        if sum(1 for n in ns if n % p == 0) < 2 or p ** 2 > v: continue
        c = v // (p * p); centred = s % p != 0
        ts = [1] + ([t for t in range(2, p) if mult_ok(p, t, k - lam)][:1] if centred else [])
        for t in ts:
            if c * p > 400: continue
            L = vectors(p, c * p, k, lam, s, centred, t)
            if len(L) ** ((p + 1) // 2) > 3_000_000: print(os.path.basename(fn), p, t, 'skip |L|=%d' % len(L)); continue
            integral, boxed = search(p, c, s, L)
            print(os.path.basename(fn), ns, (v, k, lam), 'p=%d t=%d %s |L|=%d integral=%d boxed=%d %s' % (
                p, t, 'centred' if centred else 'nc', len(L), integral, boxed, 'SURVIVES' if boxed else 'KILLED!'), flush=True)
