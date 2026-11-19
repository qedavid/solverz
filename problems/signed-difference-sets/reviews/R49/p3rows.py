"""Rows of instances.csv with a Z_3^r quotient (r >= 3) and 3 !| s: do the centred valid vectors on Z_3 share w(0)?"""
import sys, os, math
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from rows import inst, valid_vectors
multi = 0; tot = 0
for nid, (v, k, lam, inv, st) in inst.items():
    if sum(1 for n in inv if n % 3 == 0) < 3: continue
    s2 = k + lam * (v - 1); s = math.isqrt(s2)
    if s * s != s2 or s % 3 == 0: continue
    V = valid_vectors(3, v // 3, k, lam, s, True)
    tot += 1
    z = sorted(set(y[0] for y in V))
    if len(z) > 1:
        multi += 1; print(nid, st, (v, k, lam, inv), 's=%d' % s, 'w0 values', z, 'vectors', V)
print('rows', tot, 'with several w(0):', multi)
