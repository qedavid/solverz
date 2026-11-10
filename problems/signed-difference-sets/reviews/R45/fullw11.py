"""Refuter (C40): p = 11 rows without the multiplier. W := first-moment-0 part of the full V from
vfull (Rust, no normalisation); compare with the orbit list, then search."""
import sys, ast, math
from indep_lib import m1, search, enum_Wfix
rows = {'N3044': (40, 3), 'N3058': (60, 7), 'N3068': (76, 5), 'N3072': (76, 17), 'N3074': (76, 45), 'N3104': (105, 46)}
p = 11
for rid in sys.argv[1:]:
    k, lam = rows[rid]; s = math.isqrt(k + lam * (p * p - 1))
    V = [tuple(ast.literal_eval(l)) for l in open(f'vfull/{rid}.txt') if l.startswith('[')]
    W = [y for y in V if m1(y, p) == 0]
    Wfix, _ = enum_Wfix(p, k, lam, s, k - lam)
    n_int, n_sds, ex, _ = search(p, s, W)
    print(rid, f"|V|={len(V)} |W|={len(W)} W==Wfix {sorted(W) == sorted(Wfix)} integral {n_int} SDS {n_sds}",
          "KILLED" if n_sds == 0 else "FOUND")
