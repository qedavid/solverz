"""Every M1 kill (row, m, p) from indep.out must also be a kill of Tan's F-bound (Def 2.10, Results 2.11-2.12) on the
same quotient: n > c^2 F(m,n)^2 / phi(F(m,n)), with F(m,n) | m/p. Uses scratch/c26/fbound_lib.py's F (copied from Tan)."""
import sys, re
sys.path.insert(0, 'scratch/c26')
from fbound_lib import F, phi
bad = notdiv = tot = 0
for ln in open('R39/indep.out'):
    parts = ln.split()
    g = re.match(r"SDS\((\d+),(-?\d+),(-?\d+),", parts[2])
    v, k, lam = map(int, g.groups())
    n = k - lam
    for mp in parts[3:]:
        m, p = map(int, mp.split('/'))
        c = v // m
        f = F(m, n)
        tot += 1
        if (m // p) % f:
            notdiv += 1
        if not n * phi(f) > c * c * f * f:
            bad += 1
print('M1 kills', tot, 'F(m,n) not dividing m/p', notdiv, 'not killed by Tan F-bound', bad)
