"""Controls for the centred p = 3 route: SDS that exist with 3 !| s and a Z_3^r quotient (no known set in objects/ has
this). (v,1,0) = delta_0; (v,v,v-4) = 1 - 2 delta_0; D1 x delta_0 for lambda = 0 sets D1 ((4,4,0) in C4, (7,4,0) in C7).
Each: own verdict (rows.verdict) and the generator (solver/tomoflat.build, origin and --search)."""
import sys, os, signal
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, HERE + '/../../../solver')
os.chdir(HERE + '/../../..')
from rows import verdict
import tomoflat as TF
cases = [  # (name, v, k, lam, ms, p, r)
    ('delta Z3^3', 27, 1, 0, [3, 3, 3], 3, 3),
    ('1-2delta Z3^3', 27, 27, 23, [3, 3, 3], 3, 3),
    ('delta Z3^4 r3', 81, 1, 0, [3, 3, 3, 3], 3, 3),
    ('1-2delta Z3^4 r3', 81, 81, 77, [3, 3, 3, 3], 3, 3),
    ('1-2delta Z3^4 r4', 81, 81, 77, [3, 3, 3, 3], 3, 4),
    ('C4 x delta Z3^3', 108, 4, 0, [3, 3, 12], 3, 3),
    ('C7 x delta Z3^3', 189, 4, 0, [3, 3, 21], 3, 3),
    ('1-2delta Z2^5', 32, 32, 28, [2, 2, 2, 2, 2], 2, 5),
    ('1-2delta Z2^6 r5', 64, 64, 60, [2, 2, 2, 2, 2, 2], 2, 5),
]
for name, v, k, lam, ms, p, r in cases:
    import math
    s = math.isqrt(k + lam * (v - 1)); c, C = v // p ** r, v // p
    vd, info = verdict(p, r, c, C, k, lam, s)
    out = []
    for search in (False, True):
        try:
            a = TF.build('X', p, r, v, k, lam, ms, 'exists', search=search)
            out.append('gen%s killed=%s nodes=%s' % ('-search' if search else '', a['killed'], a['gnodes']))
        except Exception as e:
            out.append('gen%s error %r' % ('-search' if search else '', e))
    print(name, '| own:', vd, '|', info, '|', '; '.join(out), flush=True)
