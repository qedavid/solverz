"""One exists row: own verdict and generator verdict (origin, and --search) for (id, p, r)."""
import sys, os, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, HERE + '/../../../solver')
os.chdir(HERE + '/../../..')
from rows import verdict, inst
import tomoflat as TF
nid, p, r, mode = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
v, k, lam, ms, st = inst[nid]
s = math.isqrt(k + lam * (v - 1)); c, C = v // p ** r, v // p
if mode == 'own':
    vd, info = verdict(p, r, c, C, k, lam, s); print(nid, st, 'own', vd, '|', info)
else:
    a = TF.build(nid, p, r, v, k, lam, ms, st, search=(mode == 'search'))
    print(nid, st, 'gen-' + mode, 'killed=%s nodes=%s' % (a['killed'], a['gnodes']))
