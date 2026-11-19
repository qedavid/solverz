"""End-to-end on G = Z2 x Z2 x Z3 (v = 12): exhaustive SDS existence vs the Klein kill verdict."""
import itertools, sys, math
sys.path.insert(0, '.')
from kill import verdict
G = [(a, b, c) for a in range(2) for b in range(2) for c in range(3)]
idx = {g: i for i, g in enumerate(G)}
add = [[idx[((x[0]+y[0]) % 2, (x[1]+y[1]) % 2, (x[2]+y[2]) % 3)] for y in G] for x in G]
found = {}
for D in itertools.product((-1, 0, 1), repeat=12):
    lam = None; ok = True
    for g in range(1, 12):
        s = sum(D[x]*D[add[x][g]] for x in range(12))
        if lam is None: lam = s
        elif s != lam: ok = False; break
    if ok:
        k = sum(1 for d in D if d); found.setdefault((k, lam), D)
print('exists (k,lam):', sorted(found))
for k in range(1, 13):
    for lam in range(-12, 13):
        V = verdict(12, k, lam)
        if V and V['kill']:
            print('killed', (12, k, lam), 'EXISTS!' if (k, lam) in found else 'ok (none)')
