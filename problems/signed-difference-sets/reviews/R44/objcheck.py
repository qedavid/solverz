"""Known objects vs the independent Z lists; C26/C37(a) halving on O101 (C3xC18), O79, O80 (C3xC3xC6)."""
import sys, itertools
P = sys.argv[1]
def load(name):
    L = open(f"{P}/objects/{name}.txt").read().split('\n')
    dims = L[0].split()[0]
    pts = {}
    for l in L[1:]:
        t = l.split()
        if not t: continue
        pts[tuple(int(x) for x in t[:-1])] = 1 if t[-1] == '+' else -1
    return dims, pts
def norm_K(pts):  # Z3xZ9: negate to positive sum, translate a minus to 0; all such
    s = sum(pts.values())
    if s < 0: pts = {k: -v for k, v in pts.items()}
    out = []
    for (a0, b0), v in pts.items():
        if v == -1:
            f = [0]*27
            for (a, b), w in pts.items(): f[9*((a-a0)%3) + (b-b0)%9] = w
            out.append(tuple(f))
    return out
def zs(fn): return set(tuple(int(x) for x in l.split()) for l in open(fn) if l.strip())
z464, z449 = zs(f"{P}/R44/rs/zsN464.txt"), zs(f"{P}/R44/rs/zsN449.txt")
_, o10 = load('O10'); _, o8 = load('O8')
print('O10 normalisations in my N464 list:', [f in z464 for f in norm_K(o10)])
print('O8 normalisations in my N449 list:', [f in z449 for f in norm_K(o8)])
# generic SDS check on a product of cyclic groups
def sds(dims, f):
    els = list(itertools.product(*[range(d) for d in dims]))
    add = lambda x, y: tuple((a+b) % d for a, b, d in zip(x, y, dims))
    k = sum(1 for x in els if f.get(x, 0))
    cs = set(sum(f.get(x, 0)*f.get(add(x, g), 0) for x in els) for g in els if any(g))
    return k, cs
def halve(dims, pts, split):  # split: element -> (u, y)
    D0, D1 = {}, {}
    for x in itertools.product(*[range(d) for d in dims]):
        u, y = split(x)
        (D0 if u == 0 else D1)[y] = pts.get(x, 0)
    par = all((D0[y] - D1[y]) % 2 == 0 for y in D0)
    Z = {y: (D0[y] + D1[y]) // 2 for y in D0}
    T = {y: (D0[y] - D1[y]) // 2 for y in D0}
    disj = all(Z[y] == 0 or T[y] == 0 for y in D0)
    return par, Z, T, disj
for name, kdims, split in [('O101', (3, 9), lambda x: (x[1] % 2, (x[0], x[1] % 9))),
                           ('O79', (3, 3, 3), lambda x: (x[2] % 2, (x[0], x[1], x[2] % 3))),
                           ('O80', (3, 3, 3), lambda x: (x[2] % 2, (x[0], x[1], x[2] % 3)))]:
    dims, pts = load(name)
    gd = (3, 18) if name == 'O101' else (3, 3, 6)
    k, cs = sds(gd, pts)
    par, Z, T, disj = halve(gd, pts, split)
    print(name, dims, 'D:', (k, cs), 'parity', par, 'Z:', sds(kdims, Z), 'T:', sds(kdims, T), 'disjoint', disj,
          'expected Z', ((k + min(cs)) // 4, min(cs) / 2), 'T', ((k - min(cs)) // 4, 0))
