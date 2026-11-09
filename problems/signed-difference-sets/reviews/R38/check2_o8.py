"""Check 2: is N62's set O8 (C3 x C9) of the form x + e(R - N), R a semiregular (9,3,9,3) RDS, N of order 3?
Same for O7 (C3^3). Then: orbits of all R - N sets (216 normalized RDSs) under Aut(C3 x C9) x translations x sign."""
import itertools
import numpy as np
import sdslib as L

def as_set(D, val):
    return [tuple(int(t) for t in x) for x in np.argwhere(D == val)]

def shape_RminusN(D, ms, n):
    out = []
    z = (0,) * len(ms)
    for e in (1, -1):
        plus, minus, zeros = as_set(e * D, 1), as_set(e * D, -1), as_set(e * D, 0)
        if len(minus) != n - 1: continue
        for x in zeros:
            N = [L.add(m, L.neg(x, ms), ms) for m in minus] + [z]
            if set(L.subgroup_gen(N, ms)) != set(N): continue
            R = [L.add(m, L.neg(x, ms), ms) for m in plus] + [z]
            out.append((e, x, sorted(N), sorted(R), L.is_rds(R, N, ms, n)))
    return out

for i in (7, 8):
    ms, par, D = L.load_obj(i)
    print(f"O{i} {ms} {par}: SDS {L.sds_params(D)}; R - N decompositions:", shape_RminusN(D, ms, 3))

# automorphisms of Z3 x Z9: images of generators (1,0) (order 3) and (0,1) (order 9)
ms = (3, 9)
els = L.elements(ms)
def order(a):
    k, b = 1, a
    while b != (0, 0): b = L.add(b, a, ms); k += 1
    return k
auts = []
for a in els:
    if order(a) not in (1, 3): continue
    for b in els:
        if order(b) != 9: continue
        img = {}
        ok = True
        for (x, y) in els:
            t = (0, 0)
            for _ in range(x): t = L.add(t, a, ms)
            for _ in range(y): t = L.add(t, b, ms)
            img[(x, y)] = t
        if len(set(img.values())) == 27: auts.append(img)
print("|Aut(C3 x C9)| =", len(auts))
def canon(D):
    best = None
    for img in auts:
        for t in els:
            for e in (1, -1):
                key = tuple(sorted((L.add(img[x], t, ms), e * int(D[x])) for x in els if D[x] != 0))
                if best is None or key < best: best = key
    return best
# all normalized semiregular RDS (brute force), their R - N
reps = {}
z = (0, 0)
for N in L.subgroups_of_order(ms, 3):
    seen, cosets = set(), []
    for g in els:
        if g in seen: continue
        c = [L.add(g, h, ms) for h in N]; seen.update(c); cosets.append(c)
    others = [c for c in cosets if z not in c]
    for ch in itertools.product(*others):
        R = [z] + list(ch)
        if L.is_rds(R, N, ms, 3):
            D = L.indicator(R, ms) - L.indicator(N, ms)
            reps.setdefault(canon(D), []).append((sorted(N), R))
print("classes of R - N in C3 x C9:", len(reps), [len(v) for v in reps.values()])
_, _, O8 = L.load_obj(8)
c8 = canon(O8)
print("O8's class among them:", c8 in reps)
# all (27,10,1) SDS classes in C3 x C9 for context are E4's business; here only the R - N ones.
