"""Check 1, part 2: is each of O40-O58 a translate (and possibly negation) of R - N, G - R - N (semiregular R),
G - 2R - N or G - R - 2N (affine R), with R an RDS relative to a subgroup N of order n?"""
import numpy as np, itertools
import sdslib as L

def as_set(D, val):
    return [tuple(int(t) for t in x) for x in np.argwhere(D == val)]

def sub(S, x, ms):
    return [L.add(s, L.neg(x, ms), ms) for s in S]

def is_subgroup(S, ms):
    S = set(S); z = (0,) * len(ms)
    return z in S and all(L.add(a, b, ms) in S for a in S for b in S)

def try_semi_RminusN(D, ms, n):
    plus, minus, zeros = as_set(D, 1), as_set(D, -1), as_set(D, 0)
    if len(minus) != n - 1: return None
    for x in zeros:
        N = sub(minus, x, ms) + [(0,) * len(ms)]
        if not is_subgroup(N, ms): continue
        R = sub(plus, x, ms) + [(0,) * len(ms)]
        if len(R) == n * n and L.is_rds(R, N, ms, n):
            return ("R-N", x, sorted(N))
    return None

def try_semi_GmRmN(D, ms, n):
    minus, zeros = as_set(D, -1), as_set(D, 0)
    if len(minus) != 1: return None
    x = minus[0]
    Z = set(sub(zeros, x, ms)) | {(0,) * len(ms)}
    for N in L.subgroups_of_order(ms, n):
        if not set(N) <= Z: continue
        R = sorted((Z - set(N)) | {(0,) * len(ms)})
        if len(R) == n * n and L.is_rds(R, N, ms, n):
            return ("G-R-N", x, sorted(N))
    return None

def cyclic_affine(D, v, n, q, kind):
    ms = (v,)
    N = [(i * (v // n),) for i in range(n)]
    if kind == "a":   # -1 on R, 0 on N, +1 elsewhere
        Rv, Nv = as_set(D, -1), as_set(D, 0)
    else:             # 0 on R, -1 on N
        Rv, Nv = as_set(D, 0), as_set(D, -1)
    if len(Nv) != n or len(Rv) != q: return None
    x = Nv[0]
    if sorted(sub(Nv, x, ms)) != sorted(N): return None
    R = sub(Rv, x, ms)
    if set(R) & set(N): return None
    return ("G-2R-N" if kind == "a" else "G-R-2N", x, L.is_rds(R, N, ms, (q - 1) // n))

nmap = {125: 5, 343: 7, 64: 4}
for i in range(40, 57):
    ms, par, D = L.load_obj(i)
    n = nmap[par[0]]
    res = None
    for sgn in (1, -1):
        for f in (try_semi_RminusN, try_semi_GmRmN):
            r = f(sgn * D, ms, n)
            if r: res = (sgn,) + r; break
        if res: break
    print(f"O{i} {ms} {par}: {res}", flush=True)
for i, n, q, kind in [(57, 12, 25, "a"), (58, 5, 81, "b")]:
    ms, par, D = L.load_obj(i)
    res = None
    for sgn in (1, -1):
        r = cyclic_affine(sgn * D, par[0], n, q, kind)
        if r: res = (sgn,) + r; break
    print(f"O{i} {ms} {par}: {res}", flush=True)
