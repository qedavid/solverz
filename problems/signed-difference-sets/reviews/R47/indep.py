"""Independent recomputation of C41 verdicts (own enumeration, own lines, meet in the middle). No code from
tomoquot.py / tomorows.py / Rust explorers."""
import math, sys, itertools
import numpy as np

def orbits(p, t):
    seen, orbs = set(), []
    for h in range(p):
        if h in seen: continue
        o, x = [], h
        while x not in o:
            o.append(x); x = x * t % p
        seen.update(o); orbs.append(o)
    return orbs

def valid(b, p, C, k, lam, s):
    if any(abs(x) > C for x in b): return False
    if sum(b) != s: return False
    if sum(x * x for x in b) != k + lam * (C - 1): return False
    for g in range(1, p):
        if sum(b[h] * b[(h + g) % p] for h in range(p)) != lam * C: return False
    a = sum(abs(x) for x in b)
    return a <= k and (k - a) % 2 == 0

def enum_vectors(p, C, k, lam, s, t=1):
    """All b : Z_p -> Z constant on <t>-orbits meeting the demands (fibres C) with sum s."""
    Q = k + lam * (C - 1)
    orbs = orbits(p, t)
    # order: put two equal-size orbits last if possible
    orbs.sort(key=lambda o: len(o))
    m = len(orbs)
    sizes = [len(o) for o in orbs]
    out = []
    def finish(vals):
        b = [0] * p
        for o, x in zip(orbs, vals):
            for h in o: b[h] = x
        if valid(b, p, C, k, lam, s): out.append(tuple(b))
    if m <= 2:
        for vals in itertools.product(range(-C, C + 1), repeat=m):
            if sum(z * x for z, x in zip(sizes, vals)) == s: finish(vals)
        return sorted(set(out))
    assert sizes[-1] == sizes[-2]
    z = sizes[-1]
    rng = np.arange(-C, C + 1, dtype=np.int64)
    def rec(i, vals, sm, sq):
        if i == m - 3:
            # vectorise orbit m-3, solve m-2, m-1
            zi = sizes[i]
            L = s - sm - zi * rng
            R = Q - sq - zi * rng * rng
            ok = (L % z == 0) & (R % z == 0) & (R >= 0)
            Lz = np.where(ok, L // z, 0); Rz = np.where(ok, R // z, 0)
            D = 2 * Rz - Lz * Lz
            ok &= D >= 0
            d = np.where(ok, np.floor(np.sqrt(np.maximum(D, 0))).astype(np.int64), 0)
            for adj in (-1, 0, 1):
                dd = d + adj
                ok2 = ok & (dd >= 0) & (dd * dd == D) & ((Lz + dd) % 2 == 0)
                for idx in np.nonzero(ok2)[0]:
                    x = int(rng[idx]); a = int((Lz[idx] + dd[idx]) // 2); bb = int((Lz[idx] - dd[idx]) // 2)
                    for (u, w) in ((a, bb), (bb, a)):
                        if abs(u) <= C and abs(w) <= C:
                            finish(vals + [x, u, w])
            return
        zi = sizes[i]
        for x in range(-C, C + 1):
            q2 = sq + zi * x * x
            if q2 > Q: continue
            rec(i + 1, vals + [x], sm + zi * x, q2)
    rec(0, [], 0, 0)
    return sorted(set(out))

def moment0(b, p):
    return sum(h * x for h, x in enumerate(b)) % p == 0

def line_index(p):
    """idx[L][g] = image of point g = (a, b) (g = a*p + b) under my line map L: a + m b (m < p), b (m = p)."""
    idx = np.zeros((p + 1, p * p), dtype=np.int64)
    for a in range(p):
        for b in range(p):
            g = a * p + b
            for m in range(p): idx[m][g] = (a + m * b) % p
            idx[p][g] = b
    return idx

def choices(p, s, c, W, limit=None):
    """All (p+1)-tuples from W with every sum - s = p z, |z| <= c; returns (n_integral, n_box, example)."""
    W = [np.array(w, dtype=np.int64) for w in W]
    if not W: return 0, 0, None
    idx = line_index(p)
    nW = len(W)
    h1 = (p + 1) // 2
    L1, L2 = list(range(h1)), list(range(h1, p + 1))
    def partial(lines):
        tuples = list(itertools.product(range(nW), repeat=len(lines)))
        P = np.zeros((len(tuples), p * p), dtype=np.int64)
        for ti, tup in enumerate(tuples):
            for L, wi in zip(lines, tup): P[ti] += W[wi][idx[L]]
        return tuples, P
    T1, P1 = partial(L1)
    T2, P2 = partial(L2)
    rng = np.random.default_rng(12345)
    coef = rng.integers(1, 2**61, size=p * p, dtype=np.int64)
    def h(R):
        return (np.mod(R, p).astype(np.uint64) * coef.astype(np.uint64)).sum(axis=1)
    H1 = h(P1)
    H2 = h(np.mod(s - P2, p))
    order = np.argsort(H1)
    H1s = H1[order]
    nint = nbox = 0
    ex = None
    for j in range(len(T2)):
        lo = np.searchsorted(H1s, H2[j], 'left'); hi = np.searchsorted(H1s, H2[j], 'right')
        for ii in order[lo:hi]:
            S = P1[ii] + P2[j] - s
            if np.all(S % p == 0):
                nint += 1
                if np.all(np.abs(S) <= p * c):
                    nbox += 1
                    if ex is None: ex = (T1[ii], T2[j], (S // p).tolist())
    return nint, nbox, ex

def origin_residues(p, s, W):
    vals = sorted(set(w[0] % p for w in W))
    reach = {0}
    for _ in range(p + 1):
        reach = {(r + v) % p for r in reach for v in vals}
    return vals, (s % p) in reach
