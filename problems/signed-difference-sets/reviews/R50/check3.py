"""Check 3 (C45): independent search, no congruences assumed. On K = Z_3^2: all z (sum +s, autocorr n*delta + 10*lam,
|z| <= 10) and all d (sum +-sqrt(n), autocorr n*delta, |d| <= 10); pairs with W = (z +- d)/2 integral, |W| <= 5,
sum |W| <= k (parity k), and W's autocorrelation on Z_2 x Z_3^2 (n*delta + 5*lam)."""
import numpy as np, itertools, math, sys
B = 10
def vecs(L, B):
    g = np.array(list(itertools.product(range(-B, B + 1), repeat=L)), dtype=np.int16) if L <= 4 else None
    return g
def all_with(S, Q):
    A = np.array(list(itertools.product(range(-B, B + 1), repeat=4)), dtype=np.int32)
    vals = np.arange(-B, B + 1)
    Bm = np.array(np.meshgrid(*([vals] * 5), indexing="ij"), dtype=np.int32).reshape(5, -1).T
    ka = {}
    sa, qa = A.sum(1), (A * A).sum(1)
    sb, qb = Bm.sum(1), (Bm * Bm).sum(1)
    keyb = {}
    order = np.lexsort((qb, sb)); sbs, qbs = sb[order], qb[order]
    out = []
    for key in set(zip(sa.tolist(), qa.tolist())):
        s1, q1 = key
        s2, q2 = S - s1, Q - q1
        if q2 < 0: continue
        lo = np.searchsorted(sbs * 100000 + qbs, s2 * 100000 + q2, "left")
        hi = np.searchsorted(sbs * 100000 + qbs, s2 * 100000 + q2, "right")
        if lo == hi: continue
        ia = np.nonzero((sa == s1) & (qa == q1))[0]
        ib = order[lo:hi]
        out.append(np.hstack([np.repeat(A[ia], len(ib), 0), np.tile(Bm[ib], (len(ia), 1))]))
    return np.vstack(out) if out else np.zeros((0, 9), np.int32)
K = [(a, b) for a in range(3) for b in range(3)]
perm = {g: np.array([K.index(((a + g[0]) % 3, (b + g[1]) % 3)) for (a, b) in K]) for g in K}
def autoc_ok(V, mu):
    ok = np.ones(len(V), bool)
    for g in K[1:]:
        ok &= (V * V[:, perm[g]]).sum(1) == mu
    return V[ok]
G2 = [(e, a, b) for e in range(2) for a in range(3) for b in range(3)]
def W_autoc(W):  # W: dict over Z_2 x Z_3^2 -> list of autocorr at nonzero g
    return [sum(W[x] * W[((x[0] + g[0]) % 2, (x[1] + g[1]) % 3, (x[2] + g[2]) % 3)] for x in G2) for g in G2[1:]]
for name, v, k, lam in (("N1575", 90, 18, 2), ("N1593", 90, 72, 8)):
    n = k - lam; s = math.isqrt(k + lam * (v - 1)); r = math.isqrt(n)
    Z = autoc_ok(all_with(s, n + 10 * lam), 10 * lam)
    Dd = np.vstack([autoc_ok(all_with(sg * r, n), 0) for sg in (1, -1)])
    print(name, "s", s, "#z", len(Z), "#d", len(Dd), "z residues mod 2^j:", sorted({int(x) % (4 if n == 16 else 8) for x in Z.ravel()}),
          "d residues:", sorted({int(x) % (4 if n == 16 else 8) for x in Dd.ravel()}), flush=True)
    integral = box = absok = full = 0; minabs = None
    for z in Z:
        P = Dd[np.all((Dd - z) % 2 == 0, axis=1)]
        if not len(P): continue
        integral += len(P)
        Wp, Wm = (z + P) // 2, (z - P) // 2
        mx = np.maximum(np.abs(Wp).max(1), np.abs(Wm).max(1))
        sab = np.abs(Wp).sum(1) + np.abs(Wm).sum(1)
        box += int((mx <= 5).sum())
        sel = (mx <= 5) & (sab <= k) & ((sab - k) % 2 == 0)
        absok += int(sel.sum())
        m = sab[mx <= 5]
        if len(m): minabs = int(m.min()) if minabs is None else min(minabs, int(m.min()))
        for i in np.nonzero(sel)[0]:
            W = {}
            for j, (a, b) in enumerate(K):
                W[(0, a, b)] = int(Wp[i, j]); W[(1, a, b)] = int(Wm[i, j])
            if all(x == 5 * lam for x in W_autoc(W)): full += 1
    print(name, "pairs with W integral", integral, "with |W|<=5", box, "min sum|W| among those", minabs,
          "also sum|W|<=k", absok, "W autocorr ok", full, flush=True)
