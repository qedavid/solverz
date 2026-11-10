"""Independent line-tomography check on Z_p x Z_p (refuter, C40). Own code: no import of
tomorows.py / tomo2.py / x_tomography. Usage: python indep.py p k lam [orbit] [full]
 - V: every Y in Z^p with |Y|<=p, sum s, sum sq Q=k+lam(p-1), every cyclic shift corr lam*p,
   sum|Y|<=k, k-sum|Y| even (DFS over all coordinates, no translation normalisation).
 - orbit: also enumerate W_fix = {Y constant on <n>-orbits of Z_p, first moment 0} directly.
 - search: exists one W-vector per line (functionals (1,m), m=0..p-1, and (0,1)) with every
   sum_j Y_j(phi_j g) - s == 0 mod p (int) and in {0,+-p} (sds)? meet in the middle."""
import sys, math, itertools
from collections import defaultdict

def isprime(n):
    return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))

def demands_ok(Y, p, k, lam, s):
    Q = k + lam * (p - 1)
    if sum(Y) != s or sum(y * y for y in Y) != Q: return False
    if any(abs(y) > p for y in Y): return False
    a = sum(abs(y) for y in Y)
    if a > k or (k - a) % 2: return False
    for g in range(1, p):
        if sum(Y[x] * Y[(x + g) % p] for x in range(p)) != lam * p: return False
    return True

def enum_V(p, k, lam, s):
    Q = k + lam * (p - 1)
    out = []
    Y = [0] * p
    def dfs(i, sm, sq):
        rem = p - i
        if rem == 0:
            if sm == s and sq == Q and demands_ok(Y, p, k, lam, s): out.append(tuple(Y))
            return
        # remaining coords must give sum s-sm, squares Q-sq: (s-sm)^2 <= rem*(Q-sq)
        R = Q - sq
        if R < 0 or (s - sm) ** 2 > rem * R or abs(s - sm) > rem * p: return
        lim = min(p, math.isqrt(R))
        for x in range(-lim, lim + 1):
            Y[i] = x
            dfs(i + 1, sm + x, sq + x * x)
        Y[i] = 0
    dfs(0, 0, 0)
    return out

def m1(Y, p):
    return sum(t * y for t, y in enumerate(Y)) % p

def orbits(p, n):
    seen, orbs = set(), [[0]]
    seen.add(0)
    for h in range(1, p):
        if h in seen: continue
        o, x = [], h
        while x not in o:
            o.append(x); x = x * n % p
        seen.update(o); orbs.append(o)
    return orbs

def enum_Wfix(p, k, lam, s, n):
    orbs = orbits(p, n)
    out = []
    for vals in itertools.product(range(-p, p + 1), repeat=len(orbs)):
        Y = [0] * p
        for o, v in zip(orbs, vals):
            for h in o: Y[h] = v
        if demands_ok(Y, p, k, lam, s) and m1(Y, p) == 0: out.append(tuple(Y))
    return out, orbs

def functionals(p):
    return [(1, m) for m in range(p)] + [(0, 1)]

def search(p, s, W, exact_D=True):
    """All choices (one W-index per line) with every line sum - s = 0 mod p; then filter to
    {0, +-p}. numpy meet in the middle over two halves of the lines."""
    import numpy as np
    F = functionals(p)
    pts = [(a, b) for a in range(p) for b in range(p)]
    L = len(F); m = len(W)
    Wa = np.array(W, dtype=np.int64)
    contrib = np.stack([Wa[:, [(u * a + w * b) % p for (a, b) in pts]] for (u, w) in F])  # L,m,P
    def half(lines):
        tot = np.zeros((1, len(pts)), dtype=np.int64)
        for j in lines:
            tot = (tot[:, None, :] + contrib[j][None, :, :]).reshape(-1, len(pts))
        return tot  # index = mixed radix over lines, first line most significant
    h1 = L // 2
    A = half(range(h1)); B = half(range(h1, L))
    rng = np.random.default_rng(1)
    coef = rng.integers(1, 2**61, size=len(pts), dtype=np.int64)
    ka = ((A % p) * coef).sum(axis=1)
    kb = (((s - B) % p) * coef).sum(axis=1)
    order = np.argsort(ka); ks = ka[order]
    lo = np.searchsorted(ks, kb, 'left'); hi = np.searchsorted(ks, kb, 'right')
    n_int = n_sds = 0; ex = None
    for bi in np.nonzero(hi > lo)[0]:
        for ai in order[lo[bi]:hi[bi]]:
            tot = A[ai] + B[bi] - s
            if np.any(tot % p): continue
            n_int += 1
            vals = tot // p
            if np.all(np.abs(vals) <= 1):
                n_sds += 1
                if ex is None: ex = ((int(ai), int(bi)), [int(v) for v in vals])
    return n_int, n_sds, ex, pts

def check_sds(p, k, lam, D, pts):
    Dm = {pt: D[i] for i, pt in enumerate(pts)}
    if sum(1 for v in D if v) != k: return False
    for g in pts:
        if g == (0, 0): continue
        c = sum(Dm[x] * Dm[((x[0] + g[0]) % p, (x[1] + g[1]) % p)] for x in pts)
        if c != lam: return False
    return True

def main():
    p, k, lam = map(int, sys.argv[1:4])
    opts = sys.argv[4:]
    s2 = k + lam * (p * p - 1)
    s = math.isqrt(s2)
    assert s * s == s2, "s^2 not a square"
    print(f"p={p} k={k} lam={lam} s={s} p|s={s % p == 0} n={k - lam}")
    if 'orbit' in opts:
        n = k - lam
        assert isprime(n) and n % p not in (0, 1)
        W, orbs = enum_Wfix(p, k, lam, s, n)
        print(f"orbit route: orbits {len(orbs)} |Wfix|={len(W)} {W}")
    if 'full' in opts or 'orbit' not in opts:
        V = enum_V(p, k, lam, s)
        Wf = [Y for Y in V if m1(Y, p) == 0]
        print(f"full: |V|={len(V)} |W|={len(Wf)} {Wf if len(Wf) <= 12 else ''}")
        if 'orbit' in opts:
            n = k - lam
            fixed = [Y for Y in Wf if all(Y[h * n % p] == Y[h] for h in range(p))]
            print(f"full W fixed by n: {len(fixed)} equal to Wfix: {sorted(fixed) == sorted(W)}")
            print(f"full W not fixed by n: {len(Wf) - len(fixed)}")
        if 'orbit' not in opts or 'searchfull' in opts: W = Wf
    if len(W) == 0:
        print("VERDICT: KILLED (W empty)"); return
    n_int, n_sds, ex, pts = search(p, s, W)
    print(f"integral choices {n_int}, SDS choices {n_sds}")
    if ex:
        D = ex[1]
        print("example D valid SDS:", check_sds(p, k, lam, D, pts))
    print("VERDICT:", "FOUND" if n_sds else "KILLED")

main()
