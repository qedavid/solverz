"""Control for objects_c34.py: the same W test on quotients that break C34's hypotheses must sometimes fail.
(a) p not self-conjugate mod lcm(d); (b) K containing a factor of p (Sylow of H not cyclic): H' = Z_{p^(j-1)} x Z_p-part
of another factor; (c) b = 0 (p || n)."""
import re, sys, glob, os, math, itertools
import numpy as np
ROOT = sys.argv[1]
def vp(x, p):
    c = 0
    while x and x % p == 0: x //= p; c += 1
    return c
def primes(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    return out + ([n] if n > 1 else [])
def selfconj(p, m):
    if m == 1: return True
    x = p % m
    for _ in range(m + 1):
        if (x + 1) % m == 0: return True
        x = x * p % m
    return False
cnt = {"a": [0, 0], "b": [0, 0], "c": [0, 0]}
for f in glob.glob(os.path.join(ROOT, "objects", "O*.txt")):
    lines = open(f, encoding="utf-8").read().split("\n")
    m = re.fullmatch(r"(\S+) \((\d+),(\d+),(-?\d+)\)", lines[0].strip())
    ms = [int(t[1:]) for t in m[1].split("x")]
    v, k, lam = int(m[2]), int(m[3]), int(m[4])
    D = np.zeros(ms, dtype=np.int64)
    for l in lines[1:]:
        if not l.strip(): continue
        *co, sg = l.split(); D[tuple(int(c) for c in co)] = 1 if sg == "+" else -1
    n = k - lam
    if n <= 0: continue
    idx = np.indices(ms).reshape(len(ms), -1); Df = D.reshape(-1)
    def W(coords, shape):
        return np.bincount(np.ravel_multi_index(coords, shape), weights=Df, minlength=int(np.prod(shape))).astype(np.int64)
    for p in primes(v):
        if p == 2: continue
        for si, msi in enumerate(ms):
            if vp(msi, p) == 0: continue
            # (c) p | v, p^2 does not divide n: H = Z_p, H' trivial is the sum; use H = Z_{p} x (another factor's p'-part)
            if vp(n, p) < 2:
                cnt["c"][0] += 1; cnt["c"][1] += int(bool(W([idx[si] % 1], [1]) % p).any()) if False else int(D.sum() % p != 0)
            if vp(n, p) < 2: continue
            for t, mt in enumerate(ms):
                if t == si: continue
                if vp(mt, p) >= 1:  # (b) H = Z_p (si) x Z_p (t): contract to Z_p on t
                    w = W([idx[t] % p], [p]); cnt["b"][0] += 1; cnt["b"][1] += int((w % p).any())
                o = mt // p ** vp(mt, p)
                for dd in range(2, o + 1):
                    if o % dd or selfconj(p, dd): continue
                    w = W([idx[t] % dd], [dd]); cnt["a"][0] += 1; cnt["a"][1] += int((w % p).any())
print("control (tested, p does not divide W somewhere):", cnt)
