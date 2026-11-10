"""C34 on every known set in objects/: for every odd prime p with p^2 | n, every factor si, every j <= v_p(m_si),
every divisor tuple d of the p'-parts with p^i = -1 mod lcm(d) (the quotients x_ma_divided tries; j = 1 included),
H = Z_{p^j} (from factor si) x prod Z_{d_t}; H' = Z_{p^(j-1)} x K. Check p | W on H' and every demand of Z = W/p.
Own code (numpy), no import from solver/. Also counts p = 2 quotients separately (outside C34)."""
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
def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]
stats = dict(objects=0, quotients=0, p2=0, bad=[])
for f in sorted(glob.glob(os.path.join(ROOT, "objects", "O*.txt")), key=lambda s: int(re.findall(r"O(\d+)", s)[-1])):
    lines = open(f, encoding="utf-8").read().split("\n")
    m = re.fullmatch(r"(\S+) \((\d+),(\d+),(-?\d+)\)", lines[0].strip())
    ms = [int(t[1:]) for t in m[1].split("x")]
    v, k, lam = int(m[2]), int(m[3]), int(m[4])
    D = np.zeros(ms, dtype=np.int64)
    for l in lines[1:]:
        if not l.strip(): continue
        *co, sg = l.split(); D[tuple(int(c) for c in co)] = 1 if sg == "+" else -1
    F = np.fft.fftn(D); ac = np.rint(np.fft.ifftn(F * np.conj(F)).real).astype(np.int64).reshape(-1)
    assert ac[0] == k and (ac[1:] == lam).all() and int((D != 0).sum()) == k, f
    stats["objects"] += 1
    s = int(D.sum()); assert s * s == k + lam * (v - 1)
    n = k - lam
    if n <= 0: continue
    idx = np.indices(ms).reshape(len(ms), -1)
    Dflat = D.reshape(-1)
    for p in primes(n):
        if vp(n, p) < 2: continue
        odd = [x // p ** vp(x, p) for x in ms]
        for si, msi in enumerate(ms):
            for j in range(1, vp(msi, p) + 1):
                r = p ** (j - 1)
                for d in itertools.product(*[divisors(x) for x in odd]):
                    L = math.lcm(*d)
                    if not selfconj(p, L): continue
                    if p == 2: stats["p2"] += 1; continue
                    # H' coordinates: (x_si mod r, x_t mod d_t)
                    shape = [r] + list(d)
                    coords = [idx[si] % r] + [idx[t] % d[t] for t in range(len(ms))]
                    lin = np.ravel_multi_index(coords, shape)
                    size = int(np.prod(shape))
                    W = np.bincount(lin, weights=Dflat, minlength=size).astype(np.int64)
                    c = v // (p * size); assert c * p * size == v
                    stats["quotients"] += 1
                    tag = (os.path.basename(f), p, j, si, d)
                    if (W % p).any(): stats["bad"].append((tag, "p does not divide W")); continue
                    Z = (W // p).reshape(shape)
                    Q = (k + lam * (p * c - 1)); t = lam * c
                    kk = k // p if (k // p - k) % 2 == 0 else k // p - 1
                    Fz = np.fft.fftn(Z); acz = np.rint(np.fft.ifftn(Fz * np.conj(Fz)).real).astype(np.int64).reshape(-1)
                    A = int(np.abs(Z).sum())
                    ok = (np.abs(Z).max() <= c and p * p * int((Z * Z).sum()) == Q and Q % (p * p) == 0
                          and t % p == 0 and (acz[1:] == t // p).all() and s % p == 0 and abs(int(Z.sum())) == abs(s) // p
                          and A <= kk and (kk - A) % 2 == 0 and k < p * (kk + 2) and (k - kk) % 2 == 0)
                    if not ok: stats["bad"].append((tag, "demand failed", A, kk, int(Z.sum()), s))
print(stats["objects"], "objects;", stats["quotients"], "odd-p Ma quotients tested;", stats["p2"], "p = 2 skipped;",
      "violations:", stats["bad"])
