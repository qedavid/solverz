"""Every object in objects/: verify it is an SDS (FFT autocorrelation), then test C33 on it: for each prime p with
p^2 | n and each cyclic quotient Z_{p^j} (j >= 2) of each cyclic factor, the coset sums Y satisfy Ma's step
Y(h + p^{j-1}) = Y(h) mod p^b and p | lam * c (c = v / p^j); also the corollary (cyclic Sylow of order >= p^2 => p | lam)."""
import re, sys, glob, os
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
tested, cor_tested, bad = 0, 0, []
for f in sorted(glob.glob(os.path.join(ROOT, "objects", "O*.txt")), key=lambda s: int(re.findall(r"O(\d+)", s)[-1])):
    lines = open(f, encoding="utf-8").read().split("\n")
    m = re.fullmatch(r"(\S+) \((\d+),(\d+),(-?\d+)\)", lines[0].strip())
    ms = [int(t[1:]) for t in m[1].split("x")]
    v, k, lam = int(m[2]), int(m[3]), int(m[4])
    D = np.zeros(ms, dtype=np.int64)
    for l in lines[1:]:
        if not l.strip(): continue
        *co, s = l.split(); D[tuple(int(c) for c in co)] = 1 if s == "+" else -1
    assert int(np.prod(ms)) == v and int((D != 0).sum()) == k, f
    F = np.fft.fftn(D); ac = np.rint(np.fft.ifftn(F * np.conj(F)).real).astype(np.int64)
    flat = ac.reshape(-1)
    if not (flat[0] == k and (flat[1:] == lam).all()): bad.append((f, "not an SDS")); continue
    n = k - lam
    for p in (primes(n) if n > 0 else []):
        if n % (p * p): continue
        b = vp(n, p) // 2
        divs = [t for t, x in enumerate(ms) if x % p == 0]
        if len(divs) == 1 and vp(v, p) >= 2:
            cor_tested += 1
            if lam % p: bad.append((f, "corollary violated", p))
        for s, mm in enumerate(ms):
            for j in range(2, vp(mm, p) + 1):
                q = p ** j
                idx = np.indices(ms)[s] % q
                Y = np.bincount(idx.reshape(-1), weights=D.reshape(-1), minlength=q).astype(np.int64)
                tested += 1
                if ((np.roll(Y, -(q // p)) - Y) % p ** b).any(): bad.append((f, "Ma step", p, j, Y.tolist()))
                if (lam * (v // q)) % p: bad.append((f, "p | lam c violated", p, j))
print("objects:", len(glob.glob(os.path.join(ROOT, "objects", "O*.txt"))), " (p, Z_{p^j}) quotients tested:", tested,
      " corollary cases (cyclic Sylow >= p^2, p^2 | n):", cor_tested, " problems:", bad)
