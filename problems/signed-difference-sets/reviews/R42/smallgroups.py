"""Every SDS (any k, lam with n = k - lam > 0) on small abelian groups, by exhaustive enumeration of {0,+-1}^G;
for each, every C34 quotient (odd p, p^2 | n, H = Z_{p^j} (one factor) x K, p self-conjugate mod lcm K) and every
demand of Z = W/p. Own code."""
import sys, math, itertools
import numpy as np
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
def run(ms):
    v = math.prod(ms)
    elems = list(itertools.product(*[range(m) for m in ms]))
    index = {e: i for i, e in enumerate(elems)}
    shifts = [[index[tuple((a + b) % m for a, b, m in zip(x, g, ms))] for x in elems] for g in elems]
    found, tested, bad = 0, 0, []
    # enumerate all vectors in chunks of 3^(v-6) * 729 via mixed radix
    N = 3 ** v
    chunk = 3 ** min(v, 12)
    for start in range(0, N, chunk):
        ids = np.arange(start, min(N, start + chunk), dtype=np.int64)
        X = np.empty((len(ids), v), dtype=np.int8)
        t = ids.copy()
        for i in range(v):
            X[:, i] = (t % 3) - 1; t //= 3
        Xi = X.astype(np.int32)
        k = (Xi != 0).sum(1)
        ac1 = (Xi * Xi[:, shifts[1]]).sum(1)
        good = np.ones(len(ids), bool)
        for g in range(2, v):
            good &= (Xi * Xi[:, shifts[g]]).sum(1) == ac1
        good &= (k - ac1) > 0
        for row in np.nonzero(good)[0]:
            D = Xi[row]; kk_, lam = int(k[row]), int(ac1[row]); n = kk_ - lam; s = int(D.sum())
            found += 1
            for p in primes(n):
                if p == 2 or vp(n, p) < 2: continue
                odd = [x // p ** vp(x, p) for x in ms]
                for si, msi in enumerate(ms):
                    for j in range(1, vp(msi, p) + 1):
                        r = p ** (j - 1)
                        for d in itertools.product(*[[q for q in range(1, x + 1) if x % q == 0] for x in odd]):
                            if not selfconj(p, math.lcm(*d)): continue
                            shape = [r] + list(d); size = math.prod(shape)
                            W = np.zeros(size, np.int64)
                            for e, val in zip(elems, D):
                                W[np.ravel_multi_index([e[si] % r] + [e[t] % d[t] for t in range(len(ms))], shape)] += val
                            c = v // (p * size); tested += 1
                            if (W % p).any(): bad.append((ms, kk_, lam, p, j, d, "W")); continue
                            Z = W // p
                            Zs = Z.reshape(shape)
                            ok = abs(Z).max() <= c and p * p * int((Z * Z).sum()) == kk_ + lam * (p * c - 1)
                            kp = kk_ // p if (kk_ // p - kk_) % 2 == 0 else kk_ // p - 1
                            A = int(abs(Z).sum())
                            ok = ok and A <= kp and (kp - A) % 2 == 0 and p * abs(int(Z.sum())) == abs(s)
                            for g in itertools.product(*[range(x) for x in shape]):
                                if not any(g): continue
                                sh = np.roll(Zs, [-x for x in g], axis=tuple(range(len(shape))))
                                ok = ok and p * int((Zs * sh).sum()) == lam * c
                            if not ok: bad.append((ms, kk_, lam, p, j, d, "demand"))
    print(ms, "SDS found:", found, " C34 quotients tested:", tested, " violations:", bad[:5], flush=True)
for ms in [[3], [6], [9], [3, 3], [12], [2, 6], [15], [3, 4], [18], [3, 6], [5, 5], [7, 2], [21]][: int(sys.argv[1])]:
    if math.prod(ms) <= 15: run(ms)
