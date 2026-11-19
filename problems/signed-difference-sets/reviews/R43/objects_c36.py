"""C36 on every known set in objects/: every prime p, every surjection G -> Z_{p^j} x K (j >= 2) of the form
x -> (sum_t g_t x_t mod p^j, (x_t mod d_t)_t) with images g_t (all hom images, not only coordinate projections; surjective
onto Z_{p^j} iff some g_t is a unit after scaling - checked by image size), d_t | p'-part of m_t, p^i = -1 mod lcm(d).
Checks with b = floor(v_p(n)/2): (i) Ma step Y(h+u) = Y(h) mod p^b; (ii) W1 = p Y mod p^b; (iii) W2 = p W1 mod p^b;
(iv) p^2 | W2; (v) every demand of Z = W2/p^2 and the bounds list; and for b >= 3 also p^3 | W3 (three levels).
b >= 2 is C36; b = 1 rows are the control (p^2 | W2 not claimed). Own code (numpy)."""
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
st = dict(objects=0, c36=0, c36_bad=[], ctrl=0, ctrl_fail=0, lvl3=0, lvl3_bad=0, byp={})
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
    st["objects"] += 1
    s = int(D.sum()); assert s * s == k + lam * (v - 1)
    n = k - lam
    if n <= 0: continue
    idx = np.indices(ms).reshape(len(ms), -1)
    Df = D.reshape(-1)
    for p in primes(n):
        e = vp(n, p); b = e // 2
        if b < 1: continue
        odd = [x // p ** vp(x, p) for x in ms]
        J = max(vp(x, p) for x in ms)
        for j in range(2, J + 1):
            N = p ** j
            # all hom images g_t in Z_N with m_t g_t = 0 mod N, surjective: gcd(g, N) generates
            choices = [[g for g in range(N) if (mt * g) % N == 0] for mt in ms]
            seen = set()
            for g in itertools.product(*choices):
                if math.gcd(math.gcd(*g), N) != 1 if len(g) > 1 else math.gcd(g[0], N) != 1: continue
                for d in itertools.product(*[divisors(x) for x in odd]):
                    if not selfconj(p, math.lcm(*d)): continue
                    a0 = (sum(gt * idx[t] for t, gt in enumerate(g)) % N)
                    key = (p, j, d, tuple(a0[:min(len(a0), 4096)].tolist()))
                    if key in seen: continue
                    seen.add(key)
                    K = int(np.prod(d)); c = v // (N * K)
                    kc = [idx[t] % d[t] for t in range(len(ms))]
                    kin = np.ravel_multi_index(kc, d) if len(d) else np.zeros_like(a0)
                    def lvl(l):  # coset sums on Z_{p^(j-l)} x K, as array [p^(j-l), K]
                        M = p ** (j - l)
                        W = np.zeros((M, K), dtype=np.int64)
                        np.add.at(W, (a0 % M, kin), Df)
                        return W
                    Y, W1, W2 = lvl(0), lvl(1), lvl(2)
                    pb = p ** b
                    r1 = N // p
                    ok_i = ((np.roll(Y, -r1, axis=0) - Y) % pb == 0).all()
                    ok_ii = all(((W1[x % (N // p)] - p * Y[x]) % pb == 0).all() for x in range(N))
                    ok_iii = all(((W2[x % (N // p // p)] - p * W1[x]) % pb == 0).all() for x in range(N // p))
                    div2 = (W2 % (p * p) == 0).all()
                    if b >= 2:
                        st["c36"] += 1; st["byp"][p] = st["byp"].get(p, 0) + 1
                        bad = []
                        if not ok_i: bad.append("ma-step")
                        if not ok_ii: bad.append("W1=pY")
                        if not ok_iii: bad.append("W2=pW1")
                        if not div2: bad.append("p2|W2")
                        else:
                            Z = (W2 // (p * p)).reshape(-1); Hs = Z.size
                            Q = (k + lam * (p * p * c - 1)); t = lam * c
                            Zm = Z.reshape(W2.shape)
                            Fz = np.fft.fftn(Zm); acz = np.rint(np.fft.ifftn(Fz * np.conj(Fz)).real).astype(np.int64).reshape(-1)
                            A = int(np.abs(Z).sum())
                            k0 = k // (p * p)
                            bounds = [k0, k0 - 1] if p == 2 else [k0 if (k0 - k) % 2 == 0 else k0 - 1]
                            if not (np.abs(Z) <= c).all(): bad.append("|Z|<=c")
                            if Q % p ** 4 or acz[0] * p ** 4 != Q: bad.append("Q")
                            if t % (p * p) or Hs > 1 and (acz[1:] * p * p != t).any(): bad.append("t")
                            if s % (p * p) or abs(int(Z.sum())) * p * p != abs(s): bad.append("sum")
                            if p * p * A > k or (k - p * p * A) % 2: bad.append("abs")
                            if not any(A <= kk and (kk - A) % 2 == 0 for kk in bounds if kk >= 0): bad.append("bounds")
                        if bad: st["c36_bad"].append((os.path.basename(f), m[1], p, j, g, d, bad))
                        if b >= 3 and j >= 3:
                            st["lvl3"] += 1
                            if not (lvl(3) % p ** 3 == 0).all(): st["lvl3_bad"] += 1
                    else:
                        st["ctrl"] += 1
                        if not div2: st["ctrl_fail"] += 1
print({k_: (v_ if k_ != "c36_bad" else len(v_)) for k_, v_ in st.items()})
for x in st["c36_bad"][:20]: print("BAD", x)
