"""Independent C34 search (own code; no import from solver/): for a row (ms, k, lam), every C34 quotient (odd p, p^2 | n,
H = Z_{p^j} from factor si (j <= v_p(m_si)) x prod Z_{d_t}, d_t | p'-part of m_t, p^i = -1 mod lcm d), H' = Z_{p^(j-1)} x K.
Per quotient: 'arith' (demands not integral), 'profile' (no value multiset fits N, sum, square sum, abs bound/parity),
'kill' (every arrangement of every profile, Z(0) fixed by translation, fails the autocorrelation), 'found', or 'big'.
Different method from x_ma_divided (coordinate DFS): profiles first, then placements."""
import math, itertools, sys
from profiles import profiles, arrangements
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
def quotients(ms, k, lam):
    v, n = math.prod(ms), k - lam
    if n <= 0: return
    for p in primes(n):
        if p == 2 or vp(n, p) < 2: continue
        odd = [x // p ** vp(x, p) for x in ms]
        seen = set()
        for si, m in enumerate(ms):
            for j in range(1, vp(m, p) + 1):
                for d in itertools.product(*[[q for q in range(1, x + 1) if x % q == 0] for x in odd]):
                    if not selfconj(p, math.lcm(*d)): continue
                    e = list(d); e[si] *= p ** (j - 1)
                    if (p, tuple(e)) in seen: continue
                    seen.add((p, tuple(e)))
                    yield p, j, e
def search(shape, c, Q, t, s, kp, limit):
    N = math.prod(shape)
    profs = profiles(N, c, Q, s, kp)
    if not profs: return "profile", 0
    if sum(arrangements(N, pr) for pr in profs) > limit: return "big", 0
    elems = list(itertools.product(*[range(x) for x in shape]))
    idx = {e: i for i, e in enumerate(elems)}
    add = [[idx[tuple((a + b) % m for a, b, m in zip(x, g, shape))] for x in elems] for g in elems]
    leaves = 0
    for pr in profs:
        a0 = min(pr, key=lambda a: pr[a])  # Z(0) = a0 by translation
        cnt = dict(pr); cnt[a0] -= 1
        Z = [None] * N; Z[0] = a0
        vals = sorted(cnt)
        def rec(pos):
            nonlocal leaves
            if pos == N:
                leaves += 1
                return all(sum(Z[x] * Z[add[g][x]] for x in range(N)) == t for g in range(1, N))
            for a in vals:
                if cnt[a]:
                    cnt[a] -= 1; Z[pos] = a
                    if rec(pos + 1): return True
                    cnt[a] += 1
            return False
        if rec(1): return "found", leaves
    return "kill", leaves
def row(ms, k, lam, limit=300000, stop=True):
    v = math.prod(ms)
    s = math.isqrt(k + lam * (v - 1))
    out = []
    for p, j, e in quotients(ms, k, lam):
        N = math.prod(e); c = v // (p * N); num = k + lam * (p * c - 1)
        if num % (p * p) or (lam * c) % p or s % p or s * s != k + lam * (v - 1):
            out.append((p, j, e, "arith", 0))
        else:
            kp = k // p if (k // p - k) % 2 == 0 else k // p - 1
            res = search(e, c, num // (p * p), lam * c // p, s // p, kp, limit) if kp >= 0 else ("kneg", 0)
            out.append((p, j, e) + res)
        if stop and out[-1][3] in ("arith", "profile", "kill", "kneg"): break
    return out
if __name__ == "__main__":
    print(row([int(x) for x in sys.argv[1].split(",")], int(sys.argv[2]), int(sys.argv[3]), stop=False))
