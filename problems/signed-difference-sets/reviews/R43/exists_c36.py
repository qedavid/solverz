"""Own enumeration of C36 level-2 quotients (any p with b >= 2, factor si, 2 <= j <= v_p(m_si), divisor tuples d of the
p'-parts with p^i = -1 mod lcm d; H'' = Z_{p^(j-2)} x prod Z_{d_t}) on rows of instances.csv with the given status; the arithmetic
demands, the value multisets and (capped) arrangements. Prints per quotient: arith-fail / no-multiset / found / none / cut."""
import csv, re, sys, math, itertools, random
from multisets import multisets
from arrange import search
ROOT, STATUS = sys.argv[1], sys.argv[2]
CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
ONLY = set(sys.argv[4].split(",")) if len(sys.argv) > 4 else None
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
def inv_factors(ns):
    pw = {}
    for n in ns:
        for q in primes(n): pw.setdefault(q, []).append(q ** vp(n, q))
    L = max((len(v) for v in pw.values()), default=0); out = [1] * L
    for q, v in pw.items():
        v.sort(reverse=True)
        for i, x in enumerate(v): out[L - 1 - i] *= x
    return out
from collections import Counter
tally = Counter()
for r in csv.DictReader(open(f"{ROOT}/instances.csv", encoding="utf-8")):
    if r["status"] != STATUS or (ONLY and r["id"] not in ONLY): continue
    m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", r["key"])
    v, k, lam = int(m[1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(",")]
    n = k - lam; tot = k + lam * (v - 1)
    if n <= 0 or tot < 0 or math.isqrt(tot) ** 2 != tot: continue
    s = math.isqrt(tot)
    seen = set()
    for p in primes(n):
        b = vp(n, p) // 2
        if b < 2: continue
        odd = [x // p ** vp(x, p) for x in ms]
        for si, msi in enumerate(ms):
            for j in range(2, vp(msi, p) + 1):
                for d in itertools.product(*[divisors(x) for x in odd]):
                    if not selfconj(p, math.lcm(*d)): continue
                    Hs = inv_factors([p ** (j - 2)] + list(d))
                    if (p, tuple(Hs)) in seen: continue
                    seen.add((p, tuple(Hs)))
                    size = p ** (j - 2) * math.prod(d); c = v // (p ** j * math.prod(d))
                    num = k + lam * (p * p * c - 1)
                    if num % p ** 4 or (lam * c) % (p * p) or s % (p * p):
                        res = "arith"
                    else:
                        Q, t, s1 = num // p ** 4, lam * c // (p * p), s // (p * p)
                        par = None if p == 2 else k % 2
                        MS = multisets(size, c, s1, Q, k // (p * p), par)
                        if not MS: res = "nomultiset"
                        elif size == 1: res = "found"
                        else:
                            shape = [x for x in Hs if x > 1] or [1]
                            rr = [search(shape, x, t, cap=CAP) for x in MS]
                            res = "found" if any(x[0] == "found" for x in rr) else ("none" if all(x[0] == "none" for x in rr) else "cut")
                    tally[res] += 1
                    print(r["id"], r["key"], p, j, Hs, res, flush=True)
print("TALLY", dict(tally))
