"""Are any of the 151 rows already settled by Gordon's table or by He-Wu's Theorem 3.2 (self-conjugate prime: v_p(n) odd
and p^j = -1 mod m for some m > 1 dividing exp G) or Theorem 4.2 (v even => n a square)? Also k = v - 1 rows."""
import csv, re, sys, math
ROOT = sys.argv[1]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
ids = [l.split("\t")[0] for l in open(ROOT + "/scratch/maedge/settle.tsv", encoding="utf-8") if l.strip()]
tab = {r["id"]: r for r in csv.DictReader(open(ROOT + "/instances.csv", encoding="utf-8"))}
def vp(x, p):
    c = 0
    while x % p == 0: x //= p; c += 1
    return c
def primes(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    return out + ([n] if n > 1 else [])
src, hw = {}, []
for i in ids:
    r = tab[i]; m = KEY.fullmatch(r["key"]); v, k, lam = int(m[2 - 1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(",")]
    E = math.lcm(*ms); n = k - lam
    src[r["source"].split("@")[0]] = src.get(r["source"].split("@")[0], 0) + 1
    why = []
    if v % 2 == 0 and math.isqrt(n) ** 2 != n: why.append("HW4.2")
    if k == v - 1: why.append("k=v-1")
    for p in primes(n):
        if vp(n, p) % 2 == 0: continue
        for mm in range(2, E + 1):
            if E % mm or math.gcd(p, mm) != 1: continue
            x, seen = p % mm, set()
            while x not in seen:
                if x == mm - 1: why.append(f"HW3.2 p={p} m={mm}"); break
                seen.add(x); x = x * p % mm
            if why and why[-1].startswith("HW3.2"): break
    if why: hw.append((i, r["key"], why))
print("Gordon source of the 151:", src); print("rows an HW test or k = v - 1 hits:", hw)
