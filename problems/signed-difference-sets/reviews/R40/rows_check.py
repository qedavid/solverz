"""Independent recomputation of C33's row rule on instances.csv (no imports from solver/).
Rule: some prime p with p^2 | n = k - lam, the Sylow p-subgroup of G = Z_m1 x ... x Z_mt cyclic
(at most one m_i divisible by p) of order p^J >= p^2, and p not dividing lam. Also j = 1 (order p) for comparison."""
import csv, re, sys
from collections import Counter
ROOT = sys.argv[1]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
def vp(x, p):
    c = 0
    while x % p == 0:
        x //= p; c += 1
    return c
def primes(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: out.append(n)
    return out
def hit(v, k, lam, ms, jmin=2):
    n = k - lam
    if n <= 0: return None
    for p in primes(n):
        if n % (p * p): continue
        divs = [m for m in ms if m % p == 0]
        if len(divs) != 1: continue
        J = vp(divs[0], p)
        assert J == vp(v, p)
        if J >= jmin and lam % p: return (p, J)
    return None
rows = list(csv.DictReader(open(ROOT + "/instances.csv", encoding="utf-8")))
settle = {l.split("\t")[0] for l in open(ROOT + "/scratch/maedge/settle.tsv", encoding="utf-8") if l.strip()}
cnt, cnt1 = Counter(), Counter(); open_hits = {}; bad = []
for r in rows:
    m = KEY.fullmatch(r["key"]); v, k, lam = int(m[1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(",")]
    prod = 1
    for x in ms: prod *= x
    assert prod == v, r["key"]
    h = hit(v, k, lam, ms)
    if h:
        cnt[r["status"]] += 1
        if r["status"] == "open": open_hits[r["id"]] = (r["key"], h)
        if r["status"] == "exists": bad.append((r["id"], r["key"], h, r["evidence"]))
    h1 = hit(v, k, lam, ms, 1)
    if h1 and h1[1] == 1: cnt1[r["status"]] += 1
print("rule (J>=2) hits by status:", dict(cnt))
print("rule (J=1, s^2 argument) hits by status:", dict(cnt1))
print("exists rows hit:", bad)
print("open hits:", len(open_hits), " settle.tsv:", len(settle))
print("in rule not settle:", sorted(set(open_hits) - settle)); print("in settle not rule:", sorted(settle - set(open_hits)))
print("(p, J) among open hits:", Counter(h for _, h in open_hits.values()))
print("non-cyclic groups among open hits:", [(i, kk) for i, (kk, h) in open_hits.items() if "," in kk.split("[")[1]])
