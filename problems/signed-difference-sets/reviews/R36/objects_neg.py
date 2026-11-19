"""Negative control for objects.py: on quotients where p is NOT self-conjugate (or p | |H|), the congruence
should fail for some stored sets, and a too-strict marked bound (maxm replaced by |x|-tight c-2) should fail."""
import glob, os, re, math, sys, itertools
sys.path.insert(0, os.path.dirname(__file__))
from controls import primes_sq, certs
ROOT = os.path.join(os.path.dirname(__file__), "..", "..", "..")
cong_fail = cong_tested = tight_fail = 0
for f in sorted(glob.glob(os.path.join(ROOT, "objects", "O*.txt"))):
    lines = open(f, encoding="utf-8").read().split("\n")
    m = re.match(r"\s*((?:C\d+x?)+)\s*\((\d+),(\d+),(-?\d+)\)", lines[0])
    ms = [int(x) for x in re.findall(r"C(\d+)", m[1])]; v, k, lam = int(m[2]), int(m[3]), int(m[4])
    D = {tuple(int(x) for x in p[:-1]): (1 if p[-1] == "+" else -1)
         for p in (ln.split() for ln in lines[1:]) if len(p) == len(ms) + 1 and p[-1] in "+-"}
    valid = {(p, ds) for p, j, i, ds in certs(ms, k - lam)}
    for p, _ in primes_sq(k - lam):
        for ds in itertools.product(*[[d for d in range(1, mm + 1) if mm % d == 0] for mm in ms]):
            N = math.prod(ds)
            if N <= 1: continue
            a = {}
            for g, e in D.items():
                h = tuple(x % d for x, d in zip(g, ds)); a[h] = a.get(h, 0) + e
            sums = [a.get(h, 0) for h in itertools.product(*[range(d) for d in ds])]
            c = v // N
            if (p, ds) not in valid:
                cong_tested += 1; cong_fail += len({x % p for x in sums}) > 1
            elif sum(c - 2 for x in sums) < k:
                tight_fail += 1
print("non-self-conjugate quotients", cong_tested, "congruence fails on", cong_fail, "| too-tight bound fails on", tight_fail)
