"""Stored sets (objects/O*.txt): on every valid quotient, coset sums are congruent mod q and their
count vector meets the four conditions (N, s', Q, sum maxm >= k) -- a direct test of IsSDS.countsOk."""
import glob, os, re, math, sys
sys.path.insert(0, os.path.dirname(__file__))
from controls import certs
from intdp import maxm
ROOT = os.path.join(os.path.dirname(__file__), "..", "..", "..")
ok = bad = skipped = tested = 0
for f in sorted(glob.glob(os.path.join(ROOT, "objects", "O*.txt"))):
    lines = open(f, encoding="utf-8").read().split("\n")
    m = re.match(r"\s*((?:C\d+x?)+)\s*\((\d+),(\d+),(-?\d+)\)", lines[0])
    if not m:
        skipped += 1; continue
    ms = [int(x) for x in re.findall(r"C(\d+)", m[1])]; v, k, lam = int(m[2]), int(m[3]), int(m[4])
    D = {}
    for ln in lines[1:]:
        p = ln.split()
        if len(p) == len(ms) + 1 and p[-1] in "+-":
            D[tuple(int(x) for x in p[:-1])] = 1 if p[-1] == "+" else -1
    if len(D) != k or math.prod(ms) != v:
        skipped += 1; print("skip", os.path.basename(f), len(D), k); continue
    s = sum(D.values())
    for p, j, i, ds in certs(ms, k - lam):
        q = p ** j; N = math.prod(ds); c = v // N
        a, mk = {}, {}
        for g, e in D.items():
            h = tuple(x % d for x, d in zip(g, ds)); a[h] = a.get(h, 0) + e; mk[h] = mk.get(h, 0) + 1
        sums = [a.get(h, 0) for h in __import__("itertools").product(*[range(d) for d in ds])]
        tested += 1
        cond = (len({x % q for x in sums}) == 1 and all(abs(x) <= c for x in sums)
                and sum(x * x for x in sums) == k + lam * (c - 1) and sum(sums) in (s, -s) and s * s == k + lam * (v - 1)
                and sum(maxm(c, x) for x in sums) >= k)
        if cond: ok += 1
        else: bad += 1; print("VIOLATION", os.path.basename(f), ms, (p, j, i, ds), sums[:12])
print("objects tested (cert, object) pairs", tested, "ok", ok, "violations", bad, "skipped files", skipped)
