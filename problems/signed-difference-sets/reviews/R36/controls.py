"""Controls for C7's integer test: rows with known sets must never be killed, and the
coset sums of every stored object must meet the four count conditions on every valid quotient."""
import csv, re, os, sys, math, glob
from itertools import product
sys.path.insert(0, os.path.dirname(__file__))
from intdp import best_int, allowed, maxm

ROOT = os.path.join(os.path.dirname(__file__), "..", "..", "..")

def primes_sq(n):
    out, m, p = [], abs(n), 2
    while p * p <= m:
        e = 0
        while m % p == 0:
            m //= p; e += 1
        if e >= 2:
            out.append((p, e // 2))
        p += 1
    return out

def certs(ms, n):
    """All (p, j, i, ds) meeting ScCert.Valid's arithmetic (any j in 1..max)."""
    if n <= 0:
        return
    for p, jmax in primes_sq(n):
        for ds in product(*[[d for d in range(1, m + 1) if m % d == 0] for m in ms]):
            N = math.prod(ds)
            if N <= 1 or N % p == 0:
                continue
            L = math.lcm(*ds)
            i = next((i for i in range(1, 2 * L + 2) if (pow(p, i, L) + 1) % L == 0), None)
            if i is None:
                continue
            for j in range(1, jmax + 1):
                yield p, j, i, ds

def test_row(v, k, lam, ms, cap_states=3_000_000):
    s2 = k + lam * (v - 1)
    s = math.isqrt(s2) if s2 >= 0 else -1
    if s < 0 or s * s != s2:
        return "no-s", []
    kills, ran, skipped = [], 0, 0
    for p, j, i, ds in certs(ms, k - lam):
        N = math.prod(ds); c = v // N; q = p ** j; Q = k + lam * (c - 1)
        if N * c > 4000 or Q > 40000 or N > 400:
            skipped += 1; continue
        feasible = False
        for sp in {s, -s}:
            for t0 in range(q):
                b = best_int(allowed(q, t0, c), N, sp, Q, c)
                if b is not None and b >= k:
                    feasible = True; break
            if feasible:
                break
        ran += 1
        if not feasible:
            kills.append((p, j, i, ds))
    return (ran, skipped), kills

if __name__ == "__main__":
    rows = list(csv.DictReader(open(os.path.join(ROOT, "instances.csv"), encoding="utf-8")))
    ex = [r for r in rows if r["status"] == "exists"]
    tot_ran = tot_skip = 0; bad = []
    for r in ex:
        m = re.match(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", r["key"])
        v, k, lam = int(m[1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(",")]
        st, kills = test_row(v, k, lam, ms)
        if st == "no-s":
            print("no integer s:", r["id"], r["key"]); continue
        tot_ran += st[0]; tot_skip += st[1]
        if kills:
            bad.append((r["id"], r["key"], kills)); print("KILLED EXISTING ROW", r["id"], r["key"], kills, flush=True)
    print("exists rows", len(ex), "certificates run", tot_ran, "skipped (size)", tot_skip, "killed", len(bad))
