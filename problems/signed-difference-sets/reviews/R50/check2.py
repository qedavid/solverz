"""Check 2: independent scan of instances.csv for the C44 test; per-row parameters against the row files."""
import csv, re, os, math, glob, collections
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../.."))
def isprime(n): return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))
kills = []
stat = collections.Counter()
for r in csv.DictReader(open(os.path.join(ROOT, "instances.csv"), encoding="utf-8")):
    m = re.match(r"SDS\((\d+),(-?\d+),(-?\d+),\[([\d,]+)\]\)", r["key"])
    v, k, lam = int(m[1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(",")]
    assert math.prod(ms) == v
    n = k - lam
    if n <= 0: continue
    p = math.isqrt(n)
    if p * p != n or not isprime(p): continue
    rank = sum(1 for x in ms if x % p == 0)
    if rank < 2: continue
    stat["n=p^2, rank>=2"] += 1
    S2 = k + lam * (v - 1)
    if S2 < 0 or math.isqrt(S2) ** 2 != S2:
        stat["s not integer"] += 1; continue
    s = math.isqrt(S2); c = v // (p * p)
    assert s % p == 0 and s * s == p * p * (1 + lam * c)
    q = s // p
    if c * p < q + p - 1 and (q + 1) % p != 0:
        kills.append((r["id"], r["key"], r["status"], p, c, s, q))
for x in kills: print(*x)
print(stat, "kills", len(kills), collections.Counter(x[2] for x in kills))
# per-row file parameters
L = os.path.join(ROOT, "lean/SignedDifferenceSets/TomographySquareRows")
kd = {x[0]: x for x in kills}
for f in sorted(glob.glob(L + "/*.lean")):
    t = open(f, encoding="utf-8").read(); rid = os.path.basename(f)[:-5]
    m = re.search(r"not_hasSDS_grp_sq \(ms := \[([\d, ]+)\]\) (\d+)\s+\(A := (\[.*?\]\])\) \(P := (\[.*?\]\])\).*?\(c := (\d+)\) \(s := (\d+)\) \(q := (\d+)\)", t, re.S)
    ms, p, A, P, c, s, q = m[1], int(m[2]), eval(m[3]), eval(m[4]), int(m[5]), int(m[6]), int(m[7])
    msl = [int(x) for x in ms.split(",")]
    # forms: A[t] applied to P[u] must give unit vectors mod p; A[t][i] * m_i ≡ 0 mod p (well defined)
    wd = all((a * mi) % p == 0 for row in A for a, mi in zip(row, msl))
    surj = all(sum(a * x for a, x in zip(A[t], P[u])) % p == (1 if t == u else 0) for t in range(2) for u in range(2))
    k0 = kd.get(rid)
    print(rid, "in scan" if k0 else "NOT IN SCAN", "params match" if k0 and (k0[3], k0[4], k0[5], k0[6]) == (p, c, s, q) else "PARAM MISMATCH", "forms ok" if wd and surj else "FORMS BAD", A, P)
