"""Own recomputation of each kill line's divided demands (no import from solver/)."""
import re, math, sys
LINE = re.compile(r"(N\d+) SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\) \d+ KILL (\d+) (\d+) \[([\d,]+)\] (\d+)$")
ids = set(sys.argv[2:])
for line in open(sys.argv[1], encoding="utf-8"):
    m = LINE.match(line.strip())
    if not m or (ids and m[1] not in ids): continue
    rid, v, k, lam, ms, p, j, e, nodes = m.groups()
    v, k, lam, p, j = int(v), int(k), int(lam), int(p), int(j)
    e = [int(x) for x in e.split(",")]; h1 = math.prod(e); c = v // (p * h1)
    num = k + lam * (p * c - 1); s = math.isqrt(k + lam * (v - 1))
    kp = k // p if (k // p - k) % 2 == 0 else k // p - 1
    Q, t, s1 = num // (p * p), lam * c // p, s // p
    cons = Q + (h1 - 1) * t == s1 * s1
    print(rid, f"v={v} k={k} lam={lam} n={k-lam} p={p} j={j} H'={e} |H'|={h1} c={c} Q={Q} t={t} s'={s1} k'={kp}",
          "exact" if num % (p*p) == 0 and lam*c % p == 0 and s % p == 0 and s*s == k+lam*(v-1) else "INEXACT",
          "Q+(|H'|-1)t=s'^2" if cons else "INCONSISTENT", nodes)
