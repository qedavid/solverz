"""Controls: every `exists` row of instances.csv with an odd Z_p x Z_p quotient, run through the same route as the rows
(centred + strict C10' multiplier when p ∤ s, all vectors when p | s), own code. A KILLED here would break the method."""
import re, math, time, sys, parse, indep
from stmts import factor, mult_group

tab = parse.table()
for rid, row in sorted(tab.items(), key=lambda kv: int(kv[0][1:])):
    if row['status'] != 'exists' or int(rid[1:]) < (int(sys.argv[1]) if len(sys.argv) > 1 else 0): continue
    m = re.match(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]*)\]\)', row['key'])
    v, k, lam = int(m.group(1)), int(m.group(2)), int(m.group(3))
    ms = [int(x) for x in m.group(4).split(',')]
    s2 = k + lam * (v - 1)
    s = math.isqrt(s2)
    for p in sorted(set(q for mm in ms for q in factor(mm))):
        if p == 2 or sum(1 for mm in ms if mm % p == 0) < 2: continue
        c = v // (p * p); C = c * p
        nc = s % p == 0
        U = None if nc else mult_group(p, k - lam)
        Ut = sorted(U - {1}) if U else []
        t = min(Ut, key=lambda u: len(indep.orbits(p, u))) if Ut else 1
        norb = len(indep.orbits(p, t))
        if not (norb <= 5 or (norb <= 7 and C <= 25)):
            print(rid, row['key'], 'p=%d skipped (orbits %d, C %d)' % (p, norb, C), flush=True); continue
        t0 = time.time()
        V = indep.enum_vectors(p, C, k, lam, s, t)
        W = V if nc else [b for b in V if indep.moment0(b, p)]
        if len(W) ** ((p + 1) // 2) > 4e5:
            print(rid, row['key'], 'p=%d t=%d |W|=%d choice search skipped' % (p, t, len(W)), flush=True); continue
        ni, nb, ex = indep.choices(p, s, c, W)
        print(rid, row['key'], 'p=%d c=%d s=%d nc=%s t=%d |W|=%d integral=%d box=%d %s %.1fs' % (
            p, c, s, nc, t, len(W), ni, nb, 'FOUND' if nb else 'KILLED(!)', time.time() - t0), flush=True)
