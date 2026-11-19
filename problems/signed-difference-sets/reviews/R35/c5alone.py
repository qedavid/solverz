"""For the 11 rows: best C5-type bound with a composite modulus Q (all q | n with q^2 | n, q !| |H|, q self-conj mod
exp H) over every quotient type H of G (any exponent e | exp G, H the largest quotient with that exponent)."""
import math
from scan import factor, selfconj, vp, divisors_of
rows = {"N6822": ([170], 146, 2), "N9200": ([195], 115, 15), "N44532": ([2, 200], 235, 10),
        "N44533": ([4, 100], 235, 10), "N58644": ([455], 415, 15)}
for nid, (ms, k, lam) in rows.items():
    n, v = k - lam, math.prod(ms)
    nf = factor(n)
    prim = {}
    for m in ms:
        for l, e in factor(m).items():
            prim.setdefault(l, []).append(e)
    expo = math.prod(l ** max(es) for l, es in prim.items())
    best = None
    for d in divisors_of(expo):
        if d == 1:
            continue
        h = math.prod(l ** sum(min(x, vp(d, l)) for x in es) for l, es in prim.items())
        c = v // h
        Q = math.prod(q ** (nf[q] // 2) for q in nf if nf[q] >= 2 and d % q and selfconj(q, d))
        if best is None or Q / (2 * c) > best[0]:
            best = (Q / (2 * c), d, h, c, Q)
    print(nid, "best Q/2c =", round(best[0], 3), "(d, |H|, c, Q) =", best[1:], "kills" if best[0] > 1 else "no kill")
