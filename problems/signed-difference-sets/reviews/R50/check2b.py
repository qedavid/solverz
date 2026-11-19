"""Check 2b: enumerate all line vectors (C3 demands, fibres c*p) for small C44 rows; residues mod p; the g = 0 test."""
import sys, math
def vectors(p, F, S, Q, mu, k):
    out = []
    def rec(pre, sm, sq):
        r = p - len(pre)
        if r == 0:
            if sm == S and sq == Q and sum(map(abs, pre)) <= k and (sum(map(abs, pre)) - k) % 2 == 0:
                if all(sum(pre[t] * pre[(t + g) % p] for t in range(p)) == mu for g in range(1, p)):
                    out.append(tuple(pre))
            return
        for x in range(-F, F + 1):
            sq2 = sq + x * x
            if sq2 > Q: continue
            # remaining r-1 entries: sum S - sm - x, squares <= Q - sq2 (Cauchy-Schwarz)
            rem = S - sm - x
            if r - 1 == 0:
                if rem != 0 or sq2 != Q: continue
            elif rem * rem > (r - 1) * (Q - sq2): continue
            rec(pre + [x], sm + x, sq2)
    rec([], 0, 0)
    return out
for rid, v, k, lam, p in (("N385", 50, 49, 24, 5), ("N1911", 98, 89, 40, 7), ("N5091", 147, 134, 85, 7), ("N2096", 100, 97, 72, 5), ("N9406", 196, 181, 132, 7)):
    c = v // (p * p); F = c * p; s = math.isqrt(k + lam * (v - 1)); q = s // p
    V = vectors(p, F, s, k - lam + lam * F, lam * F, k)
    res = sorted({(y[0] - q) % p for y in V} | {(y[1] - q) % p for y in V})
    const = all(len({y % p for y in Y}) == 1 for Y in V)
    # line identity at g = 0: sum over p+1 lines of Y_j(0) == p W(0) + s, so == s mod p
    vals0 = sorted({Y[t] % p for Y in V for t in range(p)})
    ok0 = any((sum(cmb) - s) % p == 0 for cmb in __import__("itertools").combinations_with_replacement(vals0, p + 1))
    print(rid, "p", p, "c", c, "s", s, "q", q, "#vectors", len(V), "examples", V[:2], "const mod p", const,
          "residues-q", res, "g=0 residue test passable", ok0)
