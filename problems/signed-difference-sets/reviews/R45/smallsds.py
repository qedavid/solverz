"""Refuter (C40): all SDS on Z_3 x Z_3 by brute force; for each, test the line identity, centring,
and (when n = k - lam prime, n != 0,1 mod 3, 3 does not divide s) fixed_line on the centred translate."""
import itertools, math
p = 3
pts = [(a, b) for a in range(p) for b in range(p)]
idx = {pt: i for i, pt in enumerate(pts)}
F = [(1, m) for m in range(p)] + [(0, 1)]
def isprime(n): return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))
found = {}
fixed_tests = 0; fixed_fail = 0; ident_fail = 0; cent_fail = 0
for D in itertools.product((-1, 0, 1), repeat=p * p):
    k = sum(1 for x in D if x)
    if k == 0: continue
    lams = set()
    for g in pts[1:]:
        lams.add(sum(D[idx[x]] * D[idx[((x[0] + g[0]) % p, (x[1] + g[1]) % p)]] for x in pts))
        if len(lams) > 1: break
    if len(lams) != 1: continue
    lam = lams.pop(); s = sum(D); n = k - lam
    found[(k, lam)] = found.get((k, lam), 0) + 1
    Y = [[sum(D[idx[x]] for x in pts if (u * x[0] + w * x[1]) % p == t) for t in range(p)] for (u, w) in F]
    for g in pts:
        if sum(Y[j][(u * g[0] + w * g[1]) % p] for j, (u, w) in enumerate(F)) != p * D[idx[g]] + s: ident_fail += 1
    if s % p == 0: continue
    inv = pow(s, -1, p)
    c = (sum(D[idx[x]] * x[0] for x in pts) * inv % p, sum(D[idx[x]] * x[1] for x in pts) * inv % p)
    Dc = [D[idx[((x[0] + c[0]) % p, (x[1] + c[1]) % p)]] for x in pts]
    Yc = [[sum(Dc[idx[x]] for x in pts if (u * x[0] + w * x[1]) % p == t) for t in range(p)] for (u, w) in F]
    if any(sum(t * y[t] for t in range(p)) % p for y in Yc): cent_fail += 1
    if isprime(n) and n % p not in (0, 1):
        fixed_tests += 1
        if any(y[(n * h) % p] != y[h] for y in Yc for h in range(p)): fixed_fail += 1
print("SDS parameter classes on Z3^2 (k, lam): count", dict(sorted(found.items())))
print("identity failures", ident_fail, "centring failures", cent_fail, "fixed_line tests", fixed_tests, "failures", fixed_fail)
