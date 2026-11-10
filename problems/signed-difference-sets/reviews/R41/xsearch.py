"""The descent core directly: every X = sum_{i < phi(m)} x_i zeta_m^i (power basis of Z[zeta_m]) with
|x_i| <= c and X Xbar = n in Z, n > 1. For every F reachable from m by valid steps (brute.py's rule),
test 'some zeta^j X lies in Q(zeta_F)' (e(aj/m) X_a = e(j/m) X_1 for all units a = 1 mod F, X_a the
embedding zeta -> e(a/m)). Controls: the same test for F reachable only under the relaxed rules
('four': p = 2 with 4 | d; 'noq': no q-condition) must fail somewhere if the test has teeth."""
import sys, math, cmath
import numpy as np
sys.argv, (m, c) = sys.argv[:1], map(int, sys.argv[1:3])
exec(open(__file__.replace('xsearch.py', 'brute.py')).read().split('m, c = int')[0])
ph = phi(m)
units = [a for a in range(m) if math.gcd(a, m) == 1]
E = np.array([[cmath.exp(2j * cmath.pi * a * i / m) for a in units] for i in range(ph)])
b = 2 * c + 1; total = b ** ph; CH = 1 << 20
sols = []
for start in range(0, total, CH):
    idx = np.arange(start, min(start + CH, total), dtype=np.int64)
    Xc = np.empty((idx.size, ph), dtype=np.float64); x = idx.copy()
    for i in range(ph):
        Xc[:, i] = (x % b) - c; x //= b
    N = np.abs(Xc @ E) ** 2
    n0 = np.rint(N[:, 0])
    ok = (np.abs(N - n0[:, None]) < 1e-6).all(1) & (n0 > 1)
    for row, nn in zip(Xc[ok], n0[ok]):
        sols.append((tuple(int(v) for v in row), int(nn)))
def e(x): return cmath.exp(2j * cmath.pi * x)
def emb(X, a): return sum(v * e(a * i / m) for i, v in enumerate(X))
def descends(X, F):
    U = [a for a in units if a % F == 1 % F]
    Xa = {a: emb(X, a) for a in U}
    return any(all(abs(e(a * j / m) * Xa[a] - e(j / m) * Xa[1]) < 1e-6 for a in U) for j in range(m))
stat = dict(X=len(sols), cases=0, fail=0, four_cases=0, four_fail=0, noq_cases=0, noq_fail=0)
ns = {}
for X, n in sols:
    ns[n] = ns.get(n, 0) + 1
    qs = tuple(sorted(factor(n)))
    R = reach(m, qs)
    for F in R:
        if F == m: continue
        stat['cases'] += 1
        if not descends(X, F): stat['fail'] += 1; print('FAIL', X, n, F, R[F])
    for rule in ('four', 'noq'):
        for F in set(reach(m, qs, rule)) - set(R):
            stat[rule + '_cases'] += 1
            if not descends(X, F):
                stat[rule + '_fail'] += 1
                if stat[rule + '_fail'] <= 2: print('control', rule, X, n, F, reach(m, qs, rule)[F])
print(f'm={m} c={c}:', stat, 'n:', dict(sorted(ns.items())))
