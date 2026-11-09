"""On every known set in objects/: each cyclic quotient Z_m and odd prime p with p^2 | m.
Checks: the coset sums f have autocorrelation n[g=0] + lam*c; where M1's q-condition holds, (i) the bound
phi(m) n <= m F c^2, (ii) the proof's intermediate claim: some translate f(. + s) has chi_{a(1+F)} = chi_a for all units a,
(iii) chi_a(f_s) = chi_a(restrict_F f_s). Also counts (m, p) where the q-condition fails and the descent claim (ii) fails."""
import os, re, sys, cmath, itertools
from math import gcd
sys.path.insert(0, os.path.dirname(__file__))
from indep import factor, phi, lcm, powers, qfree

def load(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    hdr = lines[0]
    g = re.match(r"(\S+) \((\d+),(\d+),(-?\d+)\)", hdr)
    ms = [int(x) for x in g[1].replace('C', ' ').replace('x', ' ').split()]
    v, k, lam = int(g[2]), int(g[3]), int(g[4])
    D = {}
    for ln in lines[1:]:
        if not ln.strip():
            continue
        *xs, s = ln.split()
        D[tuple(int(x) for x in xs)] = 1 if s == '+' else -1
    return ms, v, k, lam, D

def chis(f, m):
    w = [cmath.exp(2j * cmath.pi * h / m) for h in range(m)]
    return [sum(f[h] * w[(a * h) % m] for h in range(m)) for a in range(m)]

stats = dict(objs=0, quot=0, hyp=0, bound_fail=0, desc_fail=0, restr_fail=0, nohyp=0, nohyp_desc_fail=0, minmargin=None)
for fn in sorted(os.listdir(sys.argv[1])):
    if not fn.endswith('.txt'):
        continue
    ms, v, k, lam, D = load(os.path.join(sys.argv[1], fn))
    prod = 1
    for x in ms:
        prod *= x
    assert prod == v and len(D) == k, fn
    stats['objs'] += 1
    n = k - lam
    qs = list(factor(n)) if n > 0 else []
    ex = 1
    for x in ms:
        ex = lcm(ex, x)
    for m in range(2, ex + 1):
        if ex % m:
            continue
        ps = [p for p in factor(m) if p != 2 and m % (p * p) == 0]
        if not ps or n <= 0:
            continue
        a_ = [m // gcd(m, mi) for mi in ms]
        f = [0] * m
        for x, s in D.items():
            f[sum(ai * xi for ai, xi in zip(a_, x)) % m] += s
        c = v // m
        for g in range(m):
            ac = sum(f[h] * f[(h + g) % m] for h in range(m))
            assert ac == (n if g == 0 else 0) + lam * c, (fn, m, g)
        stats['quot'] += 1
        units = [a for a in range(1, m) if gcd(a, m) == 1]
        for p in ps:
            F = m // p
            t = 1 + F
            hyp = all(qfree(m, q) == 1 or t % qfree(m, q) in powers(q % qfree(m, q), qfree(m, q)) for q in qs)
            # descent claim: some translate with chi_{a t} = chi_a for all units a
            okS = None
            for s in range(m):
                fs = [f[(h + s) % m] for h in range(m)]
                ch = chis(fs, m)
                if all(abs(ch[a * t % m] - ch[a]) < 1e-6 for a in units):
                    okS = (s, fs, ch)
                    break
            if hyp:
                stats['hyp'] += 1
                lhs, rhs = phi(m) * n, m * F * c * c
                if lhs > rhs:
                    stats['bound_fail'] += 1
                    print('BOUND FAIL', fn, m, p)
                mg = rhs / lhs
                if stats['minmargin'] is None or mg < stats['minmargin'][0]:
                    stats['minmargin'] = (mg, fn, ms, v, k, lam, m, p)
                if okS is None:
                    stats['desc_fail'] += 1
                    print('DESCENT FAIL', fn, ms, (v, k, lam), m, p)
                else:
                    s, fs, ch = okS
                    r = [fs[h] if (F * h) % m == 0 else 0 for h in range(m)]
                    cr = chis(r, m)
                    if any(abs(cr[a] - ch[a]) > 1e-6 for a in units):
                        stats['restr_fail'] += 1
                        print('RESTRICT FAIL', fn, m, p)
            else:
                stats['nohyp'] += 1
                if okS is None:
                    stats['nohyp_desc_fail'] += 1
                    print('control: q-condition fails and no translate descends:', fn, ms, (v, k, lam), m, p)
print(stats)
