"""Independent recomputation of M1 kills (refuter, P18 M1).

For every row of instances.csv: every cyclic quotient Z_m of G (m | exp G, m > 1), every odd prime p with p^2 | m,
F = m/p, t = 1 + F; for each prime q | n = k - lam, t must lie in <q> in the units mod the q-free part of m
(subgroup enumerated by brute force). Kill: m*F*c^2 < phi(m)*n, c = v/m. Written without reading descentrows1.py.
"""
import csv, re, sys
from math import gcd

def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def phi(n):
    r = n
    for p in factor(n):
        r = r // p * (p - 1)
    return r

def lcm(a, b):
    return a // gcd(a, b) * b

def powers(q, mod):
    """The cyclic subgroup <q> of (Z/mod)^*, as a set of residues."""
    if mod == 1:
        return {0}
    s, x = set(), 1 % mod
    while x not in s:
        s.add(x)
        x = x * q % mod
    return s

def qfree(m, q):
    while m % q == 0:
        m //= q
    return m

def kills(v, k, lam, ms):
    n = k - lam
    if n <= 0:
        return []
    qs = list(factor(n))
    ex = 1
    for x in ms:
        ex = lcm(ex, x)
    out = []
    for m in range(2, ex + 1):
        if ex % m:
            continue
        c = v // m
        for p in factor(m):
            if p == 2 or m % (p * p):
                continue
            F = m // p
            t = 1 + F
            ok = True
            for q in qs:
                mq = qfree(m, q)
                if (t % mq) not in powers(q % mq, mq) and mq != 1:
                    ok = False
                    break
            if ok and m * F * c * c < phi(m) * n:
                out.append((m, p))
    return out

def parse(key):
    g = re.match(r"SDS\((\d+),(-?\d+),(-?\d+),\[([\d,]*)\]\)", key)
    v, k, lam = int(g[1]), int(g[2]), int(g[3])
    ms = [int(x) for x in g[4].split(',') if x]
    return v, k, lam, ms

if __name__ == '__main__':
    rows = list(csv.DictReader(open(sys.argv[1], encoding='utf-8')))
    for r in rows:
        v, k, lam, ms = parse(r['key'])
        prod = 1
        for x in ms:
            prod *= x
        assert prod == v, r
        kl = kills(v, k, lam, ms)
        if kl:
            print(r['id'], r['status'], r['key'], ' '.join(f'{m}/{p}' for m, p in kl))
