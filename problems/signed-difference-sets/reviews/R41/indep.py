"""Refuter's independent recomputation of C35's chain kills (written without reading
solver/descentrows2.py or scratch/p18/rows.py). For every row of instances.csv and every cyclic
quotient Z_m of G (m | exp G, m > 1), find the smallest F reachable from m by valid steps
d -> d/p (p prime, p^2 | d, p odd or 8 | d, rad m | d/p, and for each prime q | n a unit t mod m
with t = 1 + d/p mod d and t mod m_q in <q>, m_q the q-free part of m); kill iff
m F c^2 < phi(m) n, c = v/m."""
import csv, re, sys, math
from functools import lru_cache

def factor(x):
    f, p = {}, 2
    while p * p <= x:
        while x % p == 0:
            f[p] = f.get(p, 0) + 1; x //= p
        p += 1
    if x > 1: f[x] = f.get(x, 0) + 1
    return f

def phi(x):
    r = x
    for p in factor(x): r = r // p * (p - 1)
    return r

def qfree(m, q):
    while m % q == 0: m //= q
    return m

@lru_cache(maxsize=None)
def powers(q, mod):
    s, x = set(), 1 % mod
    while x not in s:
        s.add(x); x = x * q % mod
    return frozenset(s)

@lru_cache(maxsize=None)
def step_ok(m, qs, d, p):
    if d % (p * p): return False
    if p == 2 and d % 8: return False
    dp = d // p
    if any(dp % r for r in factor(m)): return False
    for q in qs:
        mq = qfree(m, q); pw = powers(q, mq)
        if not any(math.gcd(t, m) == 1 and t % mq in pw
                   for t in range((1 + dp) % d, m, d)):
            return False
    return True

@lru_cache(maxsize=None)
def best(m, qs):
    """(min F, a chain to it) over all valid chains from m."""
    seen, stack, bestF = {m: []}, [m], (m, [])
    while stack:
        d = stack.pop()
        for p in factor(d):
            if step_ok(m, qs, d, p):
                e = d // p
                if e not in seen:
                    seen[e] = seen[d] + [p]; stack.append(e)
                    if e < bestF[0]: bestF = (e, seen[e])
    return bestF

def divisors(x):
    return [i for i in range(1, x + 1) if x % i == 0]

rows = list(csv.DictReader(open(sys.argv[1], encoding='utf-8')))
kills = []
for r in rows:
    v, k, lam, ms = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)', r['key']).groups()
    v, k, lam = int(v), int(k), int(lam); ms = [int(x) for x in ms.split(',')]
    assert math.prod(ms) == v
    n = k - lam
    if n <= 0: continue
    ex = math.lcm(*ms); qs = tuple(sorted(factor(n)))
    hit = None
    for m in divisors(ex):
        if m == 1: continue
        c = v // m
        F, ch = best(m, qs)
        if m * F * c * c < phi(m) * n:
            hit = (m, F, ch, c); break
    if hit:
        kills.append((r['id'], r['status'], r['key'], n, hit))
for x in kills:
    print(*x, sep='\t')
