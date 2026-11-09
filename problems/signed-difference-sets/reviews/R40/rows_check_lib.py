"""Independent recomputation of C33's row rule on instances.csv (no imports from solver/).
Rule: some prime p with p^2 | n = k - lam, the Sylow p-subgroup of G = Z_m1 x ... x Z_mt cyclic
(at most one m_i divisible by p) of order p^J >= p^2, and p not dividing lam. Also j = 1 (order p) for comparison."""
import csv, re, sys
from collections import Counter
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
def vp(x, p):
    c = 0
    while x % p == 0:
        x //= p; c += 1
    return c
def primes(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: out.append(n)
    return out
def hit(v, k, lam, ms, jmin=2):
    n = k - lam
    if n <= 0: return None
    for p in primes(n):
        if n % (p * p): continue
        divs = [m for m in ms if m % p == 0]
        if len(divs) != 1: continue
        J = vp(divs[0], p)
        assert J == vp(v, p)
        if J >= jmin and lam % p: return (p, J)
    return None
