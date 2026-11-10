"""Chain's smallest reachable F (indep.py's rule) vs Schmidt's F(m, n) as restated by Tan
(arXiv:1610.01914v4, Def. 2.10): for m <= M and every set Q of primes of n (n = product of Q,
primes < 60), report how often F_chain = F_S, F_chain a proper multiple, or anything else."""
import sys, math
from functools import lru_cache
src = open(__file__.replace('compare_F3.py', 'brute.py')).read().split('m, c = int')[0]
exec(src)
def nu(p, x):
    k = 0
    while x % p == 0: x //= p; k += 1
    return k
def ordmod(q, mod):
    if mod == 1: return 1
    x, k = q % mod, 1
    while x != 1: x = x * q % mod; k += 1
    return k
def F_S(v, Q):
    Dv = sorted(factor(v)); out = 1
    for r in Dv:
        others = [q for q in Q if q != r]
        if not others:
            b = 2 if r == 2 else 1
        else:
            bs = []
            for q in others:
                if v % 2 == 1 or q == 2: mu = math.prod(p for p in Dv if p != q)
                else: mu = 4 * math.prod(p for p in Dv if p not in (2, q))
                if r == 2: bs.append(nu(2, q * q - 1) + nu(2, ordmod(q, mu)) - 1)
                else: bs.append(nu(r, q ** (r - 1) - 1) + nu(r, ordmod(q, mu)))
            b = max(bs)
        out *= r ** b
    return math.gcd(v, out)
M = int(sys.argv[1])
primes = [p for p in range(2, 40) if all(p % d for d in range(2, p))]
import itertools
stats = {'eq': 0, 'chain_bigger_multiple': 0, 'chain_smaller': 0, 'other': 0}
ex = {}
for m in range(2, M + 1):
    for k in (1, 2, 3):
        for Q in itertools.combinations(primes, k):
            Fc = min(reach(m, Q)); Fs = F_S(m, Q)
            key = 'eq' if Fc == Fs else 'chain_bigger_multiple' if Fc % Fs == 0 else 'chain_smaller' if Fs % Fc == 0 and Fc < Fs else 'other'
            stats[key] += 1
            if key != 'eq' and len(ex.setdefault(key, [])) < 8: ex[key].append((m, Q, Fc, Fs))
print(stats)
for k, v in ex.items(): print(k, v)
