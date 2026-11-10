"""Exhaustive: every f : Z_m -> [-c, c] with autocorrelation n[g = 0] + mu, n > 0 (the setting of
totient_mul_le_of_chain_aux, wider than coset sums). For each, every F reachable by valid chains
(step rule of indep.py): check phi(m) n <= m F c^2 and the descent (zeta^j X in Q(zeta_F)).
Also reports f breaking the bound for the relaxed rule (p = 2 with only 4 | d) or with no q-condition."""
import sys, math, cmath, itertools
import numpy as np
from functools import lru_cache

def factor(x):
    f, p = {}, 2
    while p * p <= x:
        while x % p == 0: f[p] = f.get(p, 0) + 1; x //= p
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
    while x not in s: s.add(x); x = x * q % mod
    return frozenset(s)
@lru_cache(maxsize=None)
def step_ok(m, qs, d, p, rule):
    if d % (p * p): return False
    if p == 2 and d % 8 and rule != 'four': return False
    dp = d // p
    if any(dp % r for r in factor(m)): return False
    if rule == 'noq': return True
    for q in qs:
        mq = qfree(m, q); pw = powers(q, mq)
        if not any(math.gcd(t, m) == 1 and t % mq in pw for t in range((1 + dp) % d, m, d)):
            return False
    return True
@lru_cache(maxsize=None)
def reach(m, qs, rule='ok'):
    seen, stack = {m: ()}, [m]
    while stack:
        d = stack.pop()
        for p in factor(d):
            if step_ok(m, qs, d, p, rule) and d // p not in seen:
                seen[d // p] = seen[d] + (p,); stack.append(d // p)
    return seen

m, c = int(sys.argv[1]), int(sys.argv[2])
b = 2 * c + 1
total = b ** m
digits = np.arange(m)
sols = []
CH = 1 << 21
for start in range(0, total, CH):
    idx = np.arange(start, min(start + CH, total), dtype=np.int64)
    F = np.empty((idx.size, m), dtype=np.int16)
    x = idx.copy()
    for i in range(m):
        F[:, i] = (x % b) - c; x //= b
    A0 = (F * F).sum(1)
    A1 = (F * np.roll(F, -1, axis=1)).sum(1)
    ok = A0 > A1
    for g in range(2, m // 2 + 1):
        ok &= (F * np.roll(F, -g, axis=1)).sum(1) == A1
    for row in F[ok]:
        sols.append(tuple(int(v) for v in row))
def e(x): return cmath.exp(2j * cmath.pi * x)
ns, checked, viol, viol_fix, relaxed = {}, 0, 0, 0, {'four': 0, 'noq': 0}
for f in sols:
    a0 = sum(v * v for v in f); a1 = sum(f[h] * f[(h + 1) % m] for h in range(m)); n = a0 - a1
    ns[n] = ns.get(n, 0) + 1
    qs = tuple(sorted(factor(n)))
    R = reach(m, qs)
    chi = [sum(f[h] * e(a * h / m) for h in range(m)) for a in range(m)]
    for Fv, ch in R.items():
        if Fv == m: continue
        checked += 1
        if phi(m) * n > m * Fv * c * c: viol += 1; print('BOUND', f, n, Fv, ch)
        U = [a for a in range(m) if math.gcd(a, m) == 1 and a % Fv == 1 % Fv]
        if not any(all(abs(e(a * j / m) * chi[a] - e(j / m) * chi[1]) < 1e-6 for a in U) for j in range(m)):
            viol_fix += 1; print('FIX', f, n, Fv, ch)
    for rule in relaxed:
        Fmin = min(reach(m, qs, rule))
        if phi(m) * n > m * Fmin * c * c:
            relaxed[rule] += 1
            if relaxed[rule] <= 3: print('relaxed', rule, 'breaks on', f, 'n =', n, 'F =', Fmin)
print(f'm={m} c={c}: {len(sols)} f with n>0; n values {sorted(ns)}; (f,F<m) cases {checked}; '
      f'bound violations {viol}; descent failures {viol_fix}; relaxed-rule bound breaks {relaxed}')
