"""Known sets (objects/) vs C35: for every cyclic quotient Z_m, every surjection (up to 60 per m),
every F reachable by valid chains (indep.py's step rule), check (i) phi(m) n <= m F c^2 and
(ii) the descent itself: some j with e(aj/m) chi_a(f) = e(j/m) chi_1(f) for all units a = 1 mod F
(i.e. zeta^j X in Q(zeta_F))."""
import sys, os, re, math, itertools, cmath
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
def step_ok(m, qs, d, p):
    if d % (p * p): return False
    dp = d // p
    if any(dp % r for r in factor(m)): return False
    if NOQ: return True
    for q in qs:
        mq = qfree(m, q); pw = powers(q, mq)
        if not any(math.gcd(t, m) == 1 and t % mq in pw for t in range((1 + dp) % d, m, d)):
            return False
    return True
@lru_cache(maxsize=None)
def reach(m, qs):
    seen, stack = {m: ()}, [m]
    while stack:
        d = stack.pop()
        for p in factor(d):
            if step_ok(m, qs, d, p) and d // p not in seen:
                seen[d // p] = seen[d] + (p,); stack.append(d // p)
    return seen

def load(path):
    lines = open(path).read().split('\n')
    g, par = lines[0].split()[:2]
    ms = [int(x) for x in g[1:].split('xC')]
    v, k, lam = map(int, par.strip('()').split(','))
    D = {}
    for ln in lines[1:]:
        t = ln.split()
        if not t: continue
        D[tuple(int(x) for x in t[:-1])] = 1 if t[-1] == '+' else -1
    return ms, v, k, lam, D

NOQ = len(sys.argv) > 2
def e(x): return cmath.exp(2j * cmath.pi * x)
stats = dict(cases=0, nontriv=0, p2=0, viol_bound=0, viol_fix=0, tight=[])
for fn in sorted(os.listdir(sys.argv[1])):
    if not re.fullmatch(r'O\d+\.txt', fn): continue
    ms, v, k, lam, D = load(os.path.join(sys.argv[1], fn))
    n = k - lam
    if n <= 0: continue
    assert math.prod(ms) == v and len(D) == k
    qs = tuple(sorted(factor(n)))
    ex = math.lcm(*ms)
    for m in range(2, ex + 1):
        if ex % m: continue
        R = reach(m, qs)
        if len(R) == 1: continue
        c = v // m
        choices = [[a for a in range(m) if (a * mi) % m == 0] for mi in ms]
        maps = [A for A in itertools.product(*choices) if math.gcd(m, *A) == 1][:60]
        for A in maps:
            f = [0] * m
            for x, s in D.items(): f[sum(a * xi for a, xi in zip(A, x)) % m] += s
            auto = [sum(f[h] * f[(h + g) % m] for h in range(m)) for g in range(m)]
            assert all(auto[g] == auto[1] for g in range(1, m)) and auto[0] - auto[1] == n
            chi = [sum(f[h] * e(a * h / m) for h in range(m)) for a in range(m)]
            for F, chain in R.items():
                if F == m: continue
                stats['cases'] += 1; stats['nontriv'] += 1
                if 2 in chain: stats['p2'] += 1
                if phi(m) * n > m * F * c * c: stats['viol_bound'] += 1; print('BOUND', fn, m, A, F, chain)
                stats['tight'].append((m * F * c * c / (phi(m) * n), fn, m, F, chain))
                U = [a for a in range(m) if math.gcd(a, m) == 1 and a % F == 1 % F]
                if not any(all(abs(e(a * j / m) * chi[a] - e(j / m) * chi[1]) < 1e-6 for a in U)
                           for j in range(m)):
                    stats['viol_fix'] += 1; print('FIX', fn, m, A, F, chain)
t = sorted(stats.pop('tight'))
print(stats); print('tightest', t[:5])
