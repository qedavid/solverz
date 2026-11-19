"""Descent test on large X: X = prod_{t in T} sigma_t(Y), T a random transversal of (Z/m)^x / <-1>,
Y = a small random element of Z[zeta_m]; then X Xbar = N(Y) = n. For every F reachable by valid chains
(brute.py's rule, n factored by Pollard rho), test 'some zeta^j X in Q(zeta_F)' numerically (relative
tolerance); controls: F reachable only with the relaxed rules ('four', 'noq')."""
import sys, math, cmath, random
sys.argv, (m, trials, seed) = sys.argv[:1], map(int, sys.argv[1:4])
exec(open(__file__.replace('transversal.py', 'brute.py')).read().split('m, c = int')[0])
random.seed(seed)
def is_prime(n):
    if n < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
def rho(n):
    if n % 2 == 0: return 2
    while True:
        x = y = random.randrange(2, n); c = random.randrange(1, n); d = 1
        while d == 1:
            x = (x * x + c) % n; y = (y * y + c) % n; y = (y * y + c) % n; d = math.gcd(abs(x - y), n)
        if d != n: return d
def primes_of(n, out):
    if n == 1: return
    if is_prime(n): out.add(n); return
    for p in range(2, 1000):
        if n % p == 0:
            out.add(p)
            while n % p == 0: n //= p
            return primes_of(n, out)
    d = rho(n); primes_of(d, out); primes_of(n // d, out)
def e(x): return cmath.exp(2j * cmath.pi * x)
units = [a for a in range(m) if math.gcd(a, m) == 1]
reps = sorted({min(a, m - a) for a in units})
stat = dict(tried=0, tested=0, cases=0, fail=0, four=0, four_fail=0, noq=0, noq_fail=0)
for _ in range(trials):
    Y = {}
    for _k in range(random.choice([2, 3, 3, 4])):
        i = random.randrange(m); Y[i] = Y.get(i, 0) + random.choice([-2, -1, 1, 1, 2])
    Yv = lambda z: sum(cf * z ** i for i, cf in Y.items())
    n = round(math.prod(abs(Yv(e(a / m))) ** 2 for a in reps))
    if n <= 1 or n > 10 ** 40: continue
    stat['tried'] += 1
    Q = set(); primes_of(n, Q); qs = tuple(sorted(Q))
    R = reach(m, qs)
    extra = {r: set(reach(m, qs, r)) - set(R) for r in ('four', 'noq')}
    if len(R) == 1 and not any(extra.values()): continue
    T = [t if random.random() < .5 else m - t for t in reps]
    X = {a: math.prod(Yv(e(a * t / m)) for t in T) for a in units}
    assert all(abs(abs(X[a]) ** 2 - n) < 1e-6 * n for a in units)
    def descends(F):
        U = [a for a in units if a % F == 1 % F]
        return any(all(abs(e(a * j / m) * X[a] - e(j / m) * X[1]) < 1e-7 * abs(X[1]) for a in U) for j in range(m))
    stat['tested'] += 1
    for F in R:
        if F == m: continue
        stat['cases'] += 1
        if not descends(F): stat['fail'] += 1; print('FAIL', Y, n, qs, F, R[F])
    for r, Fs in extra.items():
        for F in Fs:
            stat[r] += 1
            if not descends(F): stat[r + '_fail'] += 1
print(f'm={m}:', stat)
