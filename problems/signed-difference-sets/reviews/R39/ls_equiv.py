"""M1's q-condition (1 + m/p in <q> mod the q-free part of m) versus the Leung-Schmidt exponent test for one step at p:
v_p(m) > v_p(q^(p-1) - 1) + v_p(ord_{mu(q)} q), mu(q) = rad of the q-free part of m (times 4 if m even, q odd), q != p."""
from indep import factor, powers, qfree

def nu(p, t):
    e = 0
    while t % p == 0:
        t //= p
        e += 1
    return e

def order(q, m):
    if m == 1:
        return 1
    x, k = q % m, 1
    while x != 1:
        x = x * q % m
        k += 1
    return k

primes = [q for q in range(2, 400) if all(q % d for d in range(2, int(q ** .5) + 1))]
agree = dis = 0
for m in range(9, 1001):
    for p in factor(m):
        if p == 2 or m % (p * p):
            continue
        t = 1 + m // p
        for q in primes:
            if q == p:
                continue
            mq = qfree(m, q)
            a = (t % mq) in powers(q % mq, mq)
            rad = 1
            for r in factor(mq):
                rad *= r
            mu = rad * (4 if m % 2 == 0 and q != 2 else 1) // (2 if m % 2 == 0 and q != 2 else 1)
            b = nu(p, m) > nu(p, q ** (p - 1) - 1) + nu(p, order(q, mu))
            if a == b:
                agree += 1
            else:
                dis += 1
                if dis < 10:
                    print('disagree', m, p, q, a, b)
print('agree', agree, 'disagree', dis)
