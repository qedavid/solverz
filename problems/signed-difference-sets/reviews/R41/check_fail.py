import sys, math, random, cmath
m = int(sys.argv[1]); Y = eval(sys.argv[2]); nfloat = int(sys.argv[3])
src = open('transversal_exact.py').read()
pre = src.split('stat = dict(')[0].split("random.seed(seed)")[1]
units = [a for a in range(m) if math.gcd(a, m) == 1]
exec(pre)
n = exact_norm(Y)
Q = set(); primes_of(n, Q)
print('float n', nfloat, 'exact n', n, 'diff', n - nfloat, 'primes', sorted(Q))
