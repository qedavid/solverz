import math
import csv, re, math, sys
def isprime(n):
    return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))
rows = []
for r in csv.DictReader(open('instances.csv', encoding='utf-8')):
    m = re.match(r'SDS\((\d+),(\d+),(-?\d+),\[(\d+),(\d+)\]\)', r['key'])
    if not m: continue
    v, k, lam, a, b = map(int, m.groups())
    if a != b or not isprime(a): continue
    p = a
    s2 = k + lam * (v - 1)
    s = math.isqrt(s2) if s2 >= 0 else -1
    n = k - lam
    orbit = isprime(n) and n % p not in (0, 1)
    rows.append((r['id'], p, k, lam, s, s % p != 0 if s >= 0 else None, n, orbit, r['status'], r['evidence'][:40]))
for x in rows:
    if x[8] != 'none' or '-v' in sys.argv: print(*x)
print(len(rows))
