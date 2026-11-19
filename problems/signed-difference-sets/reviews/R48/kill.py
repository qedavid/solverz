"""Independent recomputation of the Klein (Z2 x Z2 x Z3, mod 4) kill. Own code, no imports from solver/."""
import csv, math, re, sys
from itertools import product
ROOT = sys.argv[1] if len(sys.argv) > 1 else '.'
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

def trip(Q, S):
    """All integer (a,b,c), a+b+c=S, a^2+b^2+c^2=Q; brute force a,b in [-r, r]."""
    if Q < 0: return []
    r = math.isqrt(Q)
    out = []
    for a in range(-r, r + 1):
        for b in range(-r, r + 1):
            c = S - a - b
            if a*a + b*b + c*c == Q: out.append((a, b, c))
    return out

def zs_alive(n, s, Qz):
    """Return (D, Z, alive): twisted-sum triples, contraction triples, z's admitting some d1,d2,d3."""
    t = math.isqrt(n)
    D = trip(n, t) + (trip(n, -t) if t else [])
    Z = trip(Qz, s) + (trip(Qz, -s) if s else [])
    Dres = sorted({tuple(x % 4 for x in d) for d in D})
    alive = []
    for z in Z:
        ok = False
        for d1, d2, d3 in product(Dres, repeat=3):
            if all((d1[i]-z[i]) % 2 == 0 and (d2[i]-z[i]) % 2 == 0 and (d3[i]-z[i]) % 2 == 0
                   and (z[i]+d1[i]+d2[i]+d3[i]) % 4 == 0 for i in range(3)):
                ok = True; break
        if ok: alive.append(z)
    return D, Z, Dres, alive

def verdict(v, k, lam):
    n = k - lam; S = k + lam*(v-1)
    if v % 3 or n < 0 or S < 0: return None
    t = math.isqrt(n); s = math.isqrt(S)
    if t*t != n or s*s != S: return None  # necessary conditions (n square from (sum d)^2 = n)
    Qz = k + lam*(v//3 - 1)
    D, Z, Dres, alive = zs_alive(n, s, Qz)
    return dict(n=n, t=t, s=s, Qz=Qz, nD=len(D), nZ=len(Z), Dres=Dres, alive=len(alive), kill=(len(alive) == 0), D=D, Z=Z)

def klein_quot(ms):
    return sum(1 for m in ms if m % 2 == 0) >= 2 and any(m % 3 == 0 for m in ms)

if __name__ == '__main__':
    rows = list(csv.DictReader(open(ROOT + '/instances.csv', encoding='utf-8')))
    cache = {}
    killed = []
    for r in rows:
        v, k, lam, ms = KEY.match(r['key']).groups()
        v, k, lam = int(v), int(k), int(lam); ms = [int(x) for x in ms.split(',')]
        assert math.prod(ms) == v, r['key']
        if not klein_quot(ms): continue
        key = (v, k, lam)
        if key not in cache: cache[key] = verdict(v, k, lam)
        V = cache[key]
        if V and V['kill']: killed.append((r['id'], r['status'], key, ms))
    for x in killed: print(*x)
    print('total killed', len(killed), 'by status', {s: sum(1 for x in killed if x[1] == s) for s in ('open','none','exists')})
