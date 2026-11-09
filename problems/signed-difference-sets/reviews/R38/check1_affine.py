"""Check 1, part 3: Bose's affine RDS (q+1, n, q, (q-1)/n) in C_{n(q+1)} built from GF(q^2) (own field code),
and the combinations G - 2R - N, G - R - 2N (and R - N) for every n | q - 1, q <= QMAX: which are SDSs?"""
import sys, itertools
import numpy as np
import sdslib as L

def factor_pp(q):
    for p in range(2, q + 1):
        if q % p == 0:
            e = 0
            while q % p == 0: q //= p; e += 1
            return (p, e) if q == 1 else None
    return None

def gf(p, d):
    """Power table of a primitive element of GF(p^d): list of coefficient tuples, via a primitive polynomial."""
    Q = p ** d
    for coeffs in itertools.product(range(p), repeat=d):   # x^d = sum c_i x^i  (monic poly x^d - sum c_i x^i)
        if coeffs[0] == 0: continue
        cur = [1] + [0] * (d - 1); seen = 0; table = []
        ok = True
        for i in range(Q - 1):
            table.append(tuple(cur))
            # multiply by x
            top = cur[-1]
            cur = [0] + cur[:-1]
            cur = [(cur[j] + top * coeffs[j]) % p for j in range(d)]
            if cur == [1] + [0] * (d - 1) and i < Q - 2:
                ok = False; break
        if ok and cur == [1] + [0] * (d - 1) and len(set(table)) == Q - 1:
            return table
    raise ValueError

def bose(q, n):
    p, e = factor_pp(q)
    T = gf(p, 2 * e)
    M = q * q - 1
    one = tuple([1] + [0] * (2 * e - 1))
    R = []
    for i in range(M):
        tr = tuple((a + b) % p for a, b in zip(T[i], T[(q * i) % M]))
        if tr == one: R.append(i)
    assert len(R) == q
    v = n * (q + 1)
    Rp = [i % v for i in R]
    assert len(set(Rp)) == q
    cos = set(i % (q + 1) for i in Rp)
    miss = [c for c in range(q + 1) if c not in cos]
    assert len(miss) == 1
    Rp = [(i - miss[0]) % v for i in Rp]
    N = [j * (q + 1) for j in range(n)]
    assert not set(Rp) & set(N)
    return v, Rp, N

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 49
bad = 0
for q in range(2, QMAX + 1):
    if not factor_pp(q): continue
    for n in range(2, q):
        if (q - 1) % n: continue
        v, R, N = bose(q, n)
        ms = (v,)
        Rt = [(r,) for r in R]; Nt = [(x,) for x in N]
        if not L.is_rds(Rt, Nt, ms, (q - 1) // n):
            print("NOT RDS", q, n); bad += 1; continue
        G = np.ones(ms, dtype=np.int64); Ri = L.indicator(Rt, ms); Ni = L.indicator(Nt, ms)
        a = L.sds_params(G - 2 * Ri - Ni); b = L.sds_params(G - Ri - 2 * Ni); c = L.sds_params(Ri - Ni)
        ca = 4 * (q - 1) == n * (n - 4)       # q = (n/2-1)^2
        cb = q == (2 * n - 1) ** 2
        cc = q == (n + 1) ** 2
        wa = (v, n * q, q * (n - 4)) if ca else None
        wb = (v, v - q, v - 2 * q) if cb else None
        wc = (v, q + n, n) if cc else None
        flag = "" if (a == wa and b == wb and c == wc) else "  <-- MISMATCH"
        if flag: bad += 1
        if a or b or c or flag:
            print(f"q={q} n={n} v={v}: G-2R-N {a} (want {wa}); G-R-2N {b} (want {wb}); R-N {c} (want {wc}){flag}", flush=True)
print("pairs checked up to q =", QMAX, "bad =", bad)
