"""Check 4: independent recomputation of C41's verdict (centred, no multiplier) on the TomographyLast rows.
Lines l_j(x, y) = x + j y (j < p), l_p = y on Z_p^2. Y_j: vectors on Z_p with sum s, square sum n + lam*c*p,
autocorrelation lam*c*p, |Y| <= c p, sum|Y| <= k (parity), centred (sum t Y(t) = 0 mod p).
Search: Y_0..Y_p with sum_j Y_j(l_j g) = s + p W(g), |W(g)| <= c, all g; meet in the middle on residues mod p."""
import sys, math, itertools, collections
import numpy as np
def vectors(p, F, S, Q, mu, k):
    out = []
    def rec(pre, sm, sq):
        r = p - len(pre)
        if r == 0:
            if sm == S and sq == Q:
                a = sum(map(abs, pre))
                if a <= k and (a - k) % 2 == 0 and all(sum(pre[t] * pre[(t + g) % p] for t in range(p)) == mu for g in range(1, p)):
                    out.append(tuple(pre))
            return
        for x in range(-F, F + 1):
            sq2 = sq + x * x
            if sq2 > Q: continue
            rem = S - sm - x
            if r == 1:
                if rem != 0 or sq2 != Q: continue
            elif rem * rem > (r - 1) * (Q - sq2): continue
            rec(pre + [x], sm + x, sq2)
    rec([], 0, 0)
    return out
def search(v, k, lam, p, name=""):
    c = v // (p * p); s = math.isqrt(k + lam * (v - 1)); n = k - lam
    assert s * s == k + lam * (v - 1) and s % p
    V = vectors(p, c * p, s, n + lam * c * p, lam * c * p, k)
    C = [Y for Y in V if sum(t * y for t, y in enumerate(Y)) % p == 0]
    pts = [(x, y) for x in range(p) for y in range(p)]
    lines = [(1, j) for j in range(p)] + [(0, 1)]
    # contribution of choosing vector Y for line j: array over the p^2 points
    contrib = [[np.array([Y[(a * x + b * y) % p] for (x, y) in pts], dtype=np.int64) for Y in C] for (a, b) in lines]
    h = (p + 1) // 2
    def half(js):
        combos = list(itertools.product(range(len(C)), repeat=len(js)))
        arr = np.zeros((len(combos), p * p), np.int64)
        for i, cb in enumerate(combos):
            arr[i] = sum(contrib[j][ci] for j, ci in zip(js, cb))
        return combos, arr
    ca, A = half(list(range(h))); cb, B = half(list(range(h, p + 1)))
    keyA = collections.defaultdict(list)
    for i, row in enumerate(A % p): keyA[row.tobytes()].append(i)
    need = (s - B) % p
    found = []; matched = 0
    for i, row in enumerate(need):
        for a in keyA.get(row.astype(np.int64).tobytes(), []):
            matched += 1
            W = (A[a] + B[i] - s) // p
            if np.abs(W).max() <= c:
                found.append((ca[a], cb[i]))
    print(name, (v, k, lam), "p", p, "c", c, "s", s, "#V", len(V), "#centred", len(C), "residue-matched tuples", matched,
          "tuples passing |W|<=c", len(found), "->", "FOUND" if found else "KILLED", flush=True)
rows = {"C5xC5(25,12,1)": (25, 12, 1, 5), "C7^3(343,172,84)": (343, 172, 84, 7), "C7xC7(49,33,1)": (49, 33, 1, 7),
        "N15384": (245, 76, 5, 7), "N31745/6": (343, 82, 11, 7), "N32195/6": (343, 334, 291, 7),
        "N15414": (245, 121, 50, 7), "N15434": (245, 144, 73, 7), "N31778/9": (343, 130, 3, 7), "N5089": (147, 134, 7, 7)}
for name in (sys.argv[1:] or rows):
    search(*rows[name], name=name)
