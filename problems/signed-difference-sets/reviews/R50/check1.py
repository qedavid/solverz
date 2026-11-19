"""Check 1: an integer vector on Z_p with autocorrelation p^2*delta + mu is constant mod p.
A: exhaustive over boxes; negative controls with n = p, 2p, p^3/... B: known sets with k - lam = p^2."""
import itertools, math, re, glob, os, sys
import numpy as np
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../.."))

def exhaustive(p, B, ns):
    vals = np.arange(-B, B + 1)
    grids = np.array(np.meshgrid(*([vals] * p), indexing="ij")).reshape(p, -1).T  # all vectors
    ac = [np.einsum("ij,ij->i", grids, np.roll(grids, -g, axis=1)) for g in range(p)]
    same = np.ones(len(grids), bool)
    for g in range(2, p):
        same &= ac[g] == ac[1]
    n = ac[0] - ac[1]
    const = np.all((grids - grids[:, :1]) % p == 0, axis=1)
    out = {}
    for target in ns:
        sel = same & (n == target)
        out[target] = (int(sel.sum()), int((sel & ~const).sum()))
    return out

for p, B in (() if 'B' in sys.argv else ((2, 20), (3, 12), (5, 7), (7, 4))):
    ns = sorted({p * p, p, 2 * p, 4 * p * p, p ** 3, p * p * 9 if p != 3 else 4 * 9})
    r = exhaustive(p, B, ns)
    print(f"p={p} B={B}:", ", ".join(f"n={n}: {a} vectors, {b} not const mod p" for n, (a, b) in r.items()), flush=True)

# B: known sets
def isprime(n): return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))
tot = bad_c = bad_id = 0
summary = []
for f in sorted(glob.glob(os.path.join(ROOT, "objects/O*.txt")), key=lambda s: int(re.findall(r"O(\d+)", s)[0])):
    L = open(f).read().strip().split("\n")
    m = re.match(r"(\S+) \((\d+),(-?\d+),(-?\d+)\)", L[0])
    ms = [int(x) for x in re.findall(r"\d+", m[1])]; v, k, lam = int(m[2]), int(m[3]), int(m[4])
    n = k - lam; p = math.isqrt(n) if n > 0 else 0
    if p * p != n or not isprime(p): continue
    D = {}
    for ln in L[1:]:
        a = ln.split(); D[tuple(int(x) for x in a[:-1])] = 1 if a[-1] == "+" else -1
    assert len(D) == k
    s = sum(D.values())
    idx = [i for i, mi in enumerate(ms) if mi % p == 0]
    homs = [a for a in itertools.product(range(p), repeat=len(idx)) if any(a)]
    def contr(a):
        Y = [0] * p
        for x, val in D.items():
            Y[sum(ai * x[i] for ai, i in zip(a, idx)) % p] += val
        return Y
    nc = 0
    for a in homs:
        Y = contr(a); tot += 1
        if len({y % p for y in Y}) != 1: nc += 1
    bad_c += nc
    # onto maps to Z_p^2: line identity, residues of the lines
    info = ""
    if len(idx) >= 2 and s % p == 0:
        q = s // p; c = v // (p * p); res = set(); nid = 0; nmaps = 0
        for a in homs:
            for b in homs:
                indep = not any(all((x * ai + y * bi) % p == 0 for ai, bi in zip(a, b)) for x in range(p) for y in range(p) if (x, y) != (0, 0))
                if not indep: continue
                nmaps += 1
                if nmaps > 60: break
                W = {}
                for xx, val in D.items():
                    u = (sum(ai * xx[i] for ai, i in zip(a, idx)) % p, sum(bi * xx[i] for bi, i in zip(b, idx)) % p)
                    W[u] = W.get(u, 0) + val
                lines = [(1, j) for j in range(p)] + [(0, 1)]
                Ys = []
                for (l1, l2) in lines:
                    Ys.append(contr(tuple((l1 * ai + l2 * bi) % p for ai, bi in zip(a, b))))
                for g in itertools.product(range(p), repeat=2):
                    lhs = sum(Ys[j][(l1 * g[0] + l2 * g[1]) % p] for j, (l1, l2) in enumerate(lines))
                    if lhs != p * W.get(g, 0) + s: nid += 1
                for Y in Ys:
                    res.add((Y[0] - q) % p)
            if nmaps > 60: break
        bad_id += nid
        info = f" Z_p^2 maps {min(nmaps,60)}: identity failures {nid}; line residues - q mod p {sorted(res)}; box c*p<q+p-1: {c*p < q+p-1}; p|q+1: {(q+1)%p==0}"
    print(os.path.basename(f), m[1], (v, k, lam), "p", p, "s", s, "homs", len(homs), "not const", nc, info, flush=True)
print("total maps", tot, "not constant", bad_c, "identity failures", bad_id)
