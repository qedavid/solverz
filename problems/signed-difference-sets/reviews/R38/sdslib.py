"""Exact group-ring helpers on Z_{m1} x ... x Z_{mr} (numpy int64 arrays of shape ms)."""
import itertools, re
import numpy as np

OBJ = "problems/signed-difference-sets/objects/"

def shift(A, g):
    """B(x) = A(x + g)."""
    return np.roll(A, tuple(-gi for gi in g), axis=tuple(range(A.ndim)))

def autocorr(D):
    """C(g) = sum_x D(x) D(x+g), exact."""
    ms = D.shape
    C = np.zeros(ms, dtype=np.int64)
    for x in zip(*np.nonzero(D)):
        # sum over x of D(x) * D(x+g): add D(x) * (D shifted so index g holds D(x+g))
        C += int(D[x]) * shift(D, x)
    return C

def sds_params(D):
    """Return (v,k,lam) if D is a {0,+-1} SDS, else None."""
    if not np.all(np.isin(D, (-1, 0, 1))):
        return None
    C = autocorr(D)
    v = D.size; k = int(np.count_nonzero(D))
    z = (0,) * D.ndim
    if int(C[z]) != k:
        return None
    vals = set(int(c) for i, c in np.ndenumerate(C) if i != z)
    if len(vals) != 1:
        return None
    return (v, k, vals.pop())

def load_obj(i):
    lines = open(OBJ + f"O{i}.txt").read().split("\n")
    head = lines[0]
    ms = tuple(int(t) for t in re.findall(r"C(\d+)", head.split()[0]))
    par = tuple(int(t) for t in re.findall(r"-?\d+", head.split()[1]))
    D = np.zeros(ms, dtype=np.int64)
    for ln in lines[1:]:
        t = ln.split()
        if not t:
            continue
        coords = tuple(int(c) for c in t[:-1]); s = t[-1]
        assert len(coords) == len(ms), (i, ln)
        D[coords] = 1 if s == "+" else -1
    return ms, par, D

def elements(ms):
    return list(itertools.product(*[range(m) for m in ms]))

def add(a, b, ms):
    return tuple((x + y) % m for x, y, m in zip(a, b, ms))

def neg(a, ms):
    return tuple((-x) % m for x, m in zip(a, ms))

def subgroup_gen(gens, ms):
    S = {tuple([0] * len(ms))}
    frontier = list(S)
    while frontier:
        nf = []
        for a in frontier:
            for g in gens:
                b = add(a, g, ms)
                if b not in S:
                    S.add(b); nf.append(b)
        frontier = nf
    return S

def subgroups_of_order(ms, n):
    """All subgroups of order n (by brute force over generator pairs; fine for small groups)."""
    els = elements(ms)
    found = set()
    for g in els:
        S = frozenset(subgroup_gen([g], ms))
        if len(S) == n:
            found.add(S)
    for g, h in itertools.combinations(els, 2):
        S = frozenset(subgroup_gen([g, h], ms))
        if len(S) == n:
            found.add(S)
    return found

def indicator(S, ms):
    A = np.zeros(ms, dtype=np.int64)
    for x in S:
        A[tuple(x)] += 1
    return A

def is_rds(R, N, ms, lamR):
    """R a set, N a subgroup: RR^(-1) = |R| + lamR (G - N)."""
    A = indicator(R, ms)
    if A.max() > 1:
        return False
    C = autocorr(A)
    Ni = indicator(N, ms)
    want = lamR * (np.ones(ms, dtype=np.int64) - Ni)
    want[(0,) * len(ms)] = len(R)
    return bool(np.array_equal(C, want))
