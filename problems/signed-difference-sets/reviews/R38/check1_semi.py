"""Check 1, part 1: semiregular RDS (n^2,n,n^2,n) -> R - N and G - R - N.
(a) every semiregular RDS in every abelian group of order 8 and 27 (brute force over coset reps);
(b) the paper's two algebraic RDSs for p = 2, 3, 5, 7;
(c) the sanity rejection: a perturbed set is not an SDS."""
import itertools, sys
import numpy as np
import sdslib as L

def combos(R, N, ms):
    G = np.ones(ms, dtype=np.int64)
    Ri, Ni = L.indicator(R, ms), L.indicator(N, ms)
    return Ri - Ni, G - Ri - Ni

def expect(n):
    return (n**3, n*n + n - 2, n - 2), (n**3, n**3 - n*n - n + 2, n**3 - 2*n*n - n + 2)

def brute(ms, n):
    """All semiregular RDS R with 0 in R, R cap N = {0}, for every subgroup N of order n."""
    out = []
    zero = (0,) * len(ms)
    for N in L.subgroups_of_order(ms, n):
        # cosets of N
        seen, cosets = set(), []
        for g in L.elements(ms):
            if g in seen: continue
            c = [L.add(g, h, ms) for h in N]
            seen.update(c); cosets.append(c)
        others = [c for c in cosets if zero not in c]
        cnt = 0
        for choice in itertools.product(*others):
            R = [zero] + list(choice)
            if L.is_rds(R, N, ms, n):
                cnt += 1
                out.append((N, R))
        print(f"  {ms} N={sorted(N)}: {cnt} RDS with 0 in R", flush=True)
    return out

bad = 0
for n, groups in [(2, [(8,), (2, 4), (2, 2, 2)]), (3, [(27,), (3, 9), (3, 3, 3)])]:
    e1, e2 = expect(n)
    for ms in groups:
        rs = brute(ms, n)
        ok = 0
        for N, R in rs:
            A, B = combos(R, N, ms)
            pa, pb = L.sds_params(A), L.sds_params(B)
            if pa != e1 or pb != e2:
                bad += 1; print("  FAIL", ms, sorted(N), R, pa, pb)
            else:
                ok += 1
        print(f"n={n} {ms}: {len(rs)} RDS, {ok} give both SDS {e1} {e2}", flush=True)

# (b) algebraic RDS
for p in [2, 3, 5, 7]:
    e1, e2 = expect(p)
    ms = (p, p, p)
    R = [(x, y, (x * y) % p) for x in range(p) for y in range(p)]
    N = [(0, 0, z) for z in range(p)]
    r1 = L.is_rds(R, N, ms, p); A, B = combos(R, N, ms)
    print(f"p={p} F_p^3 (x,y,xy): RDS={r1}", L.sds_params(A), L.sds_params(B), "want", e1, e2)
    if not (r1 and L.sds_params(A) == e1 and L.sds_params(B) == e2): bad += 1
    ms = (p * p, p)
    R = [((x + p * x * y) % (p * p), y) for x in range(p) for y in range(p)]
    N = [(p * z, 0) for z in range(p)]
    r2 = L.is_rds(R, N, ms, p); A, B = combos(R, N, ms)
    print(f"p={p} Z_p2 x Z_p (x+pxy,y): RDS={r2}", L.sds_params(A), L.sds_params(B), "want", e1, e2)
    if p > 2 and not (r2 and L.sds_params(A) == e1 and L.sds_params(B) == e2): bad += 1

# (c) rejection
ms, par, D = L.load_obj(6); D2 = D.copy(); D2[0, 0] = -D2[0, 0]
print("perturbed O6 ->", L.sds_params(D2))
ms, par, D = L.load_obj(57); D2 = D.copy(); idx = tuple(np.argwhere(D == 0)[0]); D2[idx] = 1
print("perturbed O57 ->", L.sds_params(D2))
print("bad =", bad)
