"""Group-ring test of C33 below the SDS level: every Y in Z[H], H = Z_{rp} x Z_m2 (m2 = |K|, K cyclic), entries in
[-c, c], with Y Y^(-1) = n + M.H (all nonzero shifts equal M), H/P nontrivial, p^2 | n: is p | M?  (M = lam c.)
Also checks Ma's step Y(h + u) = Y(h) mod p^b (b = v_p(n) // 2) on the hits. Any SDS on any group with a surjection
onto H with fibres c contracts to such a Y, so this covers all such groups at once.  Usage: grtest.py rp m2 p c"""
import sys, itertools
import numpy as np
rp, m2, p, c = map(int, sys.argv[1:5]); CTRL = len(sys.argv) > 5  # control: p || n instead of p^2 | n
N = rp * m2
els = [(a, b) for a in range(rp) for b in range(m2)]
idx = {e: t for t, e in enumerate(els)}
shift = [[idx[((a + g[0]) % rp, (b + g[1]) % m2)] for (a, b) in els] for g in els]   # shift[g][t] = index of t + g
base = 2 * c + 1; total = base ** N; chunk = base ** max(1, min(N, int(np.log(2e6) / np.log(base))))
u_perm = shift[idx[(rp // p, 0)]]
viol, hits, ma_viol, pairs = [], 0, 0, set()
for start in range(0, total, chunk):
    a = np.arange(start, min(start + chunk, total), dtype=np.int64)
    Y = np.empty((a.size, N), dtype=np.int64); x = a.copy()
    for t in range(N):
        Y[:, t] = (x % base) - c; x //= base
    M = (Y * Y[:, shift[1]]).sum(1)
    ok = np.ones(a.size, bool)
    for g in range(2, N):
        ok &= (Y * Y[:, shift[g]]).sum(1) == M
        if not ok.any(): break
    if not ok.any(): continue
    Yk, Mk = Y[ok], M[ok]; nk = (Yk * Yk).sum(1) - Mk
    sel = ((nk % p == 0) & (nk % (p * p) != 0) if CTRL else (nk % (p * p) == 0)) & (nk > 0)
    for y, m, n in zip(Yk[sel], Mk[sel], nk[sel]):
        hits += 1; pairs.add((int(n), int(m)))
        if m % p: viol.append((y.tolist(), int(n), int(m)))
        e = 0; nn = int(n)
        while nn % p == 0: nn //= p; e += 1
        if not CTRL and ((y[u_perm] - y) % p ** (e // 2)).any(): ma_viol += 1
print(("CONTROL p||n: " if CTRL else "") + f"H=Z{rp}xZ{m2} p={p} c={c}: {total} vectors, {hits} with p^2|n>0 and constant shifts; (n,M) seen {sorted(pairs)[:12]}"
      f"{'...' if len(pairs) > 12 else ''} ({len(pairs)} pairs); violations of p|M: {len(viol)} {viol[:3]}; Ma-step violations: {ma_viol}", flush=True)
