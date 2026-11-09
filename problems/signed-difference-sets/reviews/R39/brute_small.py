"""Exhaustive: every f : Z_m -> [-c, c] with autocorrelation n[g=0] + mu (n > 0), for the theorem's general aux form
(any integer f, not only coset sums). For each odd p with p^2 | m: if M1's q-condition holds for n, the bound
phi(m) n <= m (m/p) c^2 must hold. Prints violations, and n beyond the bound where the q-condition fails (controls)."""
import sys, itertools
import numpy as np
from indep import factor, phi, powers, qfree

def run(m, c, chunk_digits):
    vals = np.arange(-c, c + 1, dtype=np.int64)
    b = 2 * c + 1
    ps = [p for p in factor(m) if p != 2 and m % (p * p) == 0]
    # split coordinates: outer digits (python loop) and inner (numpy grid)
    inner = chunk_digits
    outer = m - inner
    grid = np.array(list(itertools.product(range(b), repeat=inner)), dtype=np.int64) - c  # (b^inner, inner)
    found = {}
    for o in itertools.product(range(-c, c + 1), repeat=outer):
        F = np.empty((grid.shape[0], m), dtype=np.int64)
        F[:, :outer] = o
        F[:, outer:] = grid
        A = [np.einsum('ij,ij->i', F, np.roll(F, -g, axis=1)) for g in range(m // 2 + 1)]
        ok = np.ones(grid.shape[0], dtype=bool)
        for g in range(2, m // 2 + 1):
            ok &= A[g] == A[1]
        nn = A[0] - A[1]
        ok &= nn > 0
        for i in np.nonzero(ok)[0]:
            key = (int(nn[i]), int(A[1][i]))
            if key not in found:
                found[key] = F[i].tolist()
    viol, ctrl = [], []
    for (n, mu), f in sorted(found.items()):
        for p in ps:
            Fm = m // p
            t = 1 + Fm
            hyp = all(qfree(m, q) == 1 or t % qfree(m, q) in powers(q % qfree(m, q), qfree(m, q)) for q in factor(n))
            within = phi(m) * n <= m * Fm * c * c
            if hyp and not within:
                viol.append((n, mu, p, f))
            if not hyp and not within:
                ctrl.append((n, mu, p, f))
    ns = sorted({n for n, _ in found})
    print(f'm={m} c={c}: {len(found)} (n, mu) classes; n values {ns}')
    print('  VIOLATIONS', viol)
    print('  controls (q-condition fails, bound exceeded):', [(n, mu, p) for n, mu, p, _ in ctrl][:20])
    for n, mu, p, f in ctrl[:3]:
        print('   e.g.', n, mu, p, f)
    sys.stdout.flush()

if __name__ == '__main__':
    m, c, d = map(int, sys.argv[1:4])
    run(m, c, d)
