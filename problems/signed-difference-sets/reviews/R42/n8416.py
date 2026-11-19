"""N8416 SDS(189,65,2,[3,63]), p = 3, H' = Z21, c = 3: Z with Q = 9, t = 2, s' = 7, k' = 21. Profiles by profiles.py,
then every arrangement with Z(0) fixed (vectorised over supports)."""
import itertools, numpy as np
from profiles import profiles
N, c, Q, t, s, kp = 21, 3, 9, 2, 7, 21
ps = profiles(N, c, Q, s, kp); print("profiles:", ps)
hits = 0
for pr in ps:
    nz = {a: m for a, m in pr.items() if a != 0}
    a0 = min(nz, key=lambda a: nz[a]); rest = dict(nz); rest[a0] -= 1
    vals = [a for a, m in rest.items() for _ in range(m)]
    assert len(set(vals)) == 1
    for sup in itertools.combinations(range(1, N), len(vals)):
        Z = np.zeros(N, np.int64); Z[0] = a0; Z[list(sup)] = vals[0]
        ac = np.array([int(Z @ np.roll(Z, -g)) for g in range(1, N)])
        if (ac == t).all(): hits += 1; print("found", Z)
print("vectors found:", hits)
