"""Refuter's independent integer marked-count test (C7, integer form).

Exact DP over the allowed values: state (used, sum, sqsum) -> max sum of maxm; no pruning
except sqsum <= Q (squares are nonnegative). Also lists all moment solutions when few,
and the LP optimum (scipy) for comparison.
"""
import sys
from itertools import product

def maxm(c, x):
    return c if (c - x) % 2 == 0 else c - 1

def allowed(q, t0, c):
    return [x for x in range(-c, c + 1) if (x - t0) % q == 0]

def best_int(vals, N, s, Q, c):
    """Max sum of maxm over nonnegative integer counts on vals with N, s, Q; None if none."""
    states = {(0, 0, 0): 0}
    for x in vals:
        new = {}
        mx, x2 = maxm(c, x), x * x
        for (n, sm, sq), m in states.items():
            i = 0
            while n + i <= N and sq + i * x2 <= Q:
                key = (n + i, sm + i * x, sq + i * x2)
                v = m + i * mx
                if new.get(key, -1) < v:
                    new[key] = v
                i += 1
                if x2 == 0 and i > N:  # x = 0: bounded by N
                    break
        states = new
    return states.get((N, s, Q))

def solutions(vals, N, s, Q, c, limit=50):
    out = []
    def rec(i, n, sm, sq, cur):
        if len(out) >= limit:
            return
        if i == len(vals):
            if n == N and sm == s and sq == Q:
                out.append(dict(cur))
            return
        x = vals[i]
        j = 0
        while n + j <= N and sq + j * x * x <= Q:
            if j:
                cur[x] = j
            rec(i + 1, n + j, sm + j * x, sq + j * x * x, cur)
            cur.pop(x, None)
            j += 1
            if x == 0 and j > N:
                break
    rec(0, 0, 0, 0, {})
    return out

def lp_max(vals, N, s, Q, c):
    from scipy.optimize import linprog
    A = [[1] * len(vals), vals, [x * x for x in vals]]
    r = linprog([-maxm(c, x) for x in vals], A_eq=A, b_eq=[N, s, Q], bounds=[(0, None)] * len(vals),
                method="highs")
    return -r.fun if r.status == 0 else None

if __name__ == "__main__":
    v, k, lam, N, q = 320, 306, 162, 32, 3
    c = v // N
    Q = k + lam * (c - 1)
    s2 = k + lam * (v - 1)
    s = int(round(s2 ** 0.5)); assert s * s == s2
    print("c", c, "Q", Q, "s", s, "n", k - lam)
    for sp in (s, -s):
        for t0 in range(q):
            vals = allowed(q, t0, c)
            b = best_int(vals, N, sp, Q, c)
            sols = solutions(vals, N, sp, Q, c)
            lp = lp_max(vals, N, sp, Q, c)
            print(sp, t0, vals, "int max", b, "LP max", lp, "nsol", len(sols))
            for so in sols:
                print("   ", so, "maxm", sum(n * maxm(c, x) for x, n in so.items()))
    # sharpness: with k lowered the vector exists
