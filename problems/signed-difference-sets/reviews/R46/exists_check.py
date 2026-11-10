"""Every `exists` row (and, with argv[1] = open, every open row) of instances.csv against C39/C38's demands on every
admissible quotient: p | n prime with b = floor(v_p(n)/2) >= 1, l in {1, 2}, l <= b, H = Z_{p^j} x K (j >= l) a quotient
of G (per-prime partition domination), K of order prime to p with p^i = -1 mod exp K. An existing SDS must give integral
Q, s', t and feasible value counts (and, at l = 1, feasible counts within one residue class mod M). Own code."""
import sys, math, itertools, functools
import numpy as np
import rowparse as R
from check_rows import isprime, vp
def factor(x):
    out = {}; d = 2
    while d * d <= x:
        while x % d == 0: out[d] = out.get(d, 0) + 1; x //= d
        d += 1
    if x > 1: out[x] = out.get(x, 0) + 1
    return out
def partitions_dominated(lam):
    """all partitions mu (descending, positive) with mu_i <= lam_i (lam descending)"""
    res = []
    def rec(i, prev, cur):
        res.append(tuple(cur))
        if i == len(lam): return
        for a in range(1, min(prev, lam[i]) + 1):
            rec(i + 1, a, cur + [a])
    rec(0, 10**9, [])
    return res
def selfconj_exp(p, m):
    if m <= 2: return True
    if math.gcd(p, m) != 1: return False
    x = p % m
    for _ in range(2 * m + 2):
        if (x + 1) % m == 0: return True
        x = x * p % m
    return False
@functools.lru_cache(maxsize=None)
def dp_table(c, Q):
    """min #nonzero values in [-c, c]\{0} for square sum Q and each sum (index sum + Q)"""
    INF = 10**9
    best = np.full((Q + 1, 2 * Q + 1), INF, dtype=np.int64); best[0, Q] = 0
    for q in range(1, Q + 1):
        for m in range(1, c + 1):
            if m * m > q: break
            prev = best[q - m * m]
            best[q, m:] = np.minimum(best[q, m:], prev[:-m] + 1)
            best[q, :-m] = np.minimum(best[q, :-m], prev[m:] + 1)
    return best
def counts_feasible(c, N, s, Q):
    if Q < 0 or abs(s) > Q or (Q - s) % 2: return False
    if Q > 3000: return True  # not checked (too large for the table)
    return dp_table(c, Q)[Q, Q + s] <= N
def res_feasible(c, N, s, Q, M):
    """some class a mod M and N values in [-c, c], all = a mod M, with sum s and square sum Q (exact DP on counts)"""
    for a in range(M):
        vals = [x for x in range(-c, c + 1) if (x - a) % M == 0]
        # reachable (count, sum, sq) with count <= N; sets of (sum, sq) per count
        cur = {(0, 0)}
        for _ in range(N):
            nxt = set()
            for (su, sq) in cur:
                for x in vals:
                    q2 = sq + x * x
                    if q2 <= Q: nxt.add((su + x, q2))
            cur = nxt
            if not cur: break
        if (s, Q) in cur or (-s, Q) in cur: return True
    return False
def main(which):
    I = R.instances()
    stats = dict(rows=0, certs=0, bad=[], res_certs=0, res_skipped=0, big_skipped=0)
    for nid, r in I.items():
        if r["status"] != which: continue
        v, k, lam, ms = r["v"], r["k"], r["lam"], r["ms"]
        n = k - lam
        if n <= 0: continue
        S2 = k + lam * (v - 1)
        s = math.isqrt(S2) if S2 >= 0 else -1
        if s * s != S2: continue
        stats["rows"] += 1
        # per-prime partitions of G
        gp = {}
        for m in ms:
            for q, e in factor(m).items(): gp.setdefault(q, []).append(e)
        for q in gp: gp[q].sort(reverse=True)
        for p in sorted(factor(n)):
            e = vp(n, p); b = e // 2
            if b < 1 or p not in gp: continue
            J = gp[p][0]
            others = [q for q in gp if q != p]
            # K: product over q of a dominated partition, with p self-conjugate mod exp K
            choices = [[(q, mu) for mu in partitions_dominated(gp[q])] for q in others]
            for combo in itertools.product(*choices) if choices else [()]:
                expK = math.prod(q ** (mu[0] if mu else 0) for q, mu in combo)
                if not selfconj_exp(p, expK): continue
                Kord = math.prod(q ** sum(mu) for q, mu in combo)
                for j in range(1, J + 1):
                    for l in (1, 2):
                        if l > b or l > j: continue
                        Hord = p ** j * Kord
                        if v % Hord: continue
                        c = v // Hord; N = p ** (j - l) * Kord
                        stats["certs"] += 1
                        bad = []
                        if (k + lam * (p ** l * c - 1)) % p ** (2 * l): bad.append("Q int")
                        if s % p ** l: bad.append("s' int")
                        if (lam * c) % p ** l: bad.append("t int")
                        if not bad:
                            Q = (k + lam * (p ** l * c - 1)) // p ** (2 * l); s1 = s // p ** l
                            if Q > 3000: stats["big_skipped"] += 1
                            elif not counts_feasible(c, N, s1, Q): bad.append("counts")
                            if l == 1 and not bad:
                                M = 1
                                for q in factor(n):
                                    if q == p or N % q == 0: continue
                                    jq = vp(n, q) // 2
                                    if jq and selfconj_exp(q, math.lcm(p ** (j - 1), expK)): M *= q ** jq
                                if M > 1:
                                    if N * len(range(-c, c + 1)) > 4000 or N > 200: stats["res_skipped"] += 1
                                    else:
                                        stats["res_certs"] += 1
                                        if not res_feasible(c, N, s1, Q, M): bad.append(f"res counts M={M}")
                        if bad: stats["bad"].append((nid, v, k, lam, ms, p, j, l, combo, bad))
    print({x: (y if x != "bad" else len(y)) for x, y in stats.items()})
    for x in stats["bad"][:40]: print("BAD", x)
if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "exists")
