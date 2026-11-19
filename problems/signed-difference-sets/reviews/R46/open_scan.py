"""Informational: every open row of instances.csv, every admissible (p, l, j, K) as in exists_check.py; a row is
count-killed when Q, s' or t is not integral or the Lean-port anyCountsMag (amax = floor(k/p^l)) is false; kills are
confirmed by the DP (no absolute-sum bound) when Q <= 3000. Lists kills outside the 52 C39 rows."""
import math, itertools, sys, ast
import rowparse as R
import countsgo as CG
from exists_check import factor, partitions_dominated, selfconj_exp
from check_rows import vp, min_nonzero
class Cap(Exception): pass
def capped_count(c, N, s, Q, A, cap=200000):
    ctr = [0]
    orig = CG.countsGo
    def go(xs, N_, s_, Q_, A_, ctr_):
        if ctr_[0] > cap: raise Cap()
        return orig(xs, N_, s_, Q_, A_, ctr_)
    CG.countsGo = go
    try: return CG.anyCountsMag(c, N, s, Q, A, ctr)
    except Cap: return None
    finally: CG.countsGo = orig
I = R.instances()
c52 = {ast.literal_eval(l)["name"] for l in open("check_rows.out") if "MaCountRows" in l}
kills, nonint, unknown = {}, {}, 0
for nid, r in I.items():
    if r["status"] != "open": continue
    v, k, lam, ms = r["v"], r["k"], r["lam"], r["ms"]; n = k - lam
    if n <= 0: continue
    S2 = k + lam * (v - 1); s = math.isqrt(S2) if S2 >= 0 else -1
    if s * s != S2: continue
    gp = {}
    for m in ms:
        for q, e in factor(m).items(): gp.setdefault(q, []).append(e)
    for q in gp: gp[q].sort(reverse=True)
    for p in sorted(factor(n)):
        b = vp(n, p) // 2
        if b < 1 or p not in gp: continue
        others = [q for q in gp if q != p]
        for combo in itertools.product(*[[(q, mu) for mu in partitions_dominated(gp[q])] for q in others]) if others else [()]:
            expK = math.prod(q ** (mu[0] if mu else 0) for q, mu in combo)
            if not selfconj_exp(p, expK): continue
            Kord = math.prod(q ** sum(mu) for q, mu in combo)
            for j in range(1, gp[p][0] + 1):
                for l in (1, 2):
                    if l > b or l > j: continue
                    c = v // (p ** j * Kord); N = p ** (j - l) * Kord
                    tag = (p, l, j, combo)
                    if (k + lam * (p ** l * c - 1)) % p ** (2 * l) or s % p ** l or (lam * c) % p ** l:
                        nonint.setdefault(nid, tag); continue
                    Q = (k + lam * (p ** l * c - 1)) // p ** (2 * l); s1 = s // p ** l
                    res = capped_count(c, N, s1, Q, k // p ** l)
                    if res is None: unknown += 1
                    elif res is False:
                        dp = None if Q > 3000 else (min_nonzero(c, Q, s1) is None or min_nonzero(c, Q, s1) > N or (Q - s1) % 2 != 0)
                        kills.setdefault(nid, (tag, Q, s1, c, N, dp))
print("open rows count-killed:", len(kills), "of which in C39's 52:", len(set(kills) & c52), "outside:", len(set(kills) - c52))
print("C39 rows not found:", sorted(c52 - set(kills)))
print("rows with a non-integral Q/s'/t (an existing SDS would contradict):", len(nonint), "outside kills:", len(set(nonint) - set(kills)))
print("count searches capped:", unknown)
for x in sorted(set(kills) - c52, key=lambda t: int(t[1:]))[:40]: print("EXTRA", x, I[x]["k"], I[x]["lam"], I[x]["ms"], kills[x])
for x in sorted(set(nonint) - set(kills), key=lambda t: int(t[1:]))[:10]: print("NONINT", x, I[x]["k"], I[x]["lam"], I[x]["ms"], nonint[x])
