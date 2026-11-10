"""Part B: C41 rows built after R47. Statement vs instances.csv; multiplier t checked against C10 (own factoring);
own list of line vectors (Demands with fibres c*p, sum s, moment 0 and t-fixed when p !| s; all when p | s);
own meet-in-the-middle search over the p + 1 lines: KILL iff no tuple gives sum_j Y_j(l_j g) - s = p z, |z| <= c at all g."""
import re, sys, os, math, itertools
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from rows import inst, ROOT

def factor(n):
    out = {}; d = 2
    while d * d <= n:
        while n % d == 0: out[d] = out.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out

def mult_ok(p, t, n):
    if n <= 0 or n % p == 0 or t % p in (0, 1): return False
    for q in factor(n):
        if t % p not in {pow(q, f, p) for f in range(p)}: return False
    return True

def vectors(p, C, k, lam, s, centred, t):
    Q = k + lam * (C - 1)
    orbs, seen = [], set()
    for x in range(1, p):
        if x in seen: continue
        o = []; y = x
        while y not in o: o.append(y); y = y * t % p
        seen |= set(o); orbs.append(o)
    B = math.isqrt(Q)
    out = []
    def rec(i, vals, rs, rq):
        if i == len(orbs):
            if rs != 0 or rq != 0: return
            b = [0] * p; b[0] = vals[0]
            for o, v in zip(orbs, vals[1:]):
                for x in o: b[x] = v
            if any(abs(a) > C for a in b): return
            if any(sum(b[h] * b[(h + g) % p] for h in range(p)) != lam * C for g in range(1, p)): return
            A = sum(abs(a) for a in b)
            if A > k or (k - A) % 2: return
            if centred and sum(h * b[h] for h in range(p)) % p: return
            out.append(tuple(b)); return
        m = len(orbs[i])
        if rq < 0: return
        rem = sum(len(o) for o in orbs[i:])
        if rs * rs > rem * rq: return  # Cauchy-Schwarz on the remaining coordinates
        if i == len(orbs) - 1:
            if rs % m == 0: rec(i + 1, vals + [rs // m], 0, rq - m * (rs // m) ** 2)
            return
        lim = math.isqrt(rq // m)
        for v in range(-lim, lim + 1):
            rec(i + 1, vals + [v], rs - m * v, rq - m * v * v)
    for a in range(-B, B + 1):
        if not orbs:
            if a == s and a * a == Q: out.append((a,))
            continue
        rec(0, [a], s - a, Q - a * a)
    return out

def search(p, c, s, L):
    pts = [(a, b) for a in range(p) for b in range(p)]
    def line(j, g): return g[1] if j == 0 else (g[0] + (j - 1) * g[1]) % p
    M = [np.array([[y[line(j, g)] for g in pts] for y in L], dtype=np.int64) for j in range(p + 1)]
    h = (p + 1) // 2
    def half(js):
        S = np.zeros((1, p * p), dtype=np.int64)
        for j in js: S = (S[:, None, :] + M[j][None, :, :]).reshape(-1, p * p)
        return S
    SA, SB = half(range(h)), half(range(h, p + 1))
    if SA.shape[0] * 1.0 * SB.shape[0] == 0: return 0, 0
    keyA = {}
    for i, row in enumerate(SA % p): keyA.setdefault(row.tobytes(), []).append(i)
    need = (s - SB) % p
    integral = 0; boxed = 0
    for i, row in enumerate(need):
        for ia in keyA.get(row.tobytes(), []):
            integral += 1
            tot = SA[ia] + SB[i] - s
            if np.all(np.abs(tot) <= p * c): boxed += 1
    return integral, boxed

if __name__ == '__main__':
    ids = sys.argv[1:]
    D = ROOT + '/lean/SignedDifferenceSets/TomographyQuotRows/'
    for nid in ids:
        txt = open(D + nid + '.lean', encoding='utf-8').read()
        m = re.search(r'theorem not_hasSDS : ¬ HasSDS \(([^)]*)\) (\d+) (-?\d+) :=\s*\n\s*(not_hasSDS_grp\w*) \(ms := \[([\d, ]*)\]\) (\d+)', txt)
        grp = [int(a) for a in re.findall(r'ZMod (\d+)', m[1])]
        k, lam, thm, ms, p = int(m[2]), int(m[3]), m[4], [int(a) for a in m[5].split(',')], int(m[6])
        c = int(re.search(r'\(c := (\d+)\)', txt)[1])
        tm = re.search(r'\(t := (\d+)\)', txt); t = int(tm[1]) if tm else 1
        v, k0, lam0, inv, st = inst[nid]
        prob = []
        if grp != inv or ms != inv: prob.append('group')
        if (k, lam) != (k0, lam0): prob.append('params')
        if c * p * p != v: prob.append('c')
        if sum(1 for n in inv if n % p == 0) < 2: prob.append('rank')
        s = math.isqrt(k + lam * (v - 1))
        if s * s != k + lam * (v - 1): prob.append('s')
        centred = s % p != 0
        if (thm == 'not_hasSDS_grp') != centred: prob.append('route')
        if t != 1 and not mult_ok(p, t, k - lam): prob.append('mult')
        L = vectors(p, c * p, k, lam, s, centred, t if centred else 1)
        integral, boxed = search(p, c, s, L) if L else (0, 0)
        vd = 'KILL' if boxed == 0 else 'SURVIVES'
        print(nid, st, 'stmt', 'OK' if not prob else prob, '| p=%d c=%d s=%d t=%d %s |L|=%d integral=%d boxed=%d | %s' % (
            p, c, s, t, 'centred' if centred else 'nc', len(L), integral, boxed, vd), flush=True)
