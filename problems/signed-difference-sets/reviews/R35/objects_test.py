"""Intermediate claims of C29 on every known set in objects/ (O*.txt): for each prime p with b >= 1, each cyclic
p-part Z_{p^j} (from one p-primary factor), each d | exp(p'-part) with p self-conjugate mod d, the coordinate quotient
H = Z_{p^j} x K_d: check (a) p^b | Y(h+u) - Y(h) for u of order p, (b) q^{j_q} | Y(h) - Y(h') for each q of C29,
(c) the combined p^b Q divides the differences along u, (d) 2c >= p^b Q (else the object would contradict C29)."""
import itertools, math, re
from pathlib import Path
from scan import factor, selfconj, vp, divisors_of

ROOT = Path(__file__).resolve().parents[3]
HEAD = re.compile(r"^(\S+) \((-?\d+),(-?\d+),(-?\d+)\)")
stats = {"objects": 0, "quotients": 0, "a_fail": 0, "b_fail": 0, "with_q": 0, "bound_hit": 0, "not_sds": 0}
for f in sorted((ROOT / "objects").glob("O*.txt")):
    lines = f.read_text(encoding="utf-8").split("\n")
    m = HEAD.match(lines[0])
    ms = [int(x) for x in m[1].replace("C", "").split("x")]
    v, k, lam = int(m[2]), int(m[3]), int(m[4])
    D = {}
    for ln in lines[1:]:
        t = ln.split()
        if len(t) == len(ms) + 1:
            D[tuple(int(x) for x in t[:-1])] = 1 if t[-1] == "+" else -1
    G = list(itertools.product(*[range(x) for x in ms]))
    # sanity: it is an SDS
    ok = len(D) == k and all(sum(D.get(x, 0) * D.get(tuple((a + b) % mm for a, b, mm in zip(x, g, ms)), 0) for x in D)
                             == lam for g in G if any(g))
    if not ok:
        stats["not_sds"] += 1
        continue
    stats["objects"] += 1
    n = k - lam
    nf = factor(abs(n)) if n else {}
    # primary factors: (factor index, prime, exponent)
    prim = [(t, l, e) for t, mm in enumerate(ms) for l, e in factor(mm).items()]
    for p, e in nf.items():
        b = e // 2
        pf = [(t, ee) for t, l, ee in prim if l == p]
        if b == 0 or not pf:
            continue
        others = [(t, l, ee) for t, l, ee in prim if l != p]
        expo = math.prod(l ** ee for _, l, ee in others) if others else 1
        expo = math.lcm(1, *[l ** ee for _, l, ee in others])
        for (tp, ep) in pf:
            for j in range(1, ep + 1):
                for d in divisors_of(expo):
                    if d > 1 and not selfconj(p, d):
                        continue
                    comps = [(tp, p ** j)] + [(t, l ** min(ee, vp(d, l))) for t, l, ee in others if vp(d, l) > 0]
                    H = math.prod(x for _, x in comps)
                    c = v // H
                    Y = {}
                    for x in G:
                        h = tuple(x[t] % mod for t, mod in comps)
                        Y[h] = Y.get(h, 0) + D.get(x, 0)
                    hs = list(itertools.product(*[range(mod) for _, mod in comps]))
                    stats["quotients"] += 1
                    u = p ** (j - 1)
                    diffs = [Y.get(((h[0] + u) % (p ** j),) + h[1:], 0) - Y.get(h, 0) for h in hs]
                    if any(dd % p ** b for dd in diffs):
                        stats["a_fail"] += 1
                        print("A FAIL", f.name, ms, (v, k, lam), p, j, d)
                    m_ = math.lcm(p ** j, d)
                    qs = [(q, nf[q] // 2) for q in nf if q != p and d % q and nf[q] >= 2 and selfconj(q, m_)]
                    Q = math.prod(q ** jq for q, jq in qs)
                    if qs:
                        stats["with_q"] += 1
                        y0 = Y.get(hs[0], 0)
                        if any((Y.get(h, 0) - y0) % Q for h in hs):
                            stats["b_fail"] += 1
                            print("B FAIL", f.name, ms, (v, k, lam), p, j, d, qs)
                    if 2 * c < p ** b * Q:
                        stats["bound_hit"] += 1
                        print("BOUND HIT (object contradicts C29!)", f.name, ms, (v, k, lam), p, j, d, qs)
print(stats)
