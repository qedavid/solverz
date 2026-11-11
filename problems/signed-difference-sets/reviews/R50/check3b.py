"""Check 3b: C45's twist_facts on known sets: maps onto Z_2 x K (K = Z_r, r in 3,5,11,13 with 2 self-conjugate, or Z_3^2),
2^(2j) | n: z and d constant mod 2^j, z +- d = 2W, |W| <= c, sum|W| <= k."""
import glob, re, os, itertools, math
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../.."))
SC = {3: 1, 5: 2, 11: 5, 13: 6}  # 2^i = -1 mod r
tested = bad = 0
for f in sorted(glob.glob(os.path.join(ROOT, "objects/O*.txt")), key=lambda s: int(re.findall(r"O(\d+)", s)[0])):
    L = open(f).read().strip().split("\n")
    m = re.match(r"(\S+) \((\d+),(-?\d+),(-?\d+)\)", L[0])
    ms = [int(x) for x in re.findall(r"\d+", m[1])]; v, k, lam = int(m[2]), int(m[3]), int(m[4]); n = k - lam
    if v % 2 or n <= 0: continue
    j = 0
    while n % (4 ** (j + 1)) == 0: j += 1
    if j == 0: continue
    D = {}
    for ln in L[1:]:
        a = ln.split(); D[tuple(int(x) for x in a[:-1])] = 1 if a[-1] == "+" else -1
    if len(ms) > 4: continue
    ev = [i for i, x in enumerate(ms) if x % 2 == 0]
    eps_list = [a for a in itertools.product(range(2), repeat=len(ev)) if any(a)][:6]
    for r in SC:
        idx = [i for i, x in enumerate(ms) if x % r == 0]
        if not idx: continue
        for K2 in (False, True):
            if K2 and (r != 3 or len(idx) < 2): continue
            homs = [b for b in itertools.product(range(r), repeat=len(idx)) if any(b)][:8]
            pairs = [(b,) for b in homs] if not K2 else [(b1, b2) for b1 in homs for b2 in homs
                     if not any(all((x * u + y * w) % r == 0 for u, w in zip(b1, b2)) for x in range(r) for y in range(r) if (x, y) != (0, 0))][:6]
            for bs in pairs:
                for e in eps_list:
                    M = 2 ** j; c = v // (2 * r ** len(bs))
                    z, d, W = {}, {}, {}
                    for x, val in D.items():
                        h = tuple(sum(bi * x[i] for bi, i in zip(b, idx)) % r for b in bs)
                        ee = sum(ai * x[i] for ai, i in zip(e, ev)) % 2
                        z[h] = z.get(h, 0) + val; d[h] = d.get(h, 0) + val * (-1) ** ee
                        W[(ee, h)] = W.get((ee, h), 0) + val
                    Ks = list(itertools.product(range(r), repeat=len(bs)))
                    zz = [z.get(h, 0) for h in Ks]; dd = [d.get(h, 0) for h in Ks]
                    ok = len({x % M for x in zz}) == 1 and len({x % M for x in dd}) == 1
                    ok &= sum(dd) ** 2 == n and max(abs(w) for w in W.values()) <= c and sum(map(abs, W.values())) <= k
                    ok &= all(zz[i] + dd[i] == 2 * W.get((0, h), 0) and zz[i] - dd[i] == 2 * W.get((1, h), 0) for i, h in enumerate(Ks))
                    tested += 1; bad += not ok
                    if not ok: print("FAIL", os.path.basename(f), m[1], (v, k, lam), r, bs, e, zz, dd)
            print(os.path.basename(f), m[1], (v, k, lam), "n", n, "j", j, "K", f"Z_{r}^{2 if K2 else 1}", "maps so far", tested, flush=True)
print("tested", tested, "failures", bad)
