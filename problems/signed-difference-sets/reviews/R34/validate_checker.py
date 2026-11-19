"""Validate check_objects.autocorr_ok / fourier_ok on Gordon's published sets (sds.json)."""
import json, re, sys, importlib.util
import numpy as np
spec = importlib.util.spec_from_file_location("co", sys.argv[2])
src = open(sys.argv[2], encoding="utf-8").read().split("rows = {r")[0]
co = {}
exec(compile(src.replace("ROOT = sys.argv[1]", "ROOT = None"), "co", "exec"), co)
d = json.load(open(sys.argv[1], encoding="utf-8"))
n = good = 0
for key, e in d.items():
    if e.get("status") not in ("Yes", "All") or "sets" not in e:
        continue
    m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", key)
    v, k, lam = int(m.group(1)), int(m.group(2)), int(m.group(3))
    if v > 120:
        continue
    inv = [int(t) for t in m.group(4).split(",")]
    def fac(n):
        f, q = {}, 2
        while q * q <= n:
            while n % q == 0:
                f[q] = f.get(q, 0) + 1; n //= q
            q += 1
        if n > 1: f[n] = f.get(n, 0) + 1
        return f
    c0 = e["sets"][0][0][0]
    ncoord = 1 if isinstance(c0, int) else len(c0)
    if ncoord == len(inv):
        dims = inv
    else:
        dims = []
        for p_ in sorted({q for x in inv for q in fac(x)}):
            dims += sorted(p_ ** fac(x)[p_] for x in inv if p_ in fac(x))
        if len(dims) != ncoord:
            print("skip", key); continue
    for s in e["sets"][:1]:
        D = np.zeros(dims, dtype=np.int64)
        for sign, part in ((1, s[0]), (-1, s[1])):
            for c in part:
                c = (c,) if isinstance(c, int) else tuple(c)
                D[c] = sign
        a = co["autocorr_ok"](D, k, lam)[0]; f = co["fourier_ok"](D, k, lam)[0]
        n += 1; good += (a and f)
        if not (a and f):
            print("fail", key)
print(f"{good}/{n} Gordon sets (v<=120) pass both checks")
