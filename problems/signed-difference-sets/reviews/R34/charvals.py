"""Distinct character values chi(D), chi != 1, of the I19 sets (with multiplicities)."""
import sys, numpy as np
from collections import Counter
src = open("R34/check_objects.py", encoding="utf-8").read().split("rows = {r")[0]
co = {}; exec(compile(src.replace("ROOT = sys.argv[1]", "ROOT = None"), "co", "exec"), co)
for o in [64, 65, 66, 67, 61, 62, 63]:
    dims, v, k, lam, D = co["parse_object"](f"objects/O{o}.txt")
    F = np.fft.fftn(D.astype(float)).ravel()[1:]
    c = Counter((round(z.real, 4) + 0.0, round(z.imag, 4) + 0.0) for z in F)
    print(f"O{o} ({v},{k},{lam}) sqrt(v)/2={np.sqrt(v)/2:.4f}:", sorted(c.items())[:10])
