"""O103 structure: support by cosets of H = {x : 3x = 0} in C3^3 x C9, and the x0-coset part."""
import numpy as np, itertools
src = open("R34/check_objects.py", encoding="utf-8").read().split("rows = {r")[0]
co = {}; exec(compile(src.replace("ROOT = sys.argv[1]", "ROOT = None"), "co", "exec"), co)
dims, v, k, lam, D = co["parse_object"]("objects/O103.txt")
cos = {}
for x in itertools.product(*[range(d) for d in dims]):
    if D[x]:
        cos.setdefault(x[3] % 3, []).append((x, int(D[x])))
for c, L in sorted(cos.items()):
    print("coset d mod 3 =", c, "size", len(L), "+", sum(s > 0 for _, s in L), "-", sum(s < 0 for _, s in L))
# coset 1: is it x0 + subgroup of order 9?
L1 = [x for x, s in cos.get(1, [])]
if L1:
    x0 = L1[0]
    S = {tuple((a - b) % d for a, b, d in zip(x, x0, dims)) for x in L1}
    closed = all(tuple((a + b) % d for a, b, d in zip(s, t, dims)) in S for s in S for t in S)
    print("coset-1 part = x0 + subgroup:", closed, "x0 =", x0, "subgroup:", sorted(S))
print("coset 2 empty:", 2 not in cos)
