import re, sys, os, importlib.util
spec = importlib.util.spec_from_file_location("c4", "check4.py")
src = open("check4.py").read().split("rows = {")[0]
ns = {}; exec(src, ns)
ROOT = "../../../lean/SignedDifferenceSets/TomographyQuotRows/"
for rid, (v, k, lam) in {"N15384": (245, 76, 5), "N31745": (343, 82, 11), "N32195": (343, 334, 291), "N15414": (245, 121, 50),
                         "N15434": (245, 144, 73), "N31778": (343, 130, 3), "N5089": (147, 134, 7)}.items():
    t = open(ROOT + rid + ".lean", encoding="utf-8").read()
    m = re.search(r"def w : List \(List ℤ\) :=\s*\[(.*?)\]\n\n", t, re.S)
    w = {tuple(int(x) for x in g.split(",")) for g in re.findall(r"\[([-\d, ]+)\]", m[1])}
    p = 7; c = v // 49; import math; s = math.isqrt(k + lam * (v - 1))
    V = ns["vectors"](p, c * p, s, k - lam + lam * c * p, lam * c * p, k)
    C = {Y for Y in V if sum(t_ * y for t_, y in enumerate(Y)) % p == 0}
    print(rid, "row w", len(w), "mine", len(C), "equal" if w == C else "DIFFER", sorted(w)[:1])
