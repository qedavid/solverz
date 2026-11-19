"""Each row file's certificate vs my own recomputation: the divided quotient Grp (r :: ks) is isomorphic to the
exploration's H' (same elementary divisors), and the search arguments (c, Q, t, k', s') in the cert and in the
split rows' `check` equal mine (params.py formulas)."""
import re, glob, os, math, sys
R = sys.argv[1]
def elem(ms):
    out = []
    for m in ms:
        x, p = m, 2
        while x > 1:
            if x % p == 0:
                q = 1
                while x % p == 0: x //= p; q *= p
                out.append(q)
            p += 1
    return sorted(out)
x = {l.split(" ")[0]: l.split(" ") for l in open(f"{R}/scratch/x_ma_divided.out", encoding="utf-8").read().splitlines() if " KILL " in l}
bad = 0
for f in sorted(glob.glob(f"{R}/lean/SignedDifferenceSets/MaDividedRows/N*.lean")):
    rid = os.path.basename(f)[:-5]; s = open(f, encoding="utf-8").read()
    m = re.search(r"\(w := ⟨\d+, \[([\d, ]+)\], (\d+), \(?(-?\d+)\)?⟩\)\s*\(c := ⟨(\d+), (\d+), (\d+), (\d+), (\d+), \[([\d, ]+)\],.*?\],\s*(\d+), (-?\d+), (-?\d+), (-?\d+)⟩\)", s, re.S)
    ms = [int(t) for t in m[1].split(",")]; k, lam = int(m[2]), int(m[3])
    p, r, i, e, b = map(int, m.groups()[3:8]); ks = [int(t) for t in m[9].split(",")]
    kp, Q, t, s1 = map(int, m.groups()[9:13])
    v = math.prod(ms); c = v // (r * p * math.prod(ks))
    xl = x[rid]; xe = [int(t) for t in xl[6].strip("[]").split(",")]
    iso = elem([r] + ks) == elem(xe)
    s = math.isqrt(k + lam * (v - 1))
    mine = (c, (k + lam * (p * c - 1)) // (p * p), lam * c // p, k // p if (k // p - k) % 2 == 0 else k // p - 1, s // p)
    ok = iso and (c, Q, t, kp, s1) == mine and int(xl[4]) == p and r == p ** (int(xl[5]) - 1) and b == e // 2 >= 1
    chk = os.path.join(f[:-5], "Check.lean")
    if os.path.exists(chk):
        cs = open(chk, encoding="utf-8").read()
        mm = re.search(r"Grp \[([\d, ]+)\]\) _ \(Grp.indexed _ hpos\)\)\s*\((\d+) : ℕ\) \((-?\d+) : ℤ\) \((-?\d+) : ℤ\) \((\d+) : ℕ\) (-?\d+) p", cs)
        ok = ok and [int(t) for t in mm[1].split(",")] == [r] + ks and tuple(map(int, mm.groups()[1:])) == mine
    bad += not ok
    print(rid, "Grp", [r] + ks, "H'", xe, "c,Q,t,k',s'", (c, Q, t, kp, s1), "split" if os.path.exists(chk) else "single", "OK" if ok else "MISMATCH")
print("mismatches:", bad)
