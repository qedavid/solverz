"""Check 5: Remark rem:z18, "on the open cases of the table both versions settle the same cases".
Weak version (Thm z18 / Lean GaussKills): for both s' and EVERY R in [1, N] with N - R even, 0 unreachable mod N.
Strong version: only the true R = |H/2H| = 2^(a+b) for H = C2^a x C4^b.
For every Open@ row with n = m^2 and s^2 = k + lam(v-1) squares, and EVERY exponent-4 quotient type H of G
(H = C2^a x C4^b, b <= y, a + b <= x + y, where G/4G = C2^x x C4^y), compare: settled_weak = any H weak-kills,
settled_strong = any H strong-kills. Also: every quotient a Lean row of GaussCharsRows uses."""
import re, csv, math, sys
PF = "problems/signed-difference-sets/"

def Xset(m):
    return [x for x in range(-m, m + 1) if math.isqrt(m * m - x * x) ** 2 == m * m - x * x]

def kill_table(N, m, s):
    """Return dict R -> True if the congruence is unsolvable for both s' at this R (R in [1,N], N-R even)."""
    full = (1 << N) - 1
    def rot(mask, d):
        d %= N
        return ((mask << d) | (mask >> (N - d))) & full
    steps = sorted(set((2 * x) % N for x in Xset(m)))
    S = 1  # j = 0: {0}
    out = {}
    j = 0
    while True:
        R = N - 2 * j
        if R < 1: break
        # signs: m * t, t = R-1 mod 2, |t| <= R-1
        ok = True
        for sp in (s, -s):
            for t in range(-(R - 1), R, 2):
                need = (-(sp + m * t)) % N
                if (S >> need) & 1: ok = False; break
            if not ok: break
        out[R] = ok
        nS = 0
        for d in steps: nS |= rot(S, d)
        S = nS; j += 1
    return out

cache = {}
def kills(N, m, s):
    key = (N, m, s % N if N else 0)
    if key not in cache: cache[key] = kill_table(N, m, s)
    return cache[key]

rows = list(csv.DictReader(open(PF + "instances.csv", encoding="utf-8")))
stats = dict(rows=0, applicable=0, weak=0, strong=0, diff=0, maxN=0)
diffs = []
for row in rows:
    pass
    mm = re.match(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", row["key"])
    v, k, lam = int(mm.group(1)), int(mm.group(2)), int(mm.group(3)); ms = [int(x) for x in mm.group(4).split(",")]
    stats["rows"] += 1
    nn, s2 = k - lam, k + lam * (v - 1)
    if nn < 0 or s2 < 0: continue
    m, s = math.isqrt(nn), math.isqrt(s2)
    if m * m != nn or s * s != s2: continue
    x = sum(1 for d in ms if d % 4 == 2); y = sum(1 for d in ms if d % 4 == 0)
    if x + y == 0: continue
    stats["applicable"] += 1
    w = st = False; wH = sH = None
    for b in range(0, y + 1):
        for a in range(0, x + y - b + 1):
            if a + b == 0: continue
            N = 2 ** a * 4 ** b; Rt = 2 ** (a + b)
            stats["maxN"] = max(stats["maxN"], N)
            T = kills(N, m, s)
            if all(T.values()) and not w: w = True; wH = (a, b)
            if T[Rt] and not st: st = True; sH = (a, b)
    stats["weak"] += w; stats["strong"] += st
    if w != st: stats["diff"] += 1; diffs.append((row["id"], row["key"], row["status"], sH))
print(stats)
for d in diffs[:40]: print("  strong only:", d)

# the Lean rows' quotients
txt = open(PF + "lean/SignedDifferenceSets/GaussCharsRows.lean", encoding="utf-8").read()
lr = re.findall(r"\(⟨(\d+), \[([\d, ]+)\], (\d+), (-?\d+)⟩, ⟨\[([\d, ]+)\], (-?\d+), (-?\d+)⟩\)", txt)
Ns = {}
bad = 0
for (i, ms, k, lam, ds, m, s) in lr:
    ds = [int(t) for t in ds.split(",")]; m, s = int(m), int(s)
    N = 1
    for d in ds: N *= d
    a = sum(1 for d in ds if d == 2); b = sum(1 for d in ds if d == 4)
    Ns[N] = Ns.get(N, 0) + 1
    T = kills(N, m, s)
    if not all(T.values()): bad += 1; print("row", i, "weak kill fails")
    if not T[2 ** (a + b)]: bad += 1; print("row", i, "strong kill fails")
print(f"Lean GaussCharsRows: {len(lr)} entries; quotient orders used: {dict(sorted(Ns.items()))}; failures {bad}")
