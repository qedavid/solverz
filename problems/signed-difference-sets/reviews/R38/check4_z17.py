"""Check 4: Remark rem:z17 (closed form, monotonicity, best r = R, Lean rows) and Remark rem:z25 (z25a/b contain z17)."""
import re, csv
INF = 10 ** 9
def v2(x):
    if x == 0: return INF
    x = abs(x); k = 0
    while x % 2 == 0: x //= 2; k += 1
    return k

def hyp17(s, m, r):  # Theorem z17's hypothesis, literally (as in Lean's hkill)
    M = 2 ** r
    return all((sp + m * T) % M != 0 for sp in (s, -s) for T in range(-(M - 1), M, 2))

def closed17(s, m, r):
    return min(v2(s), r) != min(v2(m), r)

def lean_kills_tail(s, m, r):  # RcCert.Kills' last conjunct: T = 2j + 1 - 2^r, j < 2^r
    M = 2 ** r
    return all((sp + m * (2 * j + 1 - M)) % M != 0 for sp in (s, -s) for j in range(M))

# (a) closed form, (b) monotone, Lean's enumeration of T equals the theorem's
bad = 0; n = 0
for r in range(1, 9):
    for m in range(-70, 71):
        for s in range(0, 260):
            n += 1
            h = hyp17(s, m, r)
            if h != closed17(s, m, r): bad += 1; print("closed form fails", s, m, r)
            if h != lean_kills_tail(s, m, r): bad += 1; print("Lean T-range differs", s, m, r)
            if r < 8 and h and not hyp17(s, m, r + 1): bad += 1; print("not monotone", s, m, r)
print(f"(a,b) {n} triples (r 1..8, |m| <= 70, 0 <= s < 260): mismatches {bad}")

# (d) z25a (q = 2 and q = 4, max b) and z25b on H = C2^t, t = r, versus z17
def z25a_kills(s, nn, t, phi):
    e = INF if nn == 0 else v2(nn)
    # largest b >= 1 with 2((b-1)phi + 1) <= e phi
    if e >= INF: b = INF
    else:
        b = 0
        while 2 * ((b) * phi + 1) <= e * phi: b += 1   # tests b+1
    if b < 1: return False
    return s % (2 ** min(t, b)) != 0
def z25b_kills(s, m, t):
    if m == 0: return False
    w = v2(m)
    return w < t and s % (2 ** (w + 1)) == 0
bad = 0; cnt = [0, 0, 0]
for t in range(1, 9):
    for m in range(-70, 71):
        for s in range(0, 260):
            k17 = hyp17(s, m, t)
            ka2 = z25a_kills(s, m * m, t, 1); ka4 = z25a_kills(s, m * m, t, 2); kb = z25b_kills(s, m, t)
            if ka2 != ka4: cnt[2] += 1
            if k17 != (ka2 or kb): bad += 1
            cnt[0] += k17; cnt[1] += (ka2 or kb)
print(f"(d) z17 kill <=> (z25a or z25b) kill on H = C2^t: mismatches {bad}; z17 kills {cnt[0]}, z25 kills {cnt[1]}; "
      f"q=2 vs q=4 differ on {cnt[2]}")

# (c) the Lean rows: parse, check r = number of even factors, re-decide the kill, and compare with instances.csv
PF = "problems/signed-difference-sets/"
txt = open(PF + "lean/SignedDifferenceSets/RealCharsRows.lean", encoding="utf-8").read()
rows = re.findall(r"\(⟨(\d+), \[([\d, ]+)\], (\d+), (-?\d+)⟩, ⟨(\d+), (-?\d+), (-?\d+)⟩\)", txt)
inst = {}
for row in csv.DictReader(open(PF + "instances.csv", encoding="utf-8")):
    inst[row["id"]] = row
bad = 0; notR = 0; R_only = 0; ids = set()
for (i, ms, k, lam, r, s, m) in rows:
    ms = [int(x) for x in ms.split(",")]; k, lam, r, s, m = int(k), int(lam), int(r), int(s), int(m)
    v = 1
    for x in ms: v *= x
    R = sum(1 for x in ms if x % 2 == 0)
    if r != R: notR += 1; print("row", i, "uses r =", r, "but R =", R)
    ok = m * m == k - lam and s * s == k + lam * (v - 1) and 0 < r <= R and hyp17(s, m, r) == closed17(s, m, r) and hyp17(s, m, r)
    key = inst["N" + i]["key"]
    if key != f"SDS({v},{k},{lam},[{','.join(map(str, ms))}])": ok = False; print("key mismatch", i, key)
    if not inst["N" + i]["source"].startswith("Open"): print("row", i, "source", inst["N" + i]["source"])
    if not ok: bad += 1; print("BAD row", i)
    ids.add(i)
print(f"(c) {len(rows)} Lean rows (distinct ids {len(ids)}): bad {bad}; rows with r != R: {notR}")
# open rows that z17 kills at r = R (for the scope of 'best r = R'): count, and are the Lean rows among them?
import math
killed = set()
for row in inst.values():
    if not row["source"].startswith("Open"): continue
    mm = re.match(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", row["key"])
    v, k, lam = int(mm.group(1)), int(mm.group(2)), int(mm.group(3)); ms = [int(x) for x in mm.group(4).split(",")]
    R = sum(1 for x in ms if x % 2 == 0)
    nn = k - lam; s2 = k + lam * (v - 1)
    if R == 0 or nn < 0 or s2 < 0: continue
    m = math.isqrt(nn); s = math.isqrt(s2)
    if m * m != nn or s * s != s2: continue
    if any(hyp17(s, m, r) for r in range(1, R + 1)):
        killed.add(row["id"][1:])
        if not hyp17(s, m, R): print("kill at r < R but not at R:", row["id"])
print(f"open rows z17 kills for some r <= R: {len(killed)}; Lean rows among them: {len(ids & killed)}; "
      f"killed but not a Lean row: {len(killed - ids)}")
