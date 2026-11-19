"""Validate check5's kill against R18's decide results and its count of 347 (C4 factor, N <= 64, weak)."""
import re, csv, math
import importlib.util, sys, io, contextlib
src = open("check5_z18.py", encoding="utf-8").read().split("rows = list(")[0]
exec(src)
for (N, m, s, want) in [(8, 4, 8, True), (8, 4, 12, False), (16, 4, 12, False), (4, 3, 9, False), (4, 2, 2, False), (1, 3, 5, False)]:
    print(f"GaussKills {N} {m} {s}: mine {all(kill_table(N, m, s).values())}, R18/Lean decide {want}")
rows = list(csv.DictReader(open(PF + "instances.csv", encoding="utf-8")))
cnt = 0; cnt_all = 0
for row in rows:
    if not row["source"].startswith("Open"): continue
    mm = re.match(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", row["key"])
    v, k, lam = int(mm.group(1)), int(mm.group(2)), int(mm.group(3)); ms = [int(x) for x in mm.group(4).split(",")]
    nn, s2 = k - lam, k + lam * (v - 1)
    if nn < 0 or s2 < 0: continue
    m, s = math.isqrt(nn), math.isqrt(s2)
    if m * m != nn or s * s != s2: continue
    x = sum(1 for d in ms if d % 4 == 2); y = sum(1 for d in ms if d % 4 == 0)
    hit = False
    for b in range(1, y + 1):
        for a in range(0, x + y - b + 1):
            N = 2 ** a * 4 ** b
            if N <= 64 and all(kill_table(N, m, s).values()): hit = True
    cnt += hit
print("Open@ rows killed by a quotient with a C4 factor, N <= 64 (R18 F4 says 347):", cnt)
# exists rows: never killed (soundness sanity)
ex = 0
for row in rows:
    if row["status"] != "exists": continue
    mm = re.match(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", row["key"])
    v, k, lam = int(mm.group(1)), int(mm.group(2)), int(mm.group(3)); ms = [int(x) for x in mm.group(4).split(",")]
    nn, s2 = k - lam, k + lam * (v - 1)
    if nn < 0 or s2 < 0: continue
    m, s = math.isqrt(nn), math.isqrt(s2)
    if m * m != nn or s * s != s2: continue
    x = sum(1 for d in ms if d % 4 == 2); y = sum(1 for d in ms if d % 4 == 0)
    for b in range(0, y + 1):
        for a in range(0, x + y - b + 1):
            if a + b and kill_table(2 ** a * 4 ** b, m, s)[2 ** (a + b)]: ex += 1; print("strong kill on exists row!", row["id"], a, b)
print("exists rows strongly killed at some quotient:", ex)
