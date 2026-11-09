"""C33's rule against Gordon's own verdicts (source column): Yes/All rows must never be hit; No rows (his exhaustive
orbit searches) that the rule hits are independent confirmations. Also the rows at small v."""
import csv, re, sys
from collections import Counter
sys.path.insert(0, sys.argv[1] + "/scratch/refuter/c33")
from rows_check_lib import hit
ROOT = sys.argv[1]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
c = Counter(); ex = []
for r in csv.DictReader(open(ROOT + "/instances.csv", encoding="utf-8")):
    m = KEY.fullmatch(r["key"]); v, k, lam = int(m[1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(",")]
    h = hit(v, k, lam, ms); g = r["source"].split("@")[0]
    if h:
        c[g] += 1
        if g == "No" and len(ex) < 12: ex.append((r["id"], r["key"], h))
print("rule hits by Gordon source:", dict(c)); print("examples of Gordon-No rows hit:", ex)
