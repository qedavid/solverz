"""Sensitivity controls for scan.py: broken variants of C29 must hit exists rows."""
import csv, math, sys
sys.path.insert(0, ".")
from scan import KEY, ROOT, best

rows = list(csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8")))
for name, kw in [("as stated", {}), ("<= instead of <", {"weak": True}), ("q not self-conjugate", {"noconj": True})]:
    hits = []
    for r in rows:
        if r["status"] != "exists":
            continue
        mt = KEY.fullmatch(r["key"])
        ms = [int(x) for x in mt[4].split(",")]
        res = best(ms, int(mt[2]), int(mt[3]), None, **kw)
        if res is not None:
            hits.append((r["id"], r["key"], res[:-1]))
    print(name, len(hits), hits[:4])
