"""Each `n<id>_not_hasSDS` in MaEdgeRows.lean: its stated type (group, k, lam) and its certificate's Row must both be
the table row N<id> (open), and each list entry must have exactly one theorem."""
import csv, re, sys
ROOT = sys.argv[1]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
tab = {r["id"]: r for r in csv.DictReader(open(ROOT + "/instances.csv", encoding="utf-8"))}
src = open(ROOT + "/lean/SignedDifferenceSets/MaEdgeRows.lean", encoding="utf-8").read()
listpart, thmpart = src.split("theorem maEdgeRows_kills")
entries = re.findall(r"\(⟨(\d+), \[([\d, ]+)\], (\d+), \(?(-?\d+)\)?⟩", listpart)
thms = re.findall(r"theorem n(\d+)_not_hasSDS : ¬ HasSDS \(([^)]*)\) (\d+) \(?(-?\d+)\)?\s*:=\s*\n\s*not_hasSDS_of_mem_maEdgeRows \(x := \(⟨(\d+), \[([\d, ]+)\], (\d+), \(?(-?\d+)\)?⟩", thmpart)
print("list entries:", len(entries), " theorems:", len(thms), " distinct ids:", len({e[0] for e in entries}))
errs = 0
lst = {e[0]: e for e in entries}
for tid, grp, k, lam, rid, ms, k2, lam2 in thms:
    r = tab["N" + tid]; m = KEY.fullmatch(r["key"])
    msl = [int(x) for x in ms.split(",")]
    want_grp = " × ".join(f"ZMod {x}" for x in msl)
    ok = (tid == rid and grp == want_grp and k == k2 == m[2] and int(lam) == int(lam2) == int(m[3])
          and msl == [int(x) for x in m[4].split(",")] and r["status"] == "open" and tid in lst
          and lst[tid][1:] == (ms, k2, lam2))
    if not ok: errs += 1; print("MISMATCH", tid, grp, k, lam, r["key"], r["status"])
print("mismatches:", errs, " list ids without theorem:", sorted(set(lst) - {t[0] for t in thms}))
