"""Check each row's final theorem against instances.csv: group factors, k, lam, and the ms in the proof."""
import csv, re, sys, glob, os
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../.."))
inst = {r["id"]: r for r in csv.DictReader(open(os.path.join(ROOT, "instances.csv"), encoding="utf-8"))}
files = sys.argv[1:]
bad = 0
for f in files:
    t = open(f, encoding="utf-8").read()
    rid = os.path.basename(f)[:-5]
    m = re.search(r"theorem not_hasSDS : ¬ HasSDS \(([^)]*)\) (-?\d+) (-?\d+) :=", t)
    if not m:
        print(rid, "NO STATEMENT"); bad += 1; continue
    grp = [int(x) for x in re.findall(r"ZMod (\d+)", m[1])]
    if m[1].replace(" ", "") != "×".join(f"ZMod{x}" for x in grp):
        print(rid, "odd group text", m[1]); bad += 1
    k, lam = int(m[2]), int(m[3])
    ms = [int(x) for x in re.search(r"\(ms := \[([\d, ]+)\]\)", t)[1].split(",")]
    key = inst[rid]["key"]
    mk = re.match(r"SDS\((\d+),(-?\d+),(-?\d+),\[([\d,]+)\]\)", key)
    v0, k0, l0 = int(mk[1]), int(mk[2]), int(mk[3]); ms0 = [int(x) for x in mk[4].split(",")]
    ok = grp == ms0 and ms == ms0 and k == k0 and lam == l0
    prod = 1
    for x in grp: prod *= x
    ok = ok and prod == v0
    # count theorems named not_hasSDS and any sorry/native_decide/axiom
    extra = [w for w in ("sorry", "native_decide", "axiom ", "admit", "implemented_by", "extern") if w in t]
    print(rid, key, inst[rid]["status"], "OK" if ok and not extra else "MISMATCH", extra)
    bad += (not ok) or bool(extra)
print("bad", bad, "of", len(files))
