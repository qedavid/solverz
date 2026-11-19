"""The 27 rows: KILL lines at odd p, minus C33's settle list; arith kills outside C33; row files vs instances.csv."""
import csv, re, glob, os, sys
R = sys.argv[1]
c33 = {l.split("\t")[0] for l in open(f"{R}/scratch/maedge/settle.tsv", encoding="utf-8") if l.strip()}
kills = [l.split(" ") for l in open(f"{R}/scratch/x_ma_divided.out", encoding="utf-8").read().splitlines() if " KILL " in l]
odd = [k for k in kills if k[4] != "2"]
arith_out = [k[0] for k in kills if k[-1] == "arith" and k[0] not in c33]
new = sorted(k[0] for k in odd if k[0] not in c33)
print("kills", len(kills), "odd", len(odd), "in C33", sum(k[0] in c33 for k in kills), "arith outside C33:", arith_out)
print("odd kills outside C33:", len(new), new)
inst = {r["id"]: r for r in csv.DictReader(open(f"{R}/instances.csv", encoding="utf-8"))}
rows = sorted(os.path.basename(f)[:-5] for f in glob.glob(f"{R}/lean/SignedDifferenceSets/MaDividedRows/N*.lean"))
print("row files:", len(rows), "missing vs new:", sorted(set(new) - set(rows)), "extra:", sorted(set(rows) - set(new)))
TH = re.compile(r"theorem not_hasSDS : ¬ HasSDS \((.*?)\) (\d+) \(?(-?\d+)\)? :=\s*MaDivCert\.not_hasSDS \(w := ⟨(\d+), \[([\d, ]+)\], (\d+), \(?(-?\d+)\)?⟩\)", re.S)
bad = 0
for rid in rows:
    s = open(f"{R}/lean/SignedDifferenceSets/MaDividedRows/{rid}.lean", encoding="utf-8").read()
    m = TH.search(s)
    grp, k, lam, wid, wms, wk, wlam = m.groups()
    ms = [int(x) for x in wms.split(",")]
    g2 = [int(x) for x in re.findall(r"ZMod (\d+)", grp)]
    key = inst[rid]["key"]
    km = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", key)
    ims = [int(x) for x in km[4].split(",")]
    ok = (g2 == ms == ims and int(k) == int(wk) == int(km[2]) and int(lam) == int(wlam) == int(km[3]) and "N" + wid == rid
          and inst[rid]["status"] == "open" and grp.count("×") == len(ms) - 1)
    bad += not ok
    print(rid, key, inst[rid]["status"], "stmt", grp, k, lam, "OK" if ok else "MISMATCH")
print("mismatches:", bad)
