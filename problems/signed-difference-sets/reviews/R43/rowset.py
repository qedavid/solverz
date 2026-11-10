"""The 49 rows: level-2 kills of x_ma_iterated vs settle list, instances.csv, single-level kills. Own code."""
import csv, re, sys, math
ROOT = sys.argv[1]
inst = {r["id"]: r for r in csv.DictReader(open(f"{ROOT}/instances.csv", encoding="utf-8"))}
it = {}
for l in open(f"{ROOT}/scratch/x_ma_iterated.out", encoding="utf-8"):
    w = l.split()
    it[w[0]] = l.strip()
one = {}
for l in open(f"{ROOT}/scratch/x_ma_divided.out", encoding="utf-8"):
    w = l.split()
    one[w[0]] = l.strip()
settle = [l.split("\t")[0] for l in open(f"{ROOT}/scratch/maedge/settle-c36.tsv", encoding="utf-8") if l.strip()]
lv2 = {i: l for i, l in it.items() if re.search(r" KILL \d+ \d+ 2 ", l)}
print("level-2 kills:", len(lv2))
for i, l in sorted(lv2.items(), key=lambda x: int(x[0][1:])):
    st = inst[i]["status"]; o = one.get(i, "-")
    ok = " KILL " in o
    print(i, st, "single-level-kill" if ok else "single:" + o.split(" ", 4)[-1][:60], "| in settle" if i in settle else "| NOT in settle")
print("settle not lv2:", [i for i in settle if i not in lv2])
print("settle status:", {inst[i]["status"] for i in settle}, "sources:", {inst[i]["source"] for i in settle})
# all kills in iterated vs open/status
from collections import Counter
print(Counter(re.search(r"KILL (\d+) \d+ (\d+)", l).groups() for l in it.values() if " KILL " in l))
# rows the iterated run lists, by status at the time of the run
print("iterated rows:", len(it), Counter(inst[i]["status"] for i in it))
