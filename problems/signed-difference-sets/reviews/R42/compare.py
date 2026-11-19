"""Compare x_ma_divided (scratch/x_ma_divided.out) with indep.py: (1) every KILL line; (2) a random sample of open rows
(each odd-p quotient the exploration marks found must not be killed here); (3) every exists row (no quotient killed).
Usage: compare.py <problem dir> <open sample size> <procs>"""
import csv, math, random, re, sys
from multiprocessing import Pool
from indep import row
ROOT = sys.argv[1]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
def parse(key):
    m = KEY.fullmatch(key); return [int(x) for x in m[4].split(",")], int(m[2]), int(m[3])
def work(item):
    tag, rid, key, extra = item
    ms, k, lam = parse(key)
    return tag, rid, key, extra, row(ms, k, lam, limit=200000, stop=(tag == "kill"))
if __name__ == "__main__":
    items = []
    lines = open(f"{ROOT}/scratch/x_ma_divided.out", encoding="utf-8").read().splitlines()
    opens = []
    for l in lines:
        parts = l.split(" ")
        rid, key = parts[0], parts[1]
        if parts[3] == "KILL": items.append(("kill", rid, key, parts[4:]))
        elif parts[3] == "open": opens.append((rid, key, parts[4:]))
    random.seed(34)
    for rid, key, notes in random.sample(opens, int(sys.argv[2])): items.append(("open", rid, key, notes))
    for r in csv.DictReader(open(f"{ROOT}/instances.csv", encoding="utf-8")):
        if r["status"] == "exists": items.append(("exists", r["id"], r["key"], []))
    bad, stats = [], {}
    with Pool(int(sys.argv[3])) as pool:
        for tag, rid, key, extra, res in pool.imap_unordered(work, items):
            killed = [q for q in res if q[3] in ("arith", "profile", "kill", "kneg")]
            st = stats.setdefault(tag, {"rows": 0, "killed": 0, "big": 0, "agree": 0})
            st["rows"] += 1; st["killed"] += bool(killed); st["big"] += any(q[3] == "big" for q in res)
            if tag == "kill":
                p, j, e = int(extra[0]), int(extra[1]), [int(x) for x in extra[2].strip("[]").split(",")]
                if p == 2: print("p=2 kill (outside C34):", rid, key, extra, "indep:", res[-1] if res else None); continue
                ok = bool(killed) and (killed[0][0], killed[0][1], killed[0][2]) == (p, j, e)
                st["agree"] += ok
                if not ok: bad.append((tag, rid, key, extra, res))
                if extra[3] != "arith": print("node-kill", rid, key, "x:", extra, "indep:", killed[0][3:] if killed else res)
            elif tag == "open":
                found = {(int(n.split(":")[0]), n.split(":")[1]) for n in extra if n.endswith(":found")}
                cut = {(int(n.split(":")[0]), n.split(":")[1]) for n in extra if n.endswith(":cut")}
                for q in res:
                    name = "[" + ",".join(map(str, q[2])) + "]"
                    if (q[0], name) in found and q[3] in ("arith", "profile", "kill", "kneg"): bad.append((tag, rid, key, q))
                    if (q[0], name) in cut and q[3] in ("arith", "profile", "kill", "kneg"): print("missed by cap:", rid, key, q)
                    if (q[0], name) not in found | cut: bad.append(("open-unlisted", rid, key, q))
                st["agree"] += not killed
            else:
                if killed: bad.append((tag, rid, key, killed))
                else: st["agree"] += 1
    print(stats)
    print("disagreements:", len(bad))
    for b in bad[:30]: print(b)
