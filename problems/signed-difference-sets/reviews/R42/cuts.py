"""indep.py on every open row whose exploration left a quotient cut (2M-node cap): kills the exploration missed."""
import re, sys
from multiprocessing import Pool
from indep import row
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
def work(item):
    rid, key = item
    m = KEY.fullmatch(key)
    return rid, key, row([int(x) for x in m[4].split(",")], int(m[2]), int(m[3]), limit=50000, stop=True)
if __name__ == "__main__":
    items = [(l.split(" ")[0], l.split(" ")[1]) for l in open(sys.argv[1], encoding="utf-8")
             if " open " in l and ":cut" in l]
    if len(sys.argv) > 3: items = [x for x in items if x[0] in set(sys.argv[3].split(","))]
    n = 0
    with Pool(int(sys.argv[2])) as pool:
        for rid, key, res in pool.imap_unordered(work, items, chunksize=4):
            n += 1
            k = [q for q in res if q[3] in ("arith", "profile", "kill", "kneg")]
            if k: print("KILL", rid, key, k[0], flush=True)
    print("done", n, flush=True)
