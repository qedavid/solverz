import sys, re
from multisets import multisets, arrangements
rows = [l for l in open(sys.argv[1], encoding="utf-8") if l.startswith("N")]
for l in rows:
    m = re.search(r"(N\d+) SDS\((\d+),(\d+),(-?\d+).*Grp\[(\d+), (\d+)\] c=(\d+) Q=(-?\d+) t=(-?\d+) s'=(-?\d+)", l)
    if not m: continue
    rid, v, k, lam, a, b, c, Q, t, s1 = m.groups()
    size = int(a) * int(b)
    ms = multisets(size, int(c), int(s1), int(Q), int(k) // 4)
    print(rid, size, "multisets", len(ms), "arrangements", sum(arrangements(x) for x in ms))
