import sys, re
from multisets import multisets
from arrange import search
for l in open(sys.argv[1], encoding="utf-8"):
    m = re.search(r"(N\d+) SDS\((\d+),(\d+),(-?\d+).*Grp\[(\d+), (\d+)\] c=(\d+) Q=(-?\d+) t=(-?\d+) s'=(-?\d+)", l)
    if not m: continue
    rid, v, k, lam, a, b, c, Q, t, s1 = m.groups()
    a, b, c, Q, t, s1, k = int(a), int(b), int(c), int(Q), int(t), int(s1), int(k)
    shape = [x for x in (a, b) if x > 1]
    size = a * b
    MS = multisets(size, c, s1, Q, k // 4)
    why = []
    if (Q - s1) % 2: why.append("Q-s' odd")
    if Q < abs(s1): why.append("Q<|s'|")
    res = [search(shape, x, t) for x in MS]
    verdict = "KILL" if all(r[0] == "none" for r in res) else ("FOUND" if any(r[0] == "found" for r in res) else "CUT")
    print(rid, f"Z{size}", "multisets", len(MS), "arrangements tried", sum(r[2] for r in res), verdict, ",".join(why) or ("" if not MS else "multiset " + str(MS)))
