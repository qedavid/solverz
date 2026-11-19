"""The Lean-port countsGo/anyCountsMag (countsgo.py) against the independent DP (check_rows.min_nonzero):
(a) on the 52 count rows with the certificate's bound amax: port false, node count; (b) on random small instances
with no binding absolute-sum bound (A = c N): port == DP exactly (countsGo is exact once the leaf is closed form)."""
import ast, random
from countsgo import anyCountsMag
from check_rows import min_nonzero
nodes = []
for l in open("check_rows.out"):
    d = ast.literal_eval(l)
    if d["sub"] != "MaCountRows": continue
    ctr = [0]
    r = anyCountsMag(d["c"], d["N"], d["s1"], d["Q"], d["amax"], ctr)
    r2 = anyCountsMag(d["c"], d["N"], d["s1"], d["Q"], d["c"] * d["N"], [0])
    nodes.append((ctr[0], d["name"]))
    assert r is False and r2 is False, d["name"]
print("52 rows: port false with amax and with A = cN; max nodes", max(nodes), "rows with 1 node:", sum(1 for x in nodes if x[0] <= 1))
random.seed(1); mism = 0; tot = 0; feas = 0
for _ in range(4000):
    c = random.randint(1, 6); N = random.randint(1, 14); Q = random.randint(0, 60); s = random.randint(-Q, Q)
    mn = min_nonzero(c, Q, s) if Q > 0 else (0 if s == 0 else None)
    dp = mn is not None and mn <= N
    port = anyCountsMag(c, N, s, Q, c * N)
    tot += 1; feas += dp
    if dp != port: mism += 1; print("MISMATCH", c, N, s, Q, dp, port)
print("random", tot, "feasible", feas, "mismatches", mism)
