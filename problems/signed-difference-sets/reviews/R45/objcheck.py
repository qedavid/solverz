"""Refuter (C40): a known Z_p^2 SDS (objects/O*.txt) passes every step of the tomography argument:
SDS check, sign to sum +s, centring, line identity, each centred line contraction meets the demands with
first moment 0 (so lies in W), and (p <= 7) the search over W reaches this very D."""
import sys, importlib.util
spec = importlib.util.spec_from_file_location('indep_mod', 'indep_lib.py'); 
from indep_lib import demands_ok, enum_V, m1, search, functionals
path = sys.argv[1]
lines = open(path).read().split('\n')
p = int(lines[0].split('x')[0][1:].replace('C', ''))
k, lam = [int(t) for t in lines[0].split('(')[1].rstrip(')').split(',')[1:3]]
D = {}
for ln in lines[1:]:
    if ln.strip():
        a, b, sg = ln.split(); D[(int(a), int(b))] = 1 if sg == '+' else -1
pts = [(a, b) for a in range(p) for b in range(p)]
Dv = {x: D.get(x, 0) for x in pts}
add = lambda x, y: ((x[0] + y[0]) % p, (x[1] + y[1]) % p)
assert sum(1 for x in pts if Dv[x]) == k
assert all(sum(Dv[x] * Dv[add(x, g)] for x in pts) == lam for g in pts if g != (0, 0)), "not an SDS"
s = sum(Dv.values())
if s < 0: Dv = {x: -v for x, v in Dv.items()}; s = -s
inv = pow(s, -1, p)
c = (sum(Dv[x] * x[0] for x in pts) * inv % p, sum(Dv[x] * x[1] for x in pts) * inv % p)
Dc = {x: Dv[add(x, c)] for x in pts}
F = functionals(p)
Y = [tuple(sum(Dc[x] for x in pts if (u * x[0] + w * x[1]) % p == t) for t in range(p)) for (u, w) in F]
ident = all(sum(Y[j][(u * g[0] + w * g[1]) % p] for j, (u, w) in enumerate(F)) == p * Dc[g] + s for g in pts)
dem = all(demands_ok(list(y), p, k, lam, s) for y in Y)
mom = all(m1(y, p) == 0 for y in Y)
print(f"{path}: p={p} k={k} lam={lam} s={s} SDS ok, identity {ident}, demands {dem}, first moments 0 {mom}")
if p <= 7:
    V = enum_V(p, k, lam, s); W = [y for y in V if m1(y, p) == 0]
    print("contractions in W:", all(y in W for y in Y))
    import numpy as np
    n_int, n_sds, ex, pts2 = search(p, s, W)
    # is this D among the search's SDS leaves? rebuild from the choice of W indices
    choice = [W.index(y) for y in Y]
    tot = [sum(W[choice[j]][(u * a + w * b) % p] for j, (u, w) in enumerate(F)) for (a, b) in pts2]
    print("its choice is integral and gives D back:", [(t - s) // p for t in tot] == [Dc[x] for x in pts2], f"(search: {n_int} integral, {n_sds} SDS)")
