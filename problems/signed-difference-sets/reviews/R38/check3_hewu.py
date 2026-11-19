"""Check 1 (credit) and check 3: GF(25) = F_5[w]/(w^2 - 2), g = 1 + 2w.
(i) He-Wu Thm 5.6's (125,28,3) set in F_25 x F_5: is P + {0} a semiregular RDS rel. {0} x F_5 (shape of Prop. rdscomb(1))?
(ii) P2's (25,12,1) set: D = C0 u C1 u C5 (+1), C3 (-1); SDS? equivalent to O6 under Aut(C5^2) x translations x sign?"""
import itertools
import numpy as np
import sdslib as L

p = 5
def mul(a, b):  # (a0 + a1 w)(b0 + b1 w), w^2 = 2
    return ((a[0] * b[0] + 2 * a[1] * b[1]) % p, (a[0] * b[1] + a[1] * b[0]) % p)
g = (1, 2)
pw = [(1, 0)]
for i in range(1, 24): pw.append(mul(pw[-1], g))
assert len(set(pw)) == 24, "g not primitive"
print("g = 1+2w primitive in F_5[w]/(w^2-2):", len(set(pw)) == 24, "; w^2-2 irreducible:", all((x * x - 2) % 5 for x in range(5)))
log = {x: i for i, x in enumerate(pw)}

# (i) He-Wu: x = g^a in F_25*, y = 2^b in F_5*, rho(x) = i^a, sigma(y) = (-i)^b ; P = {a = 3b mod 4}
ms = (5, 5, 5)
P = []
for a in range(24):
    for b in range(4):
        if a % 4 == (3 * b) % 4:
            x = pw[a]; y = pow(2, b, 5)
            P.append((x[0], x[1], y))
N = [(0, 0, z) for z in range(5)]
D = L.indicator(P, ms) - L.indicator(N, ms) + L.indicator([(0, 0, 0)], ms)  # P - ({0} x F5*)
print("He-Wu D = P - {0}xF5*:", L.sds_params(D), "|P| =", len(P))
R = P + [(0, 0, 0)]
print("  R = P + {0} is a (25,5,25,5) RDS rel {0}xF5:", L.is_rds(R, N, ms, 5))

# (ii) P2's (25,12,1)
cls = lambda i: [pw[(i + 8 * j) % 24] for j in range(3)]
ms2 = (5, 5)
D2 = np.zeros(ms2, dtype=np.int64)
for i in (0, 1, 5):
    for x in cls(i): D2[x] = 1
for x in cls(3): D2[x] = -1
print("P2 (25,12,1) set:", L.sds_params(D2), " +1:", sorted(map(tuple, np.argwhere(D2 == 1).tolist())), " -1:", sorted(map(tuple, np.argwhere(D2 == -1).tolist())))
# other unions of 4 classes with signs: how many SDS (25,12,1)? (context)
cnt = 0; sols = []
for S in itertools.combinations(range(8), 4):
    for sg in itertools.product((1, -1), repeat=4):
        if sg[0] != 1: continue
        E = np.zeros(ms2, dtype=np.int64)
        for i, s in zip(S, sg):
            for x in cls(i): E[x] = s
        if L.sds_params(E) == (25, 12, 1): cnt += 1; sols.append((S, sg))
print("signed unions of 4 eighth-power classes giving (25,12,1) (first sign +):", cnt, sols)

# equivalence with O6: O6(A x + t) = e D2(x) for some A in GL(2,5), t, e = +-1
_, _, O6 = L.load_obj(6)
def apply(A, t, X):
    Y = np.zeros(ms2, dtype=np.int64)
    for (x0, x1) in itertools.product(range(5), repeat=2):
        y = ((A[0][0] * x0 + A[0][1] * x1 + t[0]) % 5, (A[1][0] * x0 + A[1][1] * x1 + t[1]) % 5)
        Y[y] = X[x0, x1]
    return Y
hits = []
for a, b, c, d in itertools.product(range(5), repeat=4):
    if (a * d - b * c) % 5 == 0: continue
    for t in itertools.product(range(5), repeat=2):
        Y = apply(((a, b), (c, d)), t, D2)
        for e in (1, -1):
            if np.array_equal(e * Y, O6): hits.append(((a, b, c, d), t, e))
print("maps (A, t, sign) with O6 = sign * D2 moved by x -> Ax + t:", len(hits), hits[:4])
