"""Line-by-line Python port of the Lean `countsGo` / `magVals` / `anyCountsMag` (MaDividedCounts.lean)."""
import sys
sys.setrecursionlimit(100000)
def tdiv_floor(a, b):  # Lean Int `/` is `Int.div` (T-division)? Lean 4 core: Int `/` is `Int.div` = ediv
    # Lean 4 `HDiv ℤ` is `Int.div` = Euclidean-style `Int.ediv` (rounds toward floor for b > 0)
    return a // b if b > 0 else -(a // -b)
def emod(a, b):
    return a % abs(b) if b != 0 else a
def magOk(m, N, s, Q, A):
    return abs(s) <= A and abs(s) <= Q and Q <= m * A and Q <= m * m * N
def countsGo(xs, N, s, Q, A, ctr):
    ctr[0] += 1
    if not xs:
        return magOk(1, N, s, Q, A) and emod(Q - s, 2) == 0
    x, rest = xs[0], xs[1:]
    if not magOk(abs(x), N, s, Q, A): return False
    top = min(N, max(0, tdiv_floor(Q, x * x)))
    for i in range(top + 1):
        if countsGo(rest, N - i if N - i >= 0 else 0, s - i * x, Q - i * x * x, A - i * abs(x), ctr):
            return True
    return False
def magVals(a):
    out = []
    while a >= 2:
        out += [a, -a]; a -= 1
    return out
def anyCountsMag(c, N, s, Q, A, ctr=None):
    ctr = ctr if ctr is not None else [0]
    return emod(Q - s, 2) == 0 and countsGo(magVals(c), N, s, Q, A, ctr)
