"""Value profiles (multisets) a divided vector Z could have: counts n_a (|a| <= c) with sum n_a = N, sum a n_a = s'
(sign fixed by negation symmetry), sum a^2 n_a = Q, A = sum |a| n_a <= k', k' - A even. Own code."""
import math
def profiles(N, c, Q, s, kp):
    vals = [x for a in range(c, 0, -1) for x in (a, -a)] + [0]
    out = []
    def rec(i, rem, sm, sq, ab, cur):
        if sq > Q or ab > kp: return
        a = vals[i]
        if a == 0:
            if sm == s and sq == Q and (kp - ab) % 2 == 0: out.append({**cur, 0: rem} if rem else dict(cur))
            return
        R, D = Q - sq, s - sm
        if R > rem * a * a or abs(D) > R or abs(D) > rem * abs(a) or ab + abs(D) > kp: return
        hi = min(rem, R // (a * a), (kp - ab) // abs(a))
        for m in range(hi + 1):
            if m: cur[a] = m
            rec(i + 1, rem - m, sm + a * m, sq + a * a * m, ab + abs(a) * m, cur)
            cur.pop(a, None)
    rec(0, N, 0, 0, 0, {})
    return out
def arrangements(N, prof):
    r = math.factorial(N)
    for m in prof.values(): r //= math.factorial(m)
    return r
if __name__ == "__main__":
    import sys
    N, c, Q, s, kp = map(int, sys.argv[1:6])
    ps = profiles(N, c, Q, s, kp)
    print(len(ps), "profiles; arrangements", sum(arrangements(N, p) for p in ps))
    for p in ps[:6]: print(p, arrangements(N, p))
