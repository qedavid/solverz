"""The 24 extra rows: recheck 'no value multiset' by direct loops over the counts (c = 2) or parity (any c). Own code."""
import re, math
def nomulti_c2(m, s1, Q, Ab):
    for n2 in range(m + 1):
        for nm2 in range(m + 1 - n2):
            for n1 in range(m + 1 - n2 - nm2):
                for nm1 in range(m + 1 - n2 - nm2 - n1):
                    if (2 * (n2 - nm2) + n1 - nm1 in (s1, -s1) and 4 * (n2 + nm2) + n1 + nm1 == Q
                            and 2 * (n2 + nm2) + n1 + nm1 <= Ab):
                        return False
    return True
rows = 0
for l in open("open.log", encoding="utf-8"):
    m = re.match(r"(N\d+) (\S+) (\d+) (\d+) \[([\d, ]*)\] nomultiset$", l.strip())
    if not m: continue
    v, k, lam = map(int, re.match(r"SDS\((\d+),(\d+),(-?\d+)", m[2]).groups())
    p, j = int(m[3]), int(m[4]); H = [int(x) for x in m[5].split(",") if x.strip()]
    size = math.prod(H) if H else 1
    c = v // (p * p * size)
    num = k + lam * (p * p * c - 1); s = math.isqrt(k + lam * (v - 1))
    assert num % p ** 4 == 0 and (lam * c) % (p * p) == 0 and s % (p * p) == 0
    Q, s1 = num // p ** 4, s // (p * p)
    if (Q - s1) % 2: res = "parity"
    elif c == 2: res = "loops:none" if nomulti_c2(size, s1, Q, k // (p * p)) else "loops:FOUND"
    else: res = "unchecked c=%d" % c
    rows += 1
    print(m[1], p, j, H, c, res)
