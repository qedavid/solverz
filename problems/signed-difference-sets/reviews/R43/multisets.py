"""Value multisets for a divided search: m entries in [-c, c], sum s1, square sum Q, absolute sum A <= Abound
(parity: if par is not None, A ≡ par mod 2). Own code."""
import math
def multisets(m, c, s1, Q, Abound, par=None):
    out = []
    vals = list(range(c, -c - 1, -1))
    def rec(idx, left, sm, sq, ab, cnt):
        if idx == len(vals):
            if left == 0 and sm == s1 and sq == Q and ab <= Abound and (par is None or (ab - par) % 2 == 0):
                out.append(dict(cnt))
            return
        a = vals[idx]
        rest = vals[idx + 1:]
        for n in range(left, -1, -1):
            sm2, sq2, ab2 = sm + a * n, sq + a * a * n, ab + abs(a) * n
            l2 = left - n
            if sq2 > Q or ab2 > Abound: continue
            # remaining values are all < a: sum bounds
            if l2:
                mx = rest[0] if rest else None
                if mx is None: continue
                hi, lo = sm2 + l2 * mx, sm2 + l2 * (-c)
                if not (lo <= s1 <= hi): continue
                rs, rq = s1 - sm2, Q - sq2
                if rs * rs > l2 * rq: continue
            elif sm2 != s1 or sq2 != Q:
                continue
            if n: cnt[a] = n
            rec(idx + 1, l2, sm2, sq2, ab2, cnt)
            if n: del cnt[a]
    rec(0, m, 0, 0, 0, {})
    return out
def arrangements(ms, fix_first=True):
    m = sum(ms.values())
    tot = math.factorial(m)
    for n in ms.values(): tot //= math.factorial(n)
    if fix_first:  # fix one value (the largest count's value? we fix the max value) at position 0
        a = max(ms); n = ms[a]
        tot = tot * n // m
    return tot
