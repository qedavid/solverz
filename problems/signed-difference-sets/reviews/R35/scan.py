"""Independent C29 scan over every row of instances.csv (refuter, written from scratch).

For each row SDS(v,k,lam,[ms]) with n = k - lam: every prime p with b = v_p(n)//2 >= 1, every cyclic p-part
C_{p^j} (j <= max p-exponent of G), every d | exp(p'-part of G) with p self-conjugate mod d (or d = 1), K the
largest subgroup-type of the p'-part with exponent d, c = v/(p^j |K|); Q = prod q^(v_q(n)//2) over primes q | n,
q != p, q not dividing d, q self-conjugate mod lcm(p^j, d). Kill iff 2c < p^b Q. Optionally restricted to (p, p^(j-1))
in maPairs. Prints counts per status and the killed open/exists rows.
"""
import csv, math, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
KEY = re.compile(r"SDS\((-?\d+),(-?\d+),(-?\d+),\[([\d,]*)\]\)")


def factor(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def vp(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def selfconj(q, m):
    """Some i >= 1 with q^i = -1 mod m (m >= 1, gcd(q, m) = 1)."""
    if m <= 2:
        return True
    x = q % m
    for _ in range(m):
        if x == m - 1:
            return True
        if x == 1:
            return False
        x = x * q % m
    return False


def divisors_of(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def pairs():
    txt = (ROOT / "lean/SignedDifferenceSets/MaRows/Polys.lean").read_text(encoding="utf-8")
    body = re.search(r"def maPairs : List \(ℕ × ℕ\) :=\s*\[([^\]]*)\]", txt).group(1)
    return {(int(a), int(b)) for a, b in re.findall(r"\((\d+),\s*(\d+)\)", body)}


def best(ms, k, lam, prs=None, weak=False, noconj=False):
    n = abs(k - lam)
    if n == 0:
        return None
    v = math.prod(ms)
    nf = factor(n)
    prim = {}  # prime -> list of exponents in G
    for m in ms:
        for l, e in factor(m).items():
            prim.setdefault(l, []).append(e)
    out = None
    for p, e in nf.items():
        b = e // 2
        if b == 0 or p not in prim:
            continue
        expo = math.prod(l ** max(es) for l, es in prim.items() if l != p)
        for j in range(1, max(prim[p]) + 1):
            if prs is not None and (p, p ** (j - 1)) not in prs:
                continue
            for d in divisors_of(expo):
                if d > 1 and not selfconj(p, d):
                    continue
                kk = math.prod(l ** sum(min(x, vp(d, l)) for x in es) for l, es in prim.items() if l != p)
                h = p ** j * kk
                c = v // h
                m = math.lcm(p ** j, d)
                qs = [(q, nf[q] // 2) for q in nf if q != p and d % q and nf[q] >= 2 and (noconj or selfconj(q, m))]
                Q = math.prod(q ** jq for q, jq in qs)
                if 2 * c < p ** b * Q or (weak and 2 * c <= p ** b * Q):
                    cand = (p, j, d, kk, c, b, qs, Q, p ** b > 2 * c)
                    if out is None or (out[-1] and not cand[-1]):
                        out = cand
    return out


def main():
    prs = pairs() if "--pairs" in sys.argv else None
    rows = list(csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8")))
    cnt = {}
    for r in rows:
        mt = KEY.fullmatch(r["key"])
        v, k, lam = int(mt[1]), int(mt[2]), int(mt[3])
        ms = [int(x) for x in mt[4].split(",")]
        assert math.prod(ms) == v
        res = best(ms, k, lam, prs)
        if res is None:
            continue
        c21 = res[-1]
        tag = (r["status"], "C21" if c21 else "C29only")
        cnt[tag] = cnt.get(tag, 0) + 1
        if r["status"] != "none" and not c21:
            print(r["id"], r["key"], r["status"], "p,j,d,|K|,c,b,qs,Q =", res[:-1])
        if r["status"] == "exists":
            print("EXISTS HIT", r["id"], r["key"], res)
    print(sorted(cnt.items()))


if __name__ == "__main__":
    main()
