"""CONTROL (b = 0: p || n, so p^2 does not divide n): the same quotients at level 1; p | W is NOT expected.
C39 / C38 on every known set in objects/. For each prime p with b = floor(v_p(n)/2) >= 1, each surjection
G -> Z_{p^j} x K (p-part: every hom image; K: products of cyclic quotients Z_d, each by every hom image, jointly onto),
p self-conjugate mod exp K, and each level l <= min(b, 2), l <= j: W = coset sums on Z_{p^(j-l)} x K must be divisible
by p^l; Z = W/p^l must meet |Z| <= c, sum = +-s/p^l, square sum Q, the count DP and the Lean-port anyCountsMag
(amax = floor(k/p^l)); at l = 1 Z must be constant mod M (C38's modulus). Own code (numpy)."""
import re, sys, glob, os, math, itertools
import numpy as np
from countsgo import anyCountsMag
from check_rows import min_nonzero as _mn, isprime, vp
import functools
@functools.lru_cache(maxsize=None)
def _row(c, Q):
    return {s: _mn(c, Q, s) for s in [0]} if False else None
_memo = {}
def min_nonzero(c, Q, s):
    key = (c, Q, s)
    if key not in _memo: _memo[key] = _mn(c, Q, s)
    return _memo[key]
ROOT = sys.argv[1]
def primes(n):
    return [q for q in range(2, n + 1) if n % q == 0 and isprime(q)]
def selfconj(q, m):
    """smallest i>0 with q^i = -1 mod m (None if none); m = 1, 2: i = 1"""
    if m <= 2: return 1
    if math.gcd(q, m) != 1: return None
    x = q % m
    for i in range(1, 2 * m + 2):
        if (x + 1) % m == 0: return i
        x = x * q % m
    return None
def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]
_acm_memo = {}
def _acm(*a):
    if a not in _acm_memo: _acm_memo[a] = anyCountsMag(*a)
    return _acm_memo[a]
st = dict(objects=0, quots=0, l1=0, l2=0, bad=[], res_quots=0, res_bad=0, byp={})
for f in sorted(glob.glob(os.path.join(ROOT, "objects", "O*.txt")), key=lambda s: int(re.findall(r"O(\d+)", s)[-1])):
    lines = open(f, encoding="utf-8").read().split("\n")
    m = re.fullmatch(r"(\S+) \((\d+),(\d+),(-?\d+)\)", lines[0].strip())
    ms = [int(t[1:]) for t in m[1].split("x")]
    v, k, lam = int(m[2]), int(m[3]), int(m[4])
    D = np.zeros(ms, dtype=np.int64)
    for l in lines[1:]:
        if not l.strip(): continue
        *co, sg = l.split(); D[tuple(int(c) for c in co)] = 1 if sg == "+" else -1
    F = np.fft.fftn(D); ac = np.rint(np.fft.ifftn(F * np.conj(F)).real).astype(np.int64).reshape(-1)
    assert ac[0] == k and (ac[1:] == lam).all() and int((D != 0).sum()) == k, f
    st["objects"] += 1
    s = int(D.sum()); n = k - lam
    if n <= 0: continue
    idx = np.indices(ms).reshape(len(ms), -1); Df = D.reshape(-1)
    for p in primes(n):
        e = vp(n, p); b = e // 2
        if b >= 1 or e == 0: continue
        b = 1  # control: pretend
        J = max(vp(x, p) for x in ms)
        pprime = [x // p ** vp(x, p) for x in ms]
        # cyclic p'-quotients Z_d by hom images (dedupe by image vector)
        Lp = math.lcm(*pprime)
        cyc = {}
        for d in divisors(Lp):
            if d == 1 or selfconj(p, d) is None: continue
            for g in itertools.product(*[[a for a in range(d) if (a * mt) % d == 0] for mt in ms]):
                img = tuple(np.asarray(sum(gt * idx[t] for t, gt in enumerate(g)) % d)[:2048].tolist())
                if math.gcd(*(list(g) + [d])) != 1: continue
                cyc.setdefault((d, img), (d, g))
        cyc = list(cyc.values())
        Ks = [()] + [(x,) for x in cyc] + [(x, y) for x, y in itertools.combinations(cyc, 2)]
        for j in range(1, J + 1):
            N = p ** j
            seen = set()
            for g in itertools.product(*[[a for a in range(N) if (mt * a) % N == 0] for mt in ms]):
                if math.gcd(*(list(g) + [N])) != 1: continue
                a0 = sum(gt * idx[t] for t, gt in enumerate(g)) % N
                for Kc in Ks:
                    ds = [d for d, _ in Kc]
                    Kord = math.prod(ds)
                    if Kord and selfconj(p, math.lcm(1, *ds)) is None: continue
                    kin = np.zeros_like(a0)
                    for d, gk in Kc:
                        kin = kin * d + sum(gt * idx[t] for t, gt in enumerate(gk)) % d
                    # joint surjectivity onto Z_N x K
                    if len(set(zip(a0.tolist(), kin.tolist()))) != N * Kord: continue
                    key = (p, j, tuple(ds), tuple((a0 * Kord + kin)[:4096].tolist()))
                    if key in seen: continue
                    seen.add(key)
                    c = v // (N * Kord)
                    st["quots"] += 1
                    for l in (1,):
                        if l > b or l > j: continue
                        M_ = p ** (j - l)
                        W = np.zeros(M_ * Kord, dtype=np.int64)
                        np.add.at(W, (a0 % M_) * Kord + kin, Df)
                        st["l%d" % l] += 1; st["byp"][(p, l)] = st["byp"].get((p, l), 0) + 1
                        bad = []
                        if M_ * Kord >= 2: st.setdefault("nontriv", {}); st["nontriv"][(p, l)] = st["nontriv"].get((p, l), 0) + 1
                        if (W % p ** l).any(): bad.append("div")
                        else:
                            Z = W // p ** l; Nh = Z.size
                            Q = (k + lam * (p ** l * c - 1))
                            if Q % p ** (2 * l): bad.append("Qint")
                            Q //= p ** (2 * l)
                            if np.abs(Z).max() > c: bad.append("|Z|")
                            if int((Z * Z).sum()) != Q: bad.append("Q")
                            if s % p ** l or abs(int(Z.sum())) != abs(s) // p ** l: bad.append("sum")
                            s1 = abs(s) // p ** l
                            if Q > 3000:
                                st.setdefault("bigQ", []).append((os.path.basename(f), m[1], p, j, l, ds, c, Q, Nh))
                            else:
                                if Nh >= 2: st.setdefault("dp_nontriv", {}); st["dp_nontriv"][(p, l)] = st["dp_nontriv"].get((p, l), 0) + 1
                                mn = min_nonzero(c, Q, s1)
                                if mn is None or mn > Nh: bad.append("DP")
                                amax = k // p ** l
                                if not _acm(c, Nh, s1, Q, amax): bad.append("countsGo")
                            if l == 1:
                                Mres = 1
                                for q in primes(n):
                                    if q == p or Nh % q == 0: continue
                                    jq = vp(n, q) // 2
                                    if jq == 0: continue
                                    if selfconj(q, math.lcm(M_, *([1] + ds))) is None: continue
                                    Mres *= q ** jq
                                if Mres > 1:
                                    st["res_quots"] += 1
                                    if Nh >= 2: st["res_nontriv"] = st.get("res_nontriv", 0) + 1
                                    if ((Z - Z[0]) % Mres).any(): st["res_bad"] += 1; bad.append("res%d" % Mres)
                        if bad: st["bad"].append((os.path.basename(f), m[1], p, j, l, ds, bad))
print({k_: (v_ if k_ not in ("bad", "bigQ") else len(v_)) for k_, v_ in st.items()})
print("bigQ with N >= 2:", sum(1 for x in st.get("bigQ", []) if x[-1] >= 2))
for x in st["bad"][:30]: print("BAD", x)
