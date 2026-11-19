"""Brute-force each MaCombRows certificate: the forms give a well-defined surjective homomorphism
G -> Z_{rp} x K with all fibres of size c, the preimages map to unit vectors, p^i = -1 on K, q^iq = -1 on H
(checked on every element), q prime, q !| |H|, q^(2 jq) | n, p^e | n, bound 2c < p^b Q."""
import itertools, math, re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
txt = (ROOT / "lean/SignedDifferenceSets/MaCombRows.lean").read_text(encoding="utf-8")
body = txt.split("def maCombRows")[1].split("set_option")[0]
pat = re.compile(r"\(⟨(\d+), \[([\d, ]*)\], (\d+), (-?\d+)⟩,\s*⟨(\d+), (\d+), (\d+), (\d+), (\d+), \[([\d, ]*)\], "
                 r"(\[\[.*?\]\]),\s*(\[\[.*?\]\]), (\[.*?\])⟩\)", re.S)
L = lambda s: [int(x) for x in s.replace(" ", "").split(",") if x]
isprime = lambda n: n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))
rows = pat.findall(body)
print("certificates parsed:", len(rows))
for (nid, ms, k, lam, p, r, i, e, b, ks, A, P, qs) in rows:
    ms, ks, A, P, qs = L(ms), L(ks), eval(A), eval(P), eval(qs.replace("(", "[").replace(")", "]"))
    k, lam, p, r, i, e, b = map(int, (k, lam, p, r, i, e, b))
    n, v = k - lam, math.prod(ms)
    ds = [r * p] + ks
    assert len(A) == len(ds)
    # FormOk: d | a_t m_t for each target d, each source factor t
    formok = all(d * 0 == 0 and all((a[t] if t < len(a) else 0) * ms[t] % d == 0 for t in range(len(ms)))
                 for d, a in zip(ds, A))
    img = {}
    for x in itertools.product(*[range(m) for m in ms]):
        y = tuple(sum((a[t] if t < len(a) else 0) * x[t] for t in range(len(ms))) % d for d, a in zip(ds, A))
        img[y] = img.get(y, 0) + 1
    H = math.prod(ds)
    c = v // H
    surj = len(img) == H and set(img.values()) == {c}
    units = all(tuple(sum((a[t] if t < len(a) else 0) * (P[s][t] if t < len(P[s]) else 0) for t in range(len(ms))) % d
                      for d, a in zip(ds, A)) == tuple(1 if u == s else 0 for u in range(len(ds))) for s in range(len(ds)))
    Hel = list(itertools.product(*[range(d) for d in ds]))
    pconj = all(all((pow(p, i) * x[s] + x[s]) % ds[s] == 0 for s in range(1, len(ds))) for x in Hel)
    qok = all(isprime(q) and H % q and iq > 0 and all((q ** iq * x[s] + x[s]) % ds[s] == 0 for x in Hel for s in range(len(ds)))
              and n % q ** (2 * jq) == 0 for q, iq, jq in qs)
    Q = math.prod(q ** jq for q, _, jq in qs)
    nodup = len({q for q, _, _ in qs}) == len(qs)
    vpn = 0
    while n % p ** (vpn + 1) == 0:
        vpn += 1
    ok = (isprime(p) and formok and surj and units and pconj and qok and nodup and n % p ** e == 0 and n != 0
          and 2 * b <= e and 2 * c < p ** b * Q and (r == 1 or r == p ** round(math.log(r, p))))
    print(f"N{nid} G={ms} n={n} v_p(n)={vpn} H={ds} c={c} p^b={p**b} Q={Q} 2c={2*c} p^bQ={p**b*Q} "
          f"formok={formok} surj+fibres={surj} units={units} pconj={pconj} qok={qok} nodup={nodup} ALL={ok}")
