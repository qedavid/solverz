"""Rows killed by value counts below a Ma quotient (C34's level 1 and C36's level 2, any p), written as Lean.

`macountrows.py [ids...]`: reads the count kills of `x_ma_iterated` (`scratch/maedge/count_kills.txt`:
`id key v KILL p j l H' count`), rebuilds each certificate (`MaCountCert`: H = ZMod (p^j) × K with K the p'-parts of H',
forms and preimages as `madivided2rows.py`, absolute-sum bound ⌊k/p^l⌋), checks it with a mirror of `MaCountCert.Kills`
(including `anyCountsMag`), and writes `lean/SignedDifferenceSets/MaCountRows/N<id>.lean` and the settle lists
`scratch/maedge/settle-c36b.tsv` (level 2) and `scratch/maedge/settle-c34b.tsv` (level 1). Standard library only; nothing
is written on import.
"""
import math
import re
import sys
from pathlib import Path

from answer import write_module
from macombrows import ma_pairs
from marows import conj_exp, crt, is_prime_td, lst, map_ok, surj_cert, vp

ROOT = Path(__file__).resolve().parent.parent
KILLS = ROOT / "scratch" / "maedge" / "count_kills.txt"
TSV = {1: ROOT / "scratch" / "maedge" / "settle-c34b.tsv", 2: ROOT / "scratch" / "maedge" / "settle-c36b.tsv"}
PREFIX = "SignedDifferenceSets.MaCountRows"
LINE = re.compile(r"(N\d+) SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\) \d+ KILL (\d+) (\d+) (\d+) \[([\d,]+)\] count$")
CLAIM = {1: "C34b (value counts one level below a Ma quotient)", 2: "C36b (value counts two levels below a Ma quotient)"}


def mag_vals(c):
    """Lean's `magVals c`: ±c, …, ±2."""
    out = []
    for a in range(c, 1, -1):
        out += [a, -a]
    return out


def mag_ok(m, N, s, Q, A):
    return abs(s) <= A and abs(s) <= Q and Q <= m * A and Q <= m * m * N


def counts_go(xs, N, s, Q, A):
    """Lean's `countsGo`."""
    if not xs:
        return mag_ok(1, N, s, Q, A) and (Q - s) % 2 == 0
    x, rest = xs[0], xs[1:]
    if not mag_ok(abs(x), N, s, Q, A):
        return False
    return any(counts_go(rest, N - i, s - i * x, Q - i * x * x, A - i * abs(x))
               for i in range(min(N, Q // (x * x)) + 1))


def any_counts_mag(c, N, s, Q, A):
    """Lean's `anyCountsMag`."""
    return (Q - s) % 2 == 0 and counts_go(mag_vals(c), N, s, Q, A)


def cert(ms, k, lam, p, j, l, e):
    """`MaCountCert` fields from the kill's p, j, l and H' = ∏ ZMod eₜ (one factor carries p^(j−l))."""
    v, n = math.prod(ms), k - lam
    d = [x // p ** vp(x, p) for x in e]
    si = max(range(len(e)), key=lambda t: vp(e[t], p))
    if vp(e[si], p) == 0:  # j = l: the factor is the one ZMod (p^j) comes from
        si = next(t for t, m in enumerate(ms) if vp(m, p) >= j and m // p ** vp(m, p) % d[t] == 0)
    pj, r, q = p ** j, p ** (j - l), p ** l
    src = [t for t, x in enumerate(d) if x > 1]
    ks = [d[t] for t in src] or [1]
    srcs = src or [si]
    A = [[0] * si + [1]] + [[0] * t + [1] for t in srcs]
    P = [[0] * si + [crt(1, pj, 0, d[si])]]
    for t, x in zip(srcs, ks):
        P.append([0] * t + [crt(1, x, 0, pj) if t == si else 1 % x])
    ee = vp(n, p)
    c = v // (r * q * math.prod(ks))
    s = math.isqrt(k + lam * (v - 1))
    return dict(p=p, r=r, i=conj_exp(p, math.lcm(*ks)), e=ee, b=ee // 2, l=l, ks=ks, A=A, P=P, amax=k // q,
                Q=(k + lam * (q * c - 1)) // (q * q), s1=s // q, c=c)


def kills(ms, k, lam, x, pairs):
    """Mirror of `MaCountCert.Kills`."""
    p, r, l, ks = x["p"], x["r"], x["l"], x["ks"]
    q = p ** l
    v, h = math.prod(ms), r * q * math.prod(ks)
    if v % h:
        return False
    c = v // h
    return (is_prime_td(p) and r > 0 and x["i"] > 0 and ks != [] and all((p ** x["i"] + 1) % d == 0 for d in ks)
            and map_ok(ms, [r * q] + ks, x["A"]) and surj_cert(ms, [r * q] + ks, x["A"], x["P"])
            and (k - lam) % p ** x["e"] == 0 and 2 * x["b"] <= x["e"] and l in (1, 2) and l <= x["b"]
            and q * q * x["Q"] == k + lam * (q * c - 1) and (q * x["s1"]) ** 2 == k + lam * (v - 1)
            and k < q * (x["amax"] + 1) and (p, r) in pairs and (l != 2 or (p, r * p) in pairs)
            and not any_counts_mag(c, r * math.prod(ks), x["s1"], x["Q"], x["amax"]))


def write_row(rid, ms, k, lam, x):
    v = math.prod(ms)
    group = " × ".join(f"ZMod {m}" for m in ms)
    lam_l = f"({lam})" if lam < 0 else str(lam)
    p, l = x["p"], x["l"]
    q = p ** l
    grp = f"ZMod {x['r']} × Grp {lst(x['ks'])}"
    certt = (f"⟨{p}, {x['r']}, {x['i']}, {x['e']}, {x['b']}, {l}, {lst(x['ks'])},\n"
             f"      {lst([lst(a) for a in x['A']])},\n"
             f"      {lst([lst(a) for a in x['P']])},\n"
             f"      {x['amax']}, {x['Q']}, {x['s1']}⟩")
    doc = (f"Open in Gordon's table (`SDS({v},{k},{lam},{lst(ms).replace(' ', '')})`, 2026-11-05).\n"
           f"{'C34' if l == 1 else 'C36'}'s step (any `p`) on the Ma quotient "
           f"`ZMod {x['r'] * q} × Grp {lst(x['ks'])}`\n"
           f"(`p = {p}`, `b = {x['b']}`, level {l}): the coset sums `W` on `{grp}`\n"
           f"(fibres {q * x['c']}) are divisible by {q}; no counts of the values of `Z = W/{q}` in "
           f"`[−{x['c']}, {x['c']}]`\ngive {x['r'] * math.prod(x['ks'])} values with sum ±{x['s1']}, "
           f"square sum {x['Q']} and absolute sum at most {x['amax']} (`anyCountsMag`).\n"
           f"Generated by `solver/macountrows.py`.")
    write_module(f"N{rid}", ["SignedDifferenceSets.MaDividedCounts"],
                 f"N{rid}: no ({v}, {k}, {lam}) SDS in {group} (value counts)", doc,
                 f"""set_option maxRecDepth 100000 in
/-- N{rid}: no SDS ({v}, {k}, {lam}) in `{group}`. -/
theorem not_hasSDS : ¬ HasSDS ({group}) {k} {lam_l} :=
  MaCountCert.not_hasSDS (w := ⟨{rid}, {lst(ms)}, {k}, {lam_l}⟩)
    (c := {certt}) (by decide +kernel) _""", ns=f"{PREFIX}.N{rid}", prefix=PREFIX)


def main(wanted):
    pairs = ma_pairs()
    rows = []
    for line in KILLS.read_text(encoding="utf-8").splitlines():
        m = LINE.match(line.strip())
        if not m:
            continue
        rid, v, k, lam, ms, p, j, l, e = m.groups()
        if wanted and rid not in wanted:
            continue
        ms, e = [int(t) for t in ms.split(",")], [int(t) for t in e.split(",")]
        x = cert(ms, int(k), int(lam), int(p), int(j), int(l), e)
        assert kills(ms, int(k), int(lam), x, pairs), (rid, x)
        rows.append((rid, ms, int(k), int(lam), x))
    rows.sort(key=lambda t: int(t[0][1:]))
    (ROOT / "lean" / PREFIX.replace(".", "/")).mkdir(parents=True, exist_ok=True)
    for rid, ms, k, lam, x in rows:
        write_row(rid[1:], ms, k, lam, x)
    if not wanted:
        for l, path in TSV.items():
            path.write_text("".join(f"{rid}\tnone\t{CLAIM[l]}; MaCountRows\t{PREFIX}.{rid}.not_hasSDS\n"
                                    for rid, *_, x in rows if x["l"] == l), encoding="utf-8", newline="\n")
    print(len(rows), "rows:", " ".join(r[0] for r in rows))


if __name__ == "__main__":
    main(set(sys.argv[1:]))
