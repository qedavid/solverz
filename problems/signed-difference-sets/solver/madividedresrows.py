"""Rows killed by C38 (the divided search below a Ma quotient with Turyn's residue class), written as Lean.

`madividedresrows.py [ids...]`: reads the kills of `x_ma_c5` (`scratch/x_ma_c5.out`: `id key v KILL p j l H' nodes`) that
`x_ma_iterated` (`scratch/x_ma_iterated.out`) does not reach, all at level 1; rebuilds each certificate (`MaDivResCert`:
H = ZMod (p^j) × K as `macountrows.py`, bounds covering the absolute sum as C36's, the primes q ≠ p of k − λ with
q^(2 j_q) ∣ k − λ, q ∤ |H| and q^(i_q) ≡ −1 mod exp H'), checks it with mirrors of `MaDivResCert.Valid` and of
`noVectorRes` (every bound must leave no vector), and writes `lean/SignedDifferenceSets/MaDividedResRows/N<id>.lean` and
`scratch/maedge/settle-c38.tsv`. Standard library only; nothing is written on import.
"""
import math
import re
import sys
from pathlib import Path

from answer import write_module
from macombrows import ma_pairs
from macountrows import cert as count_cert
from marows import conj_exp, is_prime_td, lst, map_ok, primes_of, surj_cert, vp

ROOT = Path(__file__).resolve().parent.parent
KILLS = ROOT / "scratch" / "x_ma_c5.out"
ITER = ROOT / "scratch" / "x_ma_iterated.out"
TSV = ROOT / "scratch" / "maedge" / "settle-c38.tsv"
PREFIX = "SignedDifferenceSets.MaDividedResRows"
LINE = re.compile(r"(N\d+) SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\) \d+ KILL (\d+) (\d+) 1 \[([\d,]+)\] (\d+)$")


def cert(ms, k, lam, p, j, e):
    x = count_cert(ms, k, lam, p, j, 1, e)
    n, r, ks, c = k - lam, x["r"], x["ks"], x["c"]
    k0 = k // p
    bounds = [k0, k0 - 1] if p == 2 else [k0 if (k0 - k) % 2 == 0 else k0 - 1]
    qs = []
    for q in primes_of(n):
        jq = vp(n, q) // 2
        if q == p or jq == 0 or (r * p * math.prod(ks)) % q == 0:
            continue
        iq = conj_exp(q, math.lcm(r, *ks))
        if iq is not None:
            qs.append((q, iq, jq))
    return dict(x, bounds=[b for b in bounds if b >= 0], t=lam * c // p, qs=qs,
                M=math.prod(q ** jq for q, _, jq in qs))


def valid(ms, k, lam, x, pairs):
    """Mirror of `MaDivResCert.Valid`."""
    p, r, ks = x["p"], x["r"], x["ks"]
    v, h = math.prod(ms), r * p * math.prod(ks)
    if v % h:
        return False
    c = v // h
    cover = all(any(a <= kk and (kk - a) % 2 == 0 for kk in x["bounds"])
                for a in range(k + 1) if p * a <= k and (k - p * a) % 2 == 0)
    qs_ok = len({q for q, _, _ in x["qs"]}) == len(x["qs"]) and all(
        is_prime_td(q) and h % q != 0 and iq > 0 and (q ** iq + 1) % r == 0 and all((q ** iq + 1) % d == 0 for d in ks)
        and (k - lam) % q ** (2 * jq) == 0 for q, iq, jq in x["qs"])
    return (is_prime_td(p) and r > 0 and x["i"] > 0 and ks != [] and all((p ** x["i"] + 1) % d == 0 for d in ks)
            and map_ok(ms, [r * p] + ks, x["A"]) and surj_cert(ms, [r * p] + ks, x["A"], x["P"])
            and (k - lam) % p ** x["e"] == 0 and 2 * x["b"] <= x["e"] and x["b"] > 0
            and p * p * x["Q"] == k + lam * (p * c - 1) and p * x["t"] == lam * c
            and (p * x["s1"]) ** 2 == k + lam * (v - 1) and cover and qs_ok and (p, r) in pairs)


def add_table(fs):
    """Addition on the element numbers of `Grp fs` (Lean's `Indexed`: mixed radix, first factor most significant)."""
    n = math.prod(fs)

    def dec(a):
        out = []
        for f in reversed(fs):
            out.append(a % f)
            a //= f
        return out[::-1]

    def enc(xs):
        a = 0
        for y, f in zip(xs, fs):
            a = a * f + y
        return a
    return [[enc([(y + z) % f for y, z, f in zip(dec(a), dec(b), fs)]) for b in range(n)] for a in range(n)]


def no_vector_res(n, add, c, Q, t, k, s, M):
    """Mirror of Lean's `noVectorRes` (`true`: no vector); also the node count."""
    nodes = [0]

    def cut(rem, sm, sq):
        return Q - sq < 0 or rem * (Q - sq) < (s - sm) ** 2 or rem * c < abs(s - sm)

    def go(top, x0, rem, pre, sm, sq, ab):
        nodes[0] += 1
        if rem == 0:
            ok = (sm == s and sq == Q and ab <= k and (k - ab) % 2 == 0
                  and all(sum(pre[y] * pre[add[y][g]] for y in range(n)) == t for g in range(1, n)))
            return not ok
        if cut(rem, sm, sq):
            return True
        return all(Q - sq < y * y or (y - x0) % M != 0 or go(top, x0, rem - 1, pre + [y], sm + y, sq + y * y, ab + abs(y))
                   for y in range(-top, top + 1))

    if cut(n, 0, 0):
        return True, 1
    ok = all(Q < y * y or go(abs(y), y, n - 1, [y], y, y * y, abs(y)) for y in range(-c, c + 1))
    return ok, nodes[0]


def write_row(rid, ms, k, lam, x):
    v = math.prod(ms)
    group = " × ".join(f"ZMod {m}" for m in ms)
    lam_l = f"({lam})" if lam < 0 else str(lam)
    qf = [x["r"]] + x["ks"]
    grp = f"Grp {lst(qf)}"
    qs = "[" + ", ".join(f"({q}, {iq}, {jq})" for q, iq, jq in x["qs"]) + "]"
    certt = (f"⟨{x['p']}, {x['r']}, {x['i']}, {x['e']}, {x['b']}, {lst(x['ks'])},\n"
             f"      {lst([lst(a) for a in x['A']])},\n"
             f"      {lst([lst(a) for a in x['P']])},\n"
             f"      {lst(x['bounds'])}, {x['Q']}, {x['t']}, {x['s1']}, {qs}⟩")
    if len(x["bounds"]) == 2:
        search = """      rcases hk' with rfl | rfl
      · decide +kernel
      · decide +kernel"""
    else:
        search = """      subst hk'
      decide +kernel"""
    doc = (f"Open in Gordon's table (`SDS({v},{k},{lam},{lst(ms).replace(' ', '')})`, 2026-11-05).\n"
           f"C38 on the Ma quotient `ZMod {x['r'] * x['p']} × Grp {lst(x['ks'])}` (`p = {x['p']}`, `b = {x['b']}`): "
           f"the coset sums\n`W` on `{grp}` (fibres {x['p'] * x['c']}) are divisible by {x['p']}, and "
           f"`Z = W/{x['p']}` is constant mod {x['M']}\n(C5 at `(q, i, j)` = {qs}); "
           f"`noVectorRes` finds no such `Z` with `|Z| ≤ {x['c']}`,\nsquare sum {x['Q']}, "
           f"autocorrelation {x['t']}, sum ±{x['s1']} and absolute sum at most a bound in {lst(x['bounds'])}.\n"
           f"Generated by `solver/madividedresrows.py`.")
    write_module(f"N{rid}", ["SignedDifferenceSets.MaDividedRes"],
                 f"N{rid}: no ({v}, {k}, {lam}) SDS in {group} (C38)", doc,
                 f"""/-- The factors of the divided quotient `{grp}` are positive. -/
theorem hpos : ∀ m ∈ {lst(qf)}, 0 < m := by decide

set_option maxRecDepth 100000 in
/-- N{rid}: no SDS ({v}, {k}, {lam}) in `{group}`. -/
theorem not_hasSDS : ¬ HasSDS ({group}) {k} {lam_l} :=
  MaDivResCert.not_hasSDS (w := ⟨{rid}, {lst(ms)}, {k}, {lam_l}⟩)
    (c := {certt}) (by decide +kernel) hpos _
    (fun k' hk' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
{search})""", ns=f"{PREFIX}.N{rid}", prefix=PREFIX)


def main(wanted):
    pairs = ma_pairs()
    iterated = {line.split()[0] for line in ITER.read_text(encoding="utf-8").splitlines() if " KILL " in line}
    rows = []
    for line in KILLS.read_text(encoding="utf-8").splitlines():
        m = LINE.match(line.strip())
        if not m or m.group(1) in iterated or (wanted and m.group(1) not in wanted):
            continue
        rid, v, k, lam, ms, p, j, e, _ = m.groups()
        ms, e, k, lam, p, j = [int(t) for t in ms.split(",")], [int(t) for t in e.split(",")], int(k), int(lam), int(p), int(j)
        x = cert(ms, k, lam, p, j, e)
        assert valid(ms, k, lam, x, pairs), (rid, x)
        fs = [x["r"]] + x["ks"]
        add = add_table(fs)
        nodes = []
        for kk in x["bounds"]:
            ok, nd = no_vector_res(math.prod(fs), add, x["c"], x["Q"], x["t"], kk, x["s1"], x["M"])
            assert ok, (rid, kk)
            nodes.append(nd)
        rows.append((rid, ms, k, lam, x))
        print(rid, "p", p, "M", x["M"], "qs", x["qs"], "bounds", x["bounds"], "nodes", nodes)
    rows.sort(key=lambda t: int(t[0][1:]))
    (ROOT / "lean" / PREFIX.replace(".", "/")).mkdir(parents=True, exist_ok=True)
    for rid, ms, k, lam, x in rows:
        write_row(rid[1:], ms, k, lam, x)
    if not wanted:
        TSV.write_text("".join(f"{rid}\tnone\tC38 (divided search with Turyn's residue class); MaDividedResRows\t"
                               f"{PREFIX}.{rid}.not_hasSDS\n" for rid, *_ in rows), encoding="utf-8", newline="\n")
    print(len(rows), "rows:", " ".join(r[0] for r in rows))


if __name__ == "__main__":
    main(set(sys.argv[1:]))
