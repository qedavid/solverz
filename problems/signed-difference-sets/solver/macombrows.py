"""Rows killed by C29 (Ma's lemma with an extra self-conjugate modulus, C21 x C5), written as Lean.

`macombrows.py`: for each open row of instances.csv, looks for a prime p with b = v_p(k - lambda) // 2 >= 1 and a
quotient H = ZMod (p^j) x K of its group as in `marows.py` (p^j dividing one factor, K = prod Z_(d_t) with d_t dividing
the p'-part of factor t, p self-conjugate mod exp K, (p, p^(j-1)) among `MaRows.maPairs`), c = v / |H|, and takes the
primes q != p of k - lambda with j_q = v_q(k - lambda) // 2 >= 1, q not dividing |H| and q self-conjugate mod exp H;
Q = prod q^(j_q). A row is killed when 2c < p^b Q; the certificate minimises ((p - 1) p^(j-1), |K|, number of q).
Writes lean/SignedDifferenceSets/MaCombRows.lean: the rows, one `decide +kernel`, and a theorem per row. Mirrors
`MaCombCert.Kills`. Standard library only; nothing is written on import.
"""
import csv
import itertools
import math
import re
from pathlib import Path

from marows import KEY, OPEN, conj_exp, crt, is_prime_td, lst, map_ok, primes_of, surj_cert, vp

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean" / "SignedDifferenceSets"
OUT = LEAN / "MaCombRows.lean"
POLYS = LEAN / "MaRows" / "Polys.lean"
PAIRS_RE = re.compile(r"def maPairs : List \(ℕ × ℕ\) :=\s*\[([^\]]*)\]")


def ma_pairs():
    """`MaRows.maPairs`, read from Polys.lean."""
    body = PAIRS_RE.search(POLYS.read_text(encoding="utf-8")).group(1)
    return {(int(a), int(b)) for a, b in re.findall(r"\((\d+),\s*(\d+)\)", body)}


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def q_prod(qs):
    return math.prod(q ** jq for q, _, jq in qs)


def valid(ms, k, lam, c, pairs):
    """Mirror of `MaCombCert.Valid`."""
    p, r, i, e, b, ks, A, P, qs = c
    ds, h, v = [r * p] + ks, r * p * math.prod(ks), math.prod(ms)
    q_ok = all(is_prime_td(q) and h % q != 0 and iq > 0 and (q ** iq + 1) % (r * p) == 0
               and all((q ** iq + 1) % d == 0 for d in ks) and (k - lam) % q ** (2 * jq) == 0
               for q, iq, jq in qs)
    return (is_prime_td(p) and r > 0 and i > 0 and ks != [] and all((p ** i + 1) % d == 0 for d in ks)
            and map_ok(ms, ds, A) and surj_cert(ms, ds, A, P) and v % h == 0
            and (k - lam) % p ** e == 0 and k != lam and 2 * b <= e
            and len({q for q, _, _ in qs}) == len(qs) and q_ok and (p, r) in pairs)


def kills(ms, k, lam, c, pairs):
    """Mirror of `MaCombCert.Kills`: `valid` and 2c < p^b Q."""
    p, r, _, _, b, ks, _, _, qs = c
    h = r * p * math.prod(ks)
    return valid(ms, k, lam, c, pairs) and 2 * (math.prod(ms) // h) < p ** b * q_prod(qs)


def cert(ms, k, lam, pairs):
    n, v = k - lam, math.prod(ms)
    if n == 0:
        return None
    best = None
    for p in primes_of(n):
        e = vp(n, p)
        b = e // 2
        if b == 0:
            continue
        odd = [m // p ** vp(m, p) for m in ms]
        for s, m in enumerate(ms):
            for j in range(1, vp(m, p) + 1):
                r, pj = p ** (j - 1), p ** j
                if (p, r) not in pairs:
                    continue
                for dl in itertools.product(*[divisors(o) for o in odd]):
                    i = conj_exp(p, math.lcm(*dl))
                    if i is None:
                        continue
                    src = [t for t, d in enumerate(dl) if d > 1]
                    ks = [dl[t] for t in src] or [1]
                    srcs = src or [s]
                    h, ex = pj * math.prod(ks), math.lcm(pj, *ks)
                    qs = []
                    for q in primes_of(n):
                        jq, iq = vp(n, q) // 2, conj_exp(q, ex)
                        if q != p and h % q and jq and iq is not None:
                            qs.append((q, iq, jq))
                    A = [[0] * s + [1]] + [[0] * t + [1] for t in srcs]
                    P = [[0] * s + [crt(1, pj, 0, dl[s])]]
                    for t, d in zip(srcs, ks):
                        P.append([0] * t + [crt(1, d, 0, pj) if t == s else 1 % d])
                    c = (p, r, i, e, b, ks, A, P, qs)
                    if qs and kills(ms, k, lam, c, pairs):
                        key = ((p - 1) * r, math.prod(ks), len(qs))
                        if best is None or key < best[0]:
                            best = (key, c)
    return best[1] if best else None


def group(ms):
    return " × ".join(f"ZMod {m}" for m in ms)


def entry(rid, ms, k, lam, c):
    p, r, i, e, b, ks, A, P, qs = c
    lam_l = f"({lam})" if lam < 0 else str(lam)
    qs_l = "[" + ", ".join(f"({q}, {iq}, {jq})" for q, iq, jq in qs) + "]"
    return (f"(⟨{rid}, {lst(ms)}, {k}, {lam_l}⟩,\n"
            f"    ⟨{p}, {r}, {i}, {e}, {b}, {lst(ks)}, {lst([lst(a) for a in A])},\n"
            f"      {lst([lst(x) for x in P])}, {qs_l}⟩)")


def row_theorem(rid, ms, k, lam, c, text):
    p, r, i, e, b, ks, A, P, qs = c
    v, h = math.prod(ms), r * p * math.prod(ks)
    qtxt = ", ".join(f"{q}^{jq}" for q, _, jq in qs)
    return f"""/-- N{rid}: `SDS({v}, {k}, {lam})` in `{group(ms)}`; `H = ZMod {r * p} × K`, `|K| = {math.prod(ks)}`,
`c = {v // h}`, `p^b = {p}^{b}`, `Q = {qtxt}`. -/
theorem n{rid}_not_hasSDS : ¬ HasSDS ({group(ms)}) {k} {f"({lam})" if lam < 0 else lam} :=
  not_hasSDS_of_mem_maCombRows (x := {text.replace(chr(10), chr(10) + "  ")}) (by decide +kernel) _
"""


def main():
    pairs = ma_pairs()
    rows = []
    for row in csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8")):
        if row["status"] != OPEN:
            continue
        m = KEY.fullmatch(row["key"])
        v, k, lam = map(int, m.groups()[:3])
        ms = [int(x) for x in m.group(4).split(",")]
        c = cert(ms, k, lam, pairs)
        if c:
            rows.append((int(row["id"][1:]), ms, k, lam, c))
    body = ",\n".join("  " + entry(*x) for x in rows)
    thms = "\n".join(row_theorem(*x, entry(*x)) for x in rows)
    OUT.write_text(f"""module

public import SignedDifferenceSets.MaComb

/-!
# Rows killed by C29 (Ma's lemma with an extra self-conjugate modulus)

{len(rows)} open rows with a quotient `ZMod (r p) × K` and extra primes `q` (C5's modulus
`Q = ∏ q^j`) such that `2c < p^b Q`, checked by `MaCombCert.Kills` in one `decide +kernel`;
generated by `solver/macombrows.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.MaCombRows

/-- Rows and certificates. -/
def maCombRows : List (Row × MaCombCert) := [
{body}]

set_option maxRecDepth 100000 in
theorem maCombRows_kills : ∀ x ∈ maCombRows, x.2.Kills x.1 := by decide +kernel

/-- No row of `maCombRows` has an SDS. -/
theorem not_hasSDS_of_mem_maCombRows {{x : Row × MaCombCert}} (hx : x ∈ maCombRows)
    (inst : Fintype (Grp x.1.ms)) : ¬ @HasSDS (Grp x.1.ms) _ inst x.1.k x.1.lam :=
  MaCombCert.not_hasSDS (maCombRows_kills x hx) inst

{thms}
end SignedDifferenceSets.MaCombRows
""", encoding="utf-8", newline="\n")
    print(len(rows), "rows:", " ".join(f"N{x[0]}" for x in rows))


if __name__ == "__main__":
    main()
