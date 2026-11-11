"""Rows killed by Klein tomography on a quotient ZMod 2 x ZMod 2 x ZMod 3 (I23), written as Lean.

`kleinrows.py [ids...]`: reads the `flatk p=2` kills of `scratch/tomo3/killed_all.txt` (all of them, or the ids
given), builds for each row the forms onto `Grp [2, 2, 3]` and the preimages of the unit vectors (`KleinCert`), and for
each parameter set (v, k, lambda) the data of `KleinKills` (s, t, the bounds, the residues mod 4 of the twisted sums),
rechecked by a mirror of `kleinKill`. Writes, under lean/SignedDifferenceSets/KleinTomographyRows:
- Params.lean: `kills_<v>_<k>_<lambda>` for each parameter set;
- N<id>.lean: the row's `not_hasSDS`.
`kleinrows.py --tests` prints the control data for Tests/KleinTomography.lean instead. Standard library only.
"""
import csv
import math
import re
import sys
from pathlib import Path

from marows import crt, map_ok, surj_cert

ROOT = Path(__file__).resolve().parent.parent
KILLS = ROOT / "scratch" / "tomo3" / "killed_all.txt"
OUT_DIR = ROOT / "lean" / "SignedDifferenceSets" / "KleinTomographyRows"
PREFIX = "SignedDifferenceSets.KleinTomographyRows"
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
DS = [2, 2, 3]


def lst(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


def load_rows():
    with open(ROOT / "instances.csv", newline="", encoding="utf-8") as f:
        return {r["id"]: r for r in csv.DictReader(f)}


def parse_key(key):
    v, k, lam, ms = KEY.match(key).groups()
    return int(v), int(k), int(lam), [int(m) for m in ms.split(",")]


def quotient(ms):
    """Forms onto ZMod 2 x ZMod 2 x ZMod 3: the first two even factors, then a factor divisible by 3."""
    even = [i for i, m in enumerate(ms) if m % 2 == 0]
    three = [i for i, m in enumerate(ms) if m % 3 == 0]
    assert len(even) >= 2 and three, ms
    srcs = [even[0], even[1], three[0]]
    A = [[0] * s + [1] for s in srcs]
    # preimage of unit vector t: x[s_u] = [u = t] mod d_u for each u (the CRT where a 2 and the 3 share a factor)
    P = []
    for t in range(3):
        xs = [0] * len(ms)
        for i in set(srcs):
            want = {DS[u]: int(u == t) for u in range(3) if srcs[u] == i}
            xs[i] = crt(want[2], 2, want[3], 3) if len(want) == 2 else next(iter(want.values()))
        P.append(xs)
    assert map_ok(ms, DS, A) and surj_cert(ms, DS, A, P), (ms, A, P)
    return A, P


# --- Mirror of kleinKill ----------------------------------------------------------------------

def coord_ok(z, r1, r2, r3):
    return (r1 - z) % 2 == 0 and (r2 - z) % 2 == 0 and (r3 - z) % 2 == 0 and (z + r1 + r2 + r3) % 4 == 0


def clash(R, z):
    return not any(all(coord_ok(z[i], r1[i], r2[i], r3[i]) for i in range(3)) for r1 in R for r2 in R for r3 in R)


def triples(Q, sigma, B):
    """Every (a, b, sigma - a - b) with |a|, |b| <= B and square sum Q."""
    return [(a, b, sigma - a - b) for a in range(-B, B + 1) for b in range(-B, B + 1)
            if a * a + b * b + (sigma - a - b) ** 2 == Q]


def res4(d):
    return tuple(x % 4 for x in d)


def klein_kill(n, t, Qz, s, Bd, Bz, R):
    return (t * t == n and n < (Bd + 1) ** 2 and Qz < (Bz + 1) ** 2
            and all(res4(d) in R for sg in (t, -t) for d in triples(n, sg, Bd))
            and all(clash(R, z) for sg in (s, -s) for z in triples(Qz, sg, Bz)))


def params(v, k, lam):
    """`KleinKills` data (s, t, Bd, Bz, R), R the residues of every twisted sum; None if the check fails."""
    n, S = k - lam, k + lam * (v - 1)
    s, t = math.isqrt(S), math.isqrt(n) if n >= 0 else -1
    if v % 3 or s * s != S or t * t != n:
        return None
    Qz = k + lam * (v // 3 - 1)
    Bd, Bz = t, math.isqrt(Qz)
    R = sorted({res4(d) for sg in (t, -t) for d in triples(n, sg, Bd)})
    return (s, t, Bd, Bz, R) if klein_kill(n, t, Qz, s, Bd, Bz, R) else None


def triple_lean(r):
    return "(" + ", ".join(map(str, r)) + ")"


def r_name(n):
    return f"R{n}"


def kills_name(v, k, lam):
    return f"kills_{v}_{k}_{lam}"


def write_params(sets):
    rs = {}
    for (v, k, lam), (s, t, Bd, Bz, R) in sorted(sets.items()):
        rs.setdefault(k - lam, R)
        assert rs[k - lam] == R
    body = []
    for n, R in sorted(rs.items()):
        body.append(f"/-- The residues mod 4 of every twisted sum for `n = {n}`. -/\n"
                    f"def {r_name(n)} : List Triple :=\n  {lst([triple_lean(r) for r in R])}\n")
    for (v, k, lam), (s, t, Bd, Bz, R) in sorted(sets.items()):
        Qz = k + lam * (v // 3 - 1)
        body.append(f"/-- ({v}, {k}, {lam}): `s = {s}`, the contraction to `ZMod 3` has square sum {Qz}. -/\n"
                    f"theorem {kills_name(v, k, lam)} : KleinKills {v} {k} {lam} :=\n"
                    f"  ⟨{s}, {t}, {Bd}, {Bz}, {r_name(k - lam)}, by decide +kernel⟩\n")
    ns = f"{PREFIX}.Params"
    text = f"""module

public import SignedDifferenceSets.KleinTomography

/-!
# Klein tomography: the parameter sets

`KleinKills v k λ` for the {len(sets)} parameter sets of the rows in `KleinTomographyRows`, each by one
`decide +kernel`: `R<n>` holds the residues mod 4 of every twisted sum (sum `±√n`, square sum `n`),
and every contraction to `ZMod 3` clashes with them. Generated by `solver/kleinrows.py`.
-/

@[expose] public section

namespace {ns}

open SignedDifferenceSets.KleinTomography

set_option maxRecDepth 100000

""" + "\n".join(body) + f"\nend {ns}\n"
    (OUT_DIR / "Params.lean").write_text(text, encoding="utf-8", newline="\n")


def write_row(rid, v, k, lam, ms, A, P):
    group = " × ".join(f"ZMod {m}" for m in ms)
    ns = f"{PREFIX}.{rid}"
    text = f"""module

public import {PREFIX}.Params

/-!
# {rid}: no ({v}, {k}, {lam}) SDS in {group} (Klein tomography)

Open in Gordon's table (`SDS({v},{k},{lam},{lst(ms).replace(' ', '')})`, 2026-11-05). The forms map the group onto
`ZMod 2 × ZMod 2 × ZMod 3`, and `Params.{kills_name(v, k, lam)}` rules ({v}, {k}, {lam}) out there
(`KleinTomography.not_hasSDS_of_kleinKills`). Generated by `solver/kleinrows.py`.
-/

@[expose] public section

namespace {ns}

open SignedDifferenceSets.KleinTomography

/-- {rid}: no SDS ({v}, {k}, {lam}) in `{group}`. -/
theorem not_hasSDS : ¬ HasSDS ({group}) {k} {lam} :=
  KleinCert.not_hasSDS (w := ⟨{rid[1:]}, {lst(ms)}, {k}, {lam}⟩)
    (c := ⟨{lst([lst(a) for a in A])}, {lst([lst(p) for p in P])}⟩)
    (by decide +kernel) (by decide) Params.{kills_name(v, k, lam)} _

end {ns}
"""
    assert max(len(line) for line in text.splitlines()) <= 100, rid
    (OUT_DIR / f"{rid}.lean").write_text(text, encoding="utf-8", newline="\n")


def main(wanted):
    rows = load_rows()
    ids = [line.split()[0] for line in KILLS.read_text(encoding="utf-8").splitlines() if "flatk p=2" in line]
    ids = [i for i in ids if not wanted or i in wanted]
    sets, todo = {}, []
    for rid in ids:
        v, k, lam, ms = parse_key(rows[rid]["key"])
        assert rows[rid]["status"] == "open" and lam >= 0, rid
        key = (v, k, lam)
        if key not in sets:
            sets[key] = params(v, k, lam)
            assert sets[key] is not None, (rid, key)
        A, P = quotient(ms)
        todo.append((rid, v, k, lam, ms, A, P))
    OUT_DIR.mkdir(exist_ok=True)
    write_params(sets)
    for row in todo:
        write_row(*row)
    print(len(todo), "rows,", len(sets), "parameter sets:", " ".join(r[0] for r in todo))


def tests():
    """Control data: the residues and the contraction verdict for exists rows (must not be killed)."""
    rows = load_rows()
    for rid in ("N170", "N931", "N934"):
        v, k, lam, ms = parse_key(rows[rid]["key"])
        n, S = k - lam, k + lam * (v - 1)
        s, t = math.isqrt(S), math.isqrt(n)
        Qz = k + lam * (v // 3 - 1)
        Bd, Bz = t, math.isqrt(Qz)
        R = sorted({res4(d) for sg in (t, -t) for d in triples(n, sg, Bd)})
        zs = [z for sg in (s, -s) for z in triples(Qz, sg, Bz) if not clash(R, z)]
        print(rid, (v, k, lam), ms, "s", s, "t", t, "Qz", Qz, "Bd", Bd, "Bz", Bz, "R", R, "unclashed z", zs[:4],
              "kill", klein_kill(n, t, Qz, s, Bd, Bz, R), "forms", quotient(ms))


if __name__ == "__main__":
    if sys.argv[1:] == ["--tests"]:
        tests()
    else:
        main(set(sys.argv[1:]))
