"""I23: line tomography rows on Z_p x Z_p, the Lean files (Tomography.not_hasSDS).

tomorows.py <id> [<id> ...] [--test]: for each row of instances.csv on [p, p] (p prime, p not dividing s),
mirrors Tomography's kernel checks exactly: inSearch (noVector's search, |w0| largest, leaves listed in V0),
rotOK (W = the rotations of V0 with sum_t t w(t) = 0 mod p), certRows (rows from vectors w on the numbers
x = a p + b whose pushforwards to the lines after depth d vanish mod p; at each depth a basis of the new
functionals, so a leaf is reached only by an integral choice) and tomoGo (one vector of W per line, line 0:
b, line j >= 1: a + (j - 1) b). Splits inSearch by first coordinates and tomoGo at a front (tomoTop) into
kernel checks of at most VSLICE / TSLICE nodes, and writes lean/SignedDifferenceSets/TomographyRows/N<id>.lean.
--test prints the verdicts and node counts only (the exists rows must give FOUND).
"""
import csv
import math
import re
import sys

DIR = "lean/SignedDifferenceSets/TomographyRows"
VSLICE = 20000     # inSearch nodes per kernel check
TSLICE = 3000      # tomoGo nodes per kernel check


def row_of(id_):
    for r in csv.DictReader(open("instances.csv", encoding="utf-8")):
        if r["id"] == id_:
            v, k, l, f = re.match(r"SDS\((\d+),(-?\d+),(-?\d+),\[([\d,]+)\]\)", r["key"]).groups()
            return int(v), int(k), int(l), [int(x) for x in f.split(",")], r["status"]
    raise KeyError(id_)


# ---------- inSearch (mirror of VectorSearch.cut / leafOK and TomographySearch.goIn) ----------

def cut(c, Q, s, rem, sm, sq):
    return Q - sq < 0 or rem * (Q - sq) < (s - sm) ** 2 or rem * c < abs(s - sm)


def leaf_ok(p, Q, t, k, s, w, sm, sq, ab):
    return (sm == s and sq == Q and ab <= k and (k - ab) % 2 == 0 and
            all(sum(w[x] * w[(x + g) % p] for x in range(p)) == t for g in range(1, p)))


def go_in(p, c, Q, t, k, s, top, rem, pre, sm, sq, ab, out, cnt):
    """Mirror of goIn; appends the listed leaves to out, counts calls in cnt[0]."""
    cnt[0] += 1
    if rem == 0:
        if leaf_ok(p, Q, t, k, s, pre, sm, sq, ab):
            out.append(tuple(pre))
        return
    if cut(c, Q, s, rem, sm, sq):
        return
    for x in range(-top, top + 1):
        if Q - sq < x * x:
            continue
        go_in(p, c, Q, t, k, s, top, rem - 1, pre + [x], sm + x, sq + x * x, ab + abs(x), out, cnt)


def in_search(p, k, lam, s):
    """V0 and the node count per first coordinate x in [-c, c]."""
    c, Q, t = p, k + lam * (p - 1), lam * p
    out, per = [], {}
    if cut(c, Q, s, p, 0, 0):
        return out, per
    for x in range(-c, c + 1):
        cnt = [0]
        if not Q < x * x:
            go_in(p, c, Q, t, k, s, abs(x), p - 1, [x], x, x * x, abs(x), out, cnt)
        per[x] = cnt[0]
    return out, per


def rot(p, r, v):
    return tuple(v[(i + r) % p] for i in range(p))


def m1ok(p, v):
    return sum(v[i] * i for i in range(p)) % p == 0


# ---------- lines and certificates ----------

def line_idx(p, j, x):
    return x % p if j == 0 else (x // p + (j - 1) * (x % p)) % p


def push(p, j, w):
    out = [0] * p
    for x in range(p * p):
        out[line_idx(p, j, x)] += w[x]
    return out


def rref(rows, p):
    rows = [list(r) for r in rows]
    piv, rk = [], 0
    for col in range(len(rows[0]) if rows else 0):
        r = next((i for i in range(rk, len(rows)) if rows[i][col] % p), None)
        if r is None:
            continue
        rows[rk], rows[r] = rows[r], rows[rk]
        inv = pow(rows[rk][col], -1, p)
        rows[rk] = [v * inv % p for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] % p:
                f = rows[i][col]
                rows[i] = [(u - f * v) % p for u, v in zip(rows[i], rows[rk])]
        piv.append(col)
        rk += 1
    return rows[:rk], piv


def nullspace(M, n, p):
    R, piv = rref(M, p) if M else ([], [])
    basis = []
    for f in (j for j in range(n) if j not in piv):
        w = [0] * n
        w[f] = 1
        for r, pc in zip(R, piv):
            w[pc] = (-r[f]) % p
        basis.append(w)
    return basis


def certs(p):
    """ws[d]: vectors w vanishing (mod p) on the lines after d whose functionals are new at depth d."""
    n, L = p * p, p + 1
    ws, base = [], []
    for d in range(L):
        M = [[1 if line_idx(p, j, x) == t else 0 for x in range(n)] for j in range(d + 1, L) for t in range(p)]
        new = []
        for w in nullspace(M, n, p):
            f = [v % p for j in range(L) for v in push(p, j, w)]
            assert not any(f[(d + 1) * p:])
            if not any(f):
                continue
            if len(rref(base + [f], p)[0]) > len(base):
                base.append(f)
                new.append(w)
        ws.append(new)
    assert len(rref(base, p)[0]) == len(base)
    return ws


def row_of_w(p, s, d, w):
    """Mirror of rowOf: pushforwards on lines d, d - 1, ..., 0 mod p, and s * sum w mod p."""
    return ([[v % p for v in push(p, j, w)] for j in reversed(range(d + 1))], s * sum(w) % p)


def vanishes(p, d, w):
    return all(j <= d or all(v % p == 0 for v in push(p, j, w)) for j in range(p + 1))


# ---------- tomoGo ----------

def dot(p, P, y):
    return sum(P[t] * y[t] for t in range(p))


def row_sum(p, Ps, cur):
    return sum(dot(p, P, y) for P, y in zip(Ps, cur))


def leaf_sds(p, s, ys):
    for x in range(p * p):
        f = sum(ys[j][line_idx(p, j, x)] for j in range(p + 1)) - s
        if f not in (0, p, -p):
            return False
    return True


def tomo_go(p, s, W, R, cur, stats):
    """Mirror of tomoGo (cur newest first); True when no completion passes. Counts calls per depth."""
    d = len(cur)
    stats[d] = stats.get(d, 0) + 1
    if not R:
        ok = leaf_sds(p, s, list(reversed(cur)))
        if ok:
            stats["found"] = stats.get("found", 0) + 1
        return not ok
    rs, rest = R[0], R[1:]
    tg = [(r[0][0] if r[0] else [], r[1] - row_sum(p, r[0][1:], cur)) for r in rs]
    for y in W:
        if all((dot(p, P, y) - t) % p == 0 for P, t in tg):
            if not tomo_go(p, s, W, rest, [y] + cur, stats):
                return False
    return True


def front(p, W, R, m):
    """The nodes m levels down that tomoTop leaves to P (cur newest first), in search order."""
    out = []

    def rec(R, cur, m):
        if m == 0:
            out.append(cur)
            return
        if not R:
            return
        rs, rest = R[0], R[1:]
        tg = [(r[0][0] if r[0] else [], r[1] - row_sum(p, r[0][1:], cur)) for r in rs]
        for y in W:
            if all((dot(p, P, y) - t) % p == 0 for P, t in tg):
                rec(rest, [y] + cur, m - 1)
    rec(R, [], m)
    return out


def subtree_nodes(p, s, W, R, cur):
    st = {}
    res = tomo_go(p, s, W, R, cur, st)
    return res, sum(v for k, v in st.items() if isinstance(k, int))


# ---------- Lean output ----------

def lst(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def wrap(items, indent, width=100):
    """Comma-separated items wrapped at width."""
    lines, cur = [], indent
    for i, it in enumerate(items):
        piece = it + ("," if i < len(items) - 1 else "")
        if len(cur) + len(piece) + 1 > width and cur.strip():
            lines.append(cur.rstrip())
            cur = indent
        cur += piece + " "
    lines.append(cur.rstrip())
    return "\n".join(lines)


def flat(obj):
    if isinstance(obj, tuple):
        return "(" + ", ".join(flat(x) for x in obj) + ")"
    if isinstance(obj, list):
        return "[" + ", ".join(flat(x) for x in obj) + "]"
    return str(obj)


def fmt(obj, ind, width=96):
    """Lean text of nested lists / pairs of ints, starting after `ind`, lines within width."""
    one = flat(obj)
    if len(ind) + len(one) <= width:
        return one
    if isinstance(obj, tuple):
        return "(" + fmt(obj[0], ind + " ") + ",\n" + ind + " " + fmt(obj[1], ind + " ") + ")"
    if all(not isinstance(x, (list, tuple)) for x in obj):
        return "[\n" + wrap([str(x) for x in obj], ind + "  ", width) + "]"
    return "[\n" + ",\n".join(ind + "  " + fmt(x, ind + "  ") for x in obj) + "]"


def lean_list(items, indent="  "):
    if not items:
        return "[]"
    return "[\n" + wrap(items, indent + "  ") + "]"


def fix_search(p, k, lam, s, fr):
    """Mirror of TomographyOrbit.fixGo: the listed leaves (valid, m1ok) and the node count."""
    c, Q, t = p, k + lam * (p - 1), lam * p
    out, cnt = [], [0]

    def go(rem, pre, sm, sq, ab):
        cnt[0] += 1
        if rem == 0:
            if leaf_ok(p, Q, t, k, s, pre, sm, sq, ab) and m1ok(p, pre):
                out.append(tuple(pre))
            return
        if cut(c, Q, s, rem, sm, sq):
            return
        h = len(pre)
        xs = [pre[fr[h]]] if fr[h] < h else range(-c, c + 1)
        for x in xs:
            go(rem - 1, pre + [x], sm + x, sq + x * x, ab + abs(x))
    go(p, [], 0, 0, 0)
    return out, cnt[0]


def is_prime(n):
    return n > 1 and all(n % q for q in range(2, math.isqrt(n) + 1))


def analyse(id_, orbit=False):
    v, k, lam, f, status = row_of(id_)
    assert len(f) == 2 and f[0] == f[1], f
    p = f[0]
    s2 = k + lam * (p * p - 1)
    s = math.isqrt(s2)
    assert s * s == s2 and s % p != 0, (id_, s2)
    orb = None
    if orbit:
        n = k - lam
        assert is_prime(n) and n % p not in (0, 1), (id_, n)
        fr, ex = [0] * p, [0] * p
        for h in range(1, p):
            e, x = 0, h
            # walk back along the orbit: h = n^e * r with r the smallest element of the orbit
            orbit_h = []
            y = h
            while y not in orbit_h:
                orbit_h.append(y)
                y = y * n % p
            r = min(orbit_h)
            e = next(e for e in range(p) if pow(n, e, p) * r % p == h)
            fr[h], ex[h] = r, e
        W, vnodes = fix_search(p, k, lam, s, fr)
        V0, per = [], {}
        orb = dict(n=n, fr=fr, ex=ex, nodes=vnodes)
    else:
        V0, per = in_search(p, k, lam, s)
        W = sorted({rot(p, r, v_) for v_ in V0 for r in range(p) if m1ok(p, rot(p, r, v_))})
    ws = certs(p)
    assert all(vanishes(p, d, w) for d in range(p + 1) for w in ws[d])
    R = [[row_of_w(p, s, d, w) for w in ws[d]] for d in range(p + 1)]
    st = {}
    killed = tomo_go(p, s, W, R, [], st)
    return dict(id=id_, p=p, k=k, lam=lam, s=s, status=status, V0=V0, per=per, W=W, ws=ws, R=R,
                killed=killed, stats=st, orbit=orb)


def vparts(per, c):
    """Consecutive first-coordinate ranges with at most VSLICE nodes each: (lo, m, nodes)."""
    parts, lo, m, acc = [], -c, 0, 0
    for x in range(-c, c + 1):
        n = per.get(x, 1)
        if m and acc + n > VSLICE:
            parts.append((lo, m, acc))
            lo, m, acc = x, 0, 0
        m += 1
        acc += n
    parts.append((lo, m, acc))
    return parts


def write_row(a):
    id_, p, k, lam, s = a["id"], a["p"], a["k"], a["lam"], a["s"]
    orb = a["orbit"]
    # tomoGo split at the shallowest depth whose subtrees all have at most TSLICE nodes
    total = sum(v_ for kk, v_ in a["stats"].items() if isinstance(kk, int))
    m, P, sizes = 0, [[]], [total]
    while max(sizes) > TSLICE and m < p:
        m += 1
        P = front(p, a["W"], a["R"], m)
        sizes = [subtree_nodes(p, s, a["W"], a["R"][m:], q)[1] for q in P]
        assert all(subtree_nodes(p, s, a["W"], a["R"][m:], q)[0] for q in P)
    batches, cur, acc = [], [], 0
    for q, n_ in zip(P, sizes):
        if cur and acc + n_ > TSLICE:
            batches.append((cur, acc))
            cur, acc = [], 0
        cur.append(q)
        acc += n_
    batches.append((cur, acc))
    vp = vparts(a["per"], p)
    Q = f"(({k} : ℕ) + ({lam} : ℤ) * (({p} : ℕ) - 1))"
    T = f"(({lam} : ℤ) * ({p} : ℕ))"
    args = f"(Indexed.size (ZMod {p})) (Indexed.addIdx (ZMod {p})) ({p} : ℕ)\n    {Q} {T} ({k} : ℕ) {s}"
    split = (f"`tomoGo` ({total} nodes; split {m} levels down into {len(P)} subtrees,\n"
             f"{len(batches)} checks) finds no choice of one per line whose line sums are integral.")
    out = []
    if orb:
        n = orb["n"]
        out.append(f"""module

public import SignedDifferenceSets.TomographyOrbit

/-!
# {id_}: no SDS ({p * p}, {k}, {lam}) in C{p} × C{p} (I23, line tomography)

`s = {s}`, `{p} ∤ s`; `n = k − λ = {n}` is prime, `{n} ≡ {n % p} (mod {p})`, a multiplier (C10).
After centring, each line contraction (fibres of {p}) is fixed by `h ↦ {n} h`; `fixSearch`
({orb["nodes"]} nodes) lists them: the {len(a["W"])} of `w`. {split}
Generated by `solver/tomorows.py --orbit`.
-/""")
    else:
        out.append(f"""module

public import SignedDifferenceSets.Tomography

/-!
# {id_}: no SDS ({p * p}, {k}, {lam}) in C{p} × C{p} (I23, line tomography)

`s = {s}`, `{p} ∤ s`. Each line contraction (fibres of {p}) is a rotation of one of the
{len(a["V0"])} vectors of `v0` (`inSearch`, {sum(a["per"].values())} nodes in {len(vp)} checks); after
centring, it is one of the {len(a["W"])} of `w`. {split}
Generated by `solver/tomorows.py`.
-/""")
    out.append(f"""
@[expose] public section

namespace SignedDifferenceSets.TomographyRows.{id_}

open Tomography

set_option maxRecDepth 100000
-- one kernel check at a time
set_option Elab.async false
""")
    if orb:
        out.append(f"""/-- `fr h`: the smallest element of the orbit of `h` under `h ↦ {n} h`. -/
def fr : List ℕ :=
  {fmt(orb["fr"], "  ")}

/-- `h ≡ {n} ^ ex h · fr h (mod {p})`. -/
def ex : List ℕ :=
  {fmt(orb["ex"], "  ")}

/-- The centred vectors fixed by `h ↦ {n} h` meeting a line contraction's demands. -/
def w : List (List ℤ) :=
  {fmt([list(x) for x in a["W"]], "  ")}
""")
    else:
        out.append(f"""/-- The vectors meeting a line contraction's demands, `|w₀|` largest. -/
def v0 : List (List ℤ) :=
  {fmt([list(x) for x in a["V0"]], "  ")}

/-- Their rotations with `Σ t w(t) ≡ 0 (mod {p})`. -/
def w : List (List ℤ) :=
  {fmt([list(x) for x in a["W"]], "  ")}
""")
    out.append("/-- The certificate: per depth, vectors on the numbers `x = a p + b`. -/")
    out.append("def ws : List (List (List ℤ)) :=")
    out.append("  " + fmt([[list(x) for x in wd] for wd in a["ws"]], "  "))
    out.append("")
    out.append("/-- `certRows` of `ws`, stored so that `tomoGo` reads them. -/")
    out.append("def rows : List (List Row) :=")
    out.append("  " + fmt([[(list(Ps), t) for Ps, t in rd] for rd in a["R"]], "  "))
    out.append("")
    if orb:
        out.append(f"theorem hfr : frOK {p} {n} fr ex = true := by decide +kernel\n")
        out.append(f"-- {orb['nodes']} nodes")
        out.append(f"theorem hV : fixSearch {args}\n    fr w = true := by\n  decide +kernel\n")
    else:
        for i, (lo, mm, nn) in enumerate(vp):
            out.append(f"-- {nn} nodes")
            out.append(f"theorem vpart{i} : inPart {args}\n    v0 ({lo}) {mm} = true := by\n  decide +kernel\n")
        out.append(f"theorem hV : inSearch {args} v0 = true := by")
        prev = "vpart0"
        for i in range(1, len(vp)):
            out.append(f"  have j{i} := inPart_add' {prev} vpart{i} (by decide)")
            prev = f"j{i}"
        out.append(f"  exact inSearch_of_inPart {prev} (by decide) (by decide)\n")
        out.append(f"theorem hW : rotOK {p} v0 w = true := by decide +kernel\n")
    out.append(f"theorem hc : certOK {p} ws = true := by decide +kernel\n")
    out.append(f"theorem hR : certRows {p} {s} ws = rows := by decide +kernel\n")
    if m == 0:
        out.append(f"-- {total} nodes")
        out.append(f"theorem hT : tomoGo {p} {s} w rows [] = true := by decide +kernel\n")
    else:
        for i, (b, nn) in enumerate(batches):
            out.append(f"/-- Subtrees, batch {i} ({nn} nodes). -/")
            out.append(f"def batch{i} : List (List (List ℤ)) :=")
            out.append("  " + fmt([[list(y) for y in q] for q in b], "  "))
            out.append("")
            out.append(f"theorem tpart{i} :")
            out.append(f"    (batch{i}.all fun q => tomoGo {p} {s} w (rows.drop {m}) q) = true := by")
            out.append("  decide +kernel")
            out.append("")
        nb = len(batches)
        chain = f"batch{nb - 1}"
        for i in reversed(range(nb - 1)):
            chain = f"batch{i} ++ ({chain})" if i < nb - 2 else f"batch{i} ++ {chain}"
        lines, cur = [], "  "
        for wd in chain.split(" "):
            if len(cur) + len(wd) + 1 > 100 and cur.strip():
                lines.append(cur.rstrip())
                cur = "    "
            cur += wd + " "
        lines.append(cur.rstrip())
        out.append("/-- The nodes the top levels leave to the batches. -/")
        out.append("def front : List (List (List ℤ)) :=")
        out.append("\n".join(lines))
        out.append("")
        out.append(f"theorem htop : tomoTop {p} {s} w front {m} rows [] = true := by")
        out.append("  decide +kernel")
        out.append("")
        out.append(f"theorem hT : tomoGo {p} {s} w rows [] = true :=")
        out.append(f"  tomoGo_of_top {m} rows [] htop fun q hq => by")
        if nb == 1:
            out.append("    simp only [front] at hq")
            out.append("    exact List.all_eq_true.1 tpart0 q hq")
        else:
            out.append("    simp only [front, List.mem_append] at hq")
            out.append("    rcases hq with " + " | ".join(["h"] * nb))
            for i in range(nb):
                out.append(f"    · exact List.all_eq_true.1 tpart{i} q h")
        out.append("")
    if orb:
        final = (f"@Tomography.not_hasSDS_prime {p} ⟨by norm_num⟩ {k} ({lam}) {s} {orb['n']} (by norm_num)\n"
                 f"    (by norm_num) (by decide) (by decide) (by norm_num) (by decide) fr ex hfr w ws rows\n"
                 f"    hV hc hR hT")
    else:
        final = (f"@Tomography.not_hasSDS {p} ⟨by norm_num⟩ {k} ({lam}) {s} (by norm_num) (by decide) v0 w ws\n"
                 f"    rows hV hW hc hR hT")
    out.append(f"""/-- {id_}: C{p} × C{p} has no signed difference set with parameters ({p * p}, {k}, {lam}). -/
theorem not_hasSDS : ¬ HasSDS (ZMod {p} × ZMod {p}) {k} {lam} :=
  {final}

end SignedDifferenceSets.TomographyRows.{id_}
""")
    import os
    os.makedirs(DIR, exist_ok=True)
    path = f"{DIR}/{id_}.lean"
    open(path, "w", encoding="utf-8", newline="\n").write("\n".join(out))
    return path, m, len(P), [nn for _, nn in batches], vp


TEST = "lean/SignedDifferenceSets/Tests/Tomography.lean"


def write_tests():
    """Tests: N49 (C5 x C5, full lists) and N352 (C7 x C7) must not be killed; broken inputs refused."""
    a, b = analyse("N49"), analyse("N352")
    assert not a["killed"] and not b["killed"]
    args49 = ("(Indexed.size (ZMod 5)) (Indexed.addIdx (ZMod 5)) (5 : ℕ)\n    "
              "((12 : ℕ) + (1 : ℤ) * ((5 : ℕ) - 1)) ((1 : ℤ) * (5 : ℕ)) (12 : ℕ) 6")
    # a vector at depth 0 whose pushforwards to the later lines do not vanish mod 5: the point 0
    bad_ws = [[[1] + [0] * 24]] + [[list(x) for x in a["ws"][d]] for d in range(1, 6)]
    bad_rows = [[(list(Ps), t) for Ps, t in rd] for rd in a["R"]]
    Ps, t = bad_rows[5][0]
    bad_rows[5][0] = (Ps, (t + 1) % 5)
    out = [f"""module

public import SignedDifferenceSets.Tomography

/-!
# Tests: line tomography (I23)

The check must not kill an `exists` row: on N49 (25, 12, 1) in C₅ × C₅ the lists are complete
and `tomoGo` finds a choice (it returns `false`); so it does on N352 (49, 33, 1) in C₇ × C₇
(object O24). Broken inputs are refused: a list missing a vector, a certificate vector that
does not vanish after its depth, a row whose target is off. Generated by
`solver/tomorows.py --tests`.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.Tomography

open SignedDifferenceSets.Tomography

set_option maxRecDepth 100000

/-- N49's vectors with `|w₀|` largest. -/
def v0N49 : List (List ℤ) :=
  {fmt([list(x) for x in a["V0"]], "  ")}

/-- N49's centred rotations. -/
def wN49 : List (List ℤ) :=
  {fmt([list(x) for x in a["W"]], "  ")}

/-- The certificate for `p = 5`. -/
def ws5 : List (List (List ℤ)) :=
  {fmt([[list(x) for x in wd] for wd in a["ws"]], "  ")}

/-- Its rows for `s = 6`. -/
def rowsN49 : List (List Row) :=
  {fmt([[(list(Ps), t) for Ps, t in rd] for rd in a["R"]], "  ")}

example : inSearch {args49}
    v0N49 = true := by
  decide +kernel

example : rotOK 5 v0N49 wN49 = true := by decide +kernel

example : certOK 5 ws5 = true := by decide +kernel

example : certRows 5 6 ws5 = rowsN49 := by decide +kernel

/-- N49 exists: the search finds a choice. -/
example : tomoGo 5 6 wN49 rowsN49 [] = false := by decide +kernel

/-- N352's centred vectors (from its {len(b["V0"])} vectors with `|w₀|` largest). -/
def wN352 : List (List ℤ) :=
  {fmt([list(x) for x in b["W"]], "  ")}

/-- The certificate's rows for `p = 7`, `s = 9`. -/
def rowsN352 : List (List Row) :=
  {fmt([[(list(Ps), t) for Ps, t in rd] for rd in b["R"]], "  ")}

/-- N352 exists: the search finds a choice. -/
example : tomoGo 7 9 wN352 rowsN352 [] = false := by decide +kernel

/-- A list missing a vector is refused. -/
example : inSearch {args49}
    v0N49.tail = false := by
  decide +kernel

example : rotOK 5 v0N49 wN49.tail = false := by decide +kernel

/-- A certificate vector that does not vanish after its depth is refused. -/
example : certOK 5
    {fmt(bad_ws, "    ")} = false := by
  decide +kernel

/-- A row whose target is off is not the certificate's. -/
example : certRows 5 6 ws5 ≠
    {fmt(bad_rows, "    ")} := by
  decide +kernel

end SignedDifferenceSets.Tests.Tomography
"""]
    open(TEST, "w", encoding="utf-8", newline="\n").write("\n".join(out))
    print("wrote", TEST)


def main():
    if "--tests" in sys.argv:
        write_tests()
        return
    test = "--test" in sys.argv
    for id_ in [x for x in sys.argv[1:] if not x.startswith("--")]:
        a = analyse(id_, orbit="--orbit" in sys.argv)
        st = a["stats"]
        print(id_, (a["p"], a["k"], a["lam"]), "s", a["s"], a["status"], "|V0|", len(a["V0"]), "vnodes",
              (a["orbit"]["nodes"] if a["orbit"] else sum(a["per"].values())), "|W|", len(a["W"]), "rows/depth", [len(r) for r in a["R"]],
              "KILLED" if a["killed"] else "FOUND", "nodes/depth",
              [st.get(d, 0) for d in range(a["p"] + 2)], flush=True)
        if not test and a["killed"]:
            print("  wrote", write_row(a), flush=True)


if __name__ == "__main__":
    main()
