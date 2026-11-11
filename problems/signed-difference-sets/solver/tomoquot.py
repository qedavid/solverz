"""I23 on a quotient: line tomography rows through G -> Z_p x Z_p, the Lean files (Tomography.not_hasSDS_grp).

tomoquot.py <id> [<id> ...] [--test]: for each row of instances.csv whose group has p-rank >= 2 (p prime, p not
dividing s), with fibres c = v / p^2: phi = reduction mod p of two factors divisible by p (forms A); the line vectors
(fibres c p) meet C3's demands. With a multiplier t of order > 1 mod p allowed by C10' (p not dividing n = k - lam,
t a power of every prime q | n mod p), the centred line vectors are constant on the orbits of h -> t h and orbSearch
lists them (one value per orbit, the last solved from the sum); otherwise inSearch and rotOK as in tomorows.py.
The choice is ruled out by one point (ptOK: the residues of sum_j y_j(line_j g) reachable from W miss s) or by
tomoGoL with tomorows.py's certificate and the leaf "every lineSum - s = p z with |z| <= c". Mirrors every kernel
check exactly and writes lean/SignedDifferenceSets/TomographyQuotRows/N<id>.lean. --test: verdicts and counts only.
Existing generator tomorows.py is imported, not changed.
"""
import csv
import math
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tomorows as T  # noqa: E402

DIR = "lean/SignedDifferenceSets/TomographyQuotRows"
TSLICE = int(os.environ.get("TSLICE", 6000))   # tomoGoL nodes per kernel check
VSLICE = 20000     # inSearch nodes per kernel check
VSPLIT = 30000     # an inPart above this many nodes is split below its first coordinate


def row_of(id_):
    for r in csv.DictReader(open("instances.csv", encoding="utf-8")):
        if r["id"] == id_:
            v, k, l, f = re.match(r"SDS\((\d+),(-?\d+),(-?\d+),\[([\d,]+)\]\)", r["key"]).groups()
            return int(v), int(k), int(l), [int(x) for x in f.split(",")], r["status"]
    raise KeyError(id_)


def factor(n):
    f, q = {}, 2
    while q * q <= n:
        while n % q == 0:
            f[q] = f.get(q, 0) + 1
            n //= q
        q += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def mult_data(p, n):
    """The t of largest order mod p (then the smallest) that C10' allows, and fs = [(q, e, f)] with
    t = q^f mod p; or None."""
    if n == 0 or n % p == 0:
        return None
    fac = factor(n)
    best = None
    for t in range(2, p):
        fs = []
        for q, e in sorted(fac.items()):
            f = next((f for f in range(1, p) if pow(q, f, p) == t), None)
            if f is None:
                break
            fs.append((q, e, f))
        else:
            order = next(o for o in range(1, p) if pow(t, o, p) == 1)
            if best is None or order > best[0]:
                best = (order, t, fs)
    return best[1:] if best else None


def orb_data(p, t):
    """orb h: orbit index (orbits numbered by their smallest element); rep, ex with h = t^ex * rep mod p; sizes."""
    reps, orb, ex = [], [0] * p, [0] * p
    for h in range(p):
        o = [pow(t, e, p) * h % p for e in range(p)]
        r = min(o)
        if r == h:
            reps.append(h)
        orb[h] = reps.index(r)
        ex[h] = next(e for e in range(p) if pow(t, e, p) * r % p == h)
    sz = [orb.count(i) for i in range(len(reps))]
    return orb, sz, reps, ex


def orb_search(p, C, k, lam, s, orb, sz):
    """Mirror of orbGo: the listed vectors and the node count."""
    Q, t = k + lam * (C - 1), lam * C
    m = len(sz)
    out, cnt = [], [0]

    def go(i, vals, sm, sq):
        cnt[0] += 1
        if i == m - 1:
            r = s - sm
            if r % sz[i] or abs(r // sz[i]) > C:
                return
            vals = vals + [r // sz[i]]
            y = [vals[orb[h]] for h in range(p)]
            if (T.leaf_ok(p, Q, t, k, s, y, sum(y), sum(x * x for x in y), sum(abs(x) for x in y))
                    and T.m1ok(p, y)):
                out.append(tuple(y))
            return
        if T.cut(C, Q, s, sum(sz[i:]), sm, sq):
            return
        for u in range(-C, C + 1):
            if Q - sq < sz[i] * u * u:
                continue
            go(i + 1, vals + [u], sm + sz[i] * u, sq + sz[i] * u * u)
    go(0, [], 0, 0)
    return out, cnt[0]


def in_search(p, C, k, lam, s):
    """Mirror of inSearch with fibres C: V0 and the node count per first coordinate."""
    Q, t = k + lam * (C - 1), lam * C
    out, per = [], {}
    if T.cut(C, Q, s, p, 0, 0):
        return out, per
    for x in range(-C, C + 1):
        cnt = [0]
        if not Q < x * x:
            T.go_in(p, C, Q, t, k, s, abs(x), p - 1, [x], x, x * x, abs(x), out, cnt)
        per[x] = cnt[0]
    return out, per


def in_front(p, C, k, lam, s, x, d):
    """Mirror of goInTop below the first coordinate x: the prefixes d levels down."""
    Q = k + lam * (C - 1)
    out, top = [], abs(x)

    def rec(pre, sm, sq, rem, dd):
        if dd == 0:
            out.append(list(pre))
            return
        assert rem > 0
        if T.cut(C, Q, s, rem, sm, sq):
            return
        for y in range(-top, top + 1):
            if Q - sq < y * y:
                continue
            rec(pre + [y], sm + y, sq + y * y, rem - 1, dd - 1)
    rec([x], x, x * x, p - 1, d)
    return out


def below_nodes(p, C, k, lam, s, q):
    """Mirror of belowIn's node count for the prefix q."""
    Q, t = k + lam * (C - 1), lam * C
    cnt, out = [0], []
    T.go_in(p, C, Q, t, k, s, abs(q[0]), p - len(q), list(q), sum(q), sum(x * x for x in q),
            sum(abs(x) for x in q), out, cnt)
    return cnt[0]


def batch_by(items, sizes, cap):
    batches, cur, acc = [], [], 0
    for it, n_ in zip(items, sizes):
        if cur and acc + n_ > cap:
            batches.append((cur, acc))
            cur, acc = [], 0
        cur.append(it)
        acc += n_
    batches.append((cur, acc))
    return batches


def join_mem(name, nb, theorem, arg, whole=None):
    """Lean text: `name` = name_0 ++ (name_1 ++ …), and the membership split into theorem_j."""
    chain = f"{name}_{nb - 1}"
    for j in reversed(range(nb - 1)):
        chain = f"{name}_{j} ++ ({chain})" if j < nb - 2 else f"{name}_{j} ++ {chain}"
    lines, cur = [], "  "
    for wd in chain.split(" "):
        if len(cur) + len(wd) + 1 > 100 and cur.strip():
            lines.append(cur.rstrip())
            cur = "    "
        cur += wd + " "
    lines.append(cur.rstrip())
    if nb == 1:
        proof = [f"    simp only [{whole or name}] at hq", f"    exact List.all_eq_true.1 {theorem}_0 {arg} hq"]
    else:
        pat = "    rcases hq with " + " | ".join(["h"] * nb)
        if len(pat) > 100:  # many batches: the pattern continues on lines indented past `rcases`
            rows_ = [" | ".join(["h"] * min(20, nb - i)) for i in range(0, nb, 20)]
            pat = "    rcases hq with " + " |\n        ".join(rows_)
        proof = [f"    simp only [{whole or name}, List.mem_append] at hq", pat]
        proof += [f"    · exact List.all_eq_true.1 {theorem}_{j} {arg} h" for j in range(nb)]
    return "\n".join(lines), proof


def pt_ok(p, s, W, g):
    """Mirror of ptOK."""
    R = [0]
    for j in range(p + 1):
        S = [y[T.line_idx(p, j, g)] for y in W]
        R = [r2 for r2 in range(p) if any((r + v - r2) % p == 0 for r in R for v in S)]
    return not any((r - s) % p == 0 for r in R)


def leaf_q(p, s, c, ys):
    for x in range(p * p):
        f = sum(ys[j][T.line_idx(p, j, x)] for j in range(p + 1)) - s
        if f % p or abs(f) > p * c:
            return False
    return True


def tomo_go(p, s, c, W, R, cur, st):
    """Mirror of tomoGoL with leafQ (cur newest first); True when no completion passes."""
    st[0] += 1
    if not R:
        return not leaf_q(p, s, c, list(reversed(cur)))
    rs, rest = R[0], R[1:]
    tg = [(r[0][0] if r[0] else [], r[1] - T.row_sum(p, r[0][1:], cur)) for r in rs]
    for y in W:
        if all((T.dot(p, P, y) - t) % p == 0 for P, t in tg):
            if not tomo_go(p, s, c, W, rest, [y] + cur, st):
                return False
    return True


def forms(ms, p):
    """Two factors divisible by p, reduced mod p: forms A, preimages P (unit vectors)."""
    idx = [i for i, m in enumerate(ms) if m % p == 0][:2]
    assert len(idx) == 2, ms
    A = [[1 if i == j else 0 for i in range(len(ms))] for j in idx]
    return A, [list(a) for a in A]


def analyse(id_, p=None):
    v, k, lam, ms, status = row_of(id_)
    if p is None:
        s0 = math.isqrt(k + lam * (v - 1))
        p = max(q for q in range(2, v + 1) if v % (q * q) == 0 and sum(m % q == 0 for m in ms) >= 2
                and all(q % d for d in range(2, q)) and s0 % q)
    c = v // (p * p)
    assert c * p * p == v
    s2 = k + lam * (v - 1)
    s = math.isqrt(s2)
    assert s * s == s2, (id_, s2)
    nc = s % p == 0   # p | s: no centring, W = every rotation of V0, no multiplier
    C = c * p
    n = k - lam
    md = None if nc else mult_data(p, n)
    a = dict(id=id_, v=v, k=k, lam=lam, ms=ms, p=p, c=c, s=s, n=n, status=status, mult=md, nc=nc)
    if nc:
        V0, per = in_search(p, C, k, lam, s)
        W = sorted({T.rot(p, r, v_) for v_ in V0 for r in range(p)})
        a.update(t=1, V0=V0, per=per, W=W, vnodes=sum(per.values()))
    elif md:
        t, fs = md
        orb, sz, reps, ex = orb_data(p, t)
        W, vnodes = orb_search(p, C, k, lam, s, orb, sz)
        a.update(t=t, fs=fs, orb=orb, sz=sz, reps=reps, ex=ex, W=W, vnodes=vnodes)
    else:
        V0, per = in_search(p, C, k, lam, s)
        W = sorted({T.rot(p, r, v_) for v_ in V0 for r in range(p) if T.m1ok(p, T.rot(p, r, v_))})
        a.update(t=1, V0=V0, per=per, W=W, vnodes=sum(per.values()))
    pts = [g for g in range(p * p) if pt_ok(p, s, W, g)]
    a["pt"] = pts[0] if pts else None
    if a["pt"] is None:
        ws = T.certs(p)
        R = [[T.row_of_w(p, s, d, w) for w in ws[d]] for d in range(p + 1)]
        st = [0]
        a["killed"] = tomo_go(p, s, c, W, R, [], st)
        a.update(ws=ws, R=R, tnodes=st[0])
    else:
        a["killed"] = True
    return a


def lean_args(a):
    p, c, k, lam, s = a["p"], a["c"], a["k"], a["lam"], a["s"]
    C = f"({c} * {p} : ℕ)"
    return (f"(Indexed.size (ZMod {p})) (Indexed.addIdx (ZMod {p})) {C}\n"
            f"    (({k} : ℕ) + ({lam} : ℤ) * ({C} - 1)) (({lam} : ℤ) * {C}) ({k} : ℕ) {s}")


def group_name(ms):
    return " × ".join(f"ZMod {m}" for m in ms)


def write_row(a):
    id_, p, c, k, lam, s, ms = a["id"], a["p"], a["c"], a["k"], a["lam"], a["s"], a["ms"]
    A, P = forms(ms, p)
    out = []
    W = a["W"]
    if a["t"] > 1:
        cong = ", ".join(f"`{q}^{f} ≡ {a['t']}`" for q, e, f in a["fs"])
        lst = (f"`n = k − λ = {a['n']}`: `t = {a['t']}` is a multiplier (C10': {cong} mod {p}),\n"
               f"so the centred line contractions (fibres of {c * p}) are constant on the orbits of\n"
               f"`h ↦ {a['t']} h`; `orbSearch` ({a['vnodes']} nodes) lists the {len(W)} of `w`.")
    elif a["nc"]:
        lst = (f"No centring\n(`not_hasSDS_grp_nc`): each line contraction (fibres of {c * p}) is a rotation of "
               f"one of\nthe {len(a['V0'])} of `v0` (`inSearch`, {a['vnodes']} nodes), one of the {len(W)} of `w`.")
    else:
        lst = (f"Each line contraction (fibres of {c * p}) is a rotation of one of the {len(a['V0'])} of `v0`\n"
               f"(`inSearch`, {a['vnodes']} nodes); after centring, it is one of the {len(W)} of `w`.")
    if a["pt"] is not None:
        g = a["pt"]
        close = (f"No choice of one per line has `Σⱼ yⱼ(lineⱼ g) ≡ s (mod {p})` at `g = {g}`\n"
                 f"(`ptOK`, the reachable residues).")
    else:
        close = (f"`tomoGoL` ({a['tnodes']} nodes) finds no choice of one per line whose line sums\n"
                 f"are `{p} z + s` with `|z| ≤ {c}`.")
    mod = "TomographyQuotNC" if a["nc"] else "TomographyQuot"
    div = f"`{p} ∣ s`" if a["nc"] else f"`{p} ∤ s`"
    out.append(f"""module

public import SignedDifferenceSets.{mod}

/-!
# {id_}: no SDS ({a['v']}, {k}, {lam}) in {' × '.join(f'C{m}' for m in ms)} (I23, tomography on a quotient)

Reduction mod {p} of two factors maps onto `ZMod {p} × ZMod {p}` with fibres of `c = {c}`; `s = {s}`,
{div}. {lst}
{close}
Generated by `solver/tomoquot.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.TomographyQuotRows.{id_}

open Tomography

set_option maxRecDepth 100000
-- one kernel check at a time
set_option Elab.async false

/-- `{p}` is prime. -/
local instance fact : Fact (Nat.Prime {p}) := ⟨by norm_num⟩
""")
    if a["t"] > 1:
        out.append(f"""/-- `orb h`: the orbit of `h` under `h ↦ {a['t']} h`, numbered by smallest elements. -/
def orb : List ℕ :=
  {T.fmt(a['orb'], '  ')}

/-- The orbit sizes. -/
def sz : List ℕ :=
  {T.fmt(a['sz'], '  ')}

/-- The orbits' smallest elements. -/
def rep : List ℕ :=
  {T.fmt(a['reps'], '  ')}

/-- `h ≡ {a['t']} ^ ex h · rep (orb h) (mod {p})`. -/
def ex : List ℕ :=
  {T.fmt(a['ex'], '  ')}

/-- The centred line vectors constant on the orbits. -/
def w : List (List ℤ) :=
  {T.fmt([list(x) for x in W], '  ')}

theorem ho : orbOK {p} {a['t']} orb sz rep ex = true := by decide +kernel

-- {a['vnodes']} nodes
theorem hV : orbSearch {lean_args(a)}
    orb sz w = true := by
  decide +kernel
""")
        lists = "(lists_of_orbSearch hV ho)"
        mult = (f"(Or.inr ⟨{a['n']}, {T.flat([tuple(f) for f in a['fs']])}, by norm_num, by decide +kernel⟩)")
    else:
        vp = T.vparts(a["per"], c * p)
        out.append(f"""/-- The vectors meeting a line contraction's demands, `|w₀|` largest. -/
def v0 : List (List ℤ) :=
  {T.fmt([list(x) for x in a['V0']], '  ')}

/-- Their rotations with `Σ t w(t) ≡ 0 (mod {p})`. -/
def w : List (List ℤ) :=
  {T.fmt([list(x) for x in W], '  ')}
""")
        for i, (lo, mm, nn) in enumerate(vp):
            if nn <= VSPLIT:
                out.append(f"-- {nn} nodes")
                out.append(f"theorem vpart{i} : inPart {lean_args(a)}\n    v0 ({lo}) {mm} = true := by\n"
                           f"  decide +kernel\n")
                continue
            assert mm == 1
            a["split"] = True
            d = 1
            while True:
                pres = in_front(p, c * p, k, lam, s, lo, d)
                sizes = [below_nodes(p, c * p, k, lam, s, q) for q in pres]
                if max(sizes, default=0) <= VSLICE:
                    break
                d += 1
            bs = batch_by(pres, sizes, VSLICE)
            for j, (b, bn) in enumerate(bs):
                out.append(f"/-- Prefixes below `{lo}`, batch {j} ({bn} nodes). -/")
                out.append(f"def pre{i}_{j} : List (List ℤ) :=\n  {T.fmt(b, '  ')}\n")
                out.append(f"theorem below{i}_{j} :\n    (pre{i}_{j}.all fun q => belowIn {lean_args(a)}\n"
                           f"      v0 q) = true := by\n  decide +kernel\n")
            chain, proof = join_mem(f"pre{i}", len(bs), f"below{i}", "q")
            out.append(f"/-- The prefixes {d} levels below `{lo}`. -/\ndef pre{i} : List (List ℤ) :=\n{chain}\n")
            out.append(f"theorem top{i} : inPartTop {lean_args(a)}\n    v0 pre{i} {d} ({lo}) 1 = true := by\n"
                       f"  decide +kernel\n")
            out.append(f"-- {nn} nodes in all\ntheorem vpart{i} : inPart {lean_args(a)}\n    v0 ({lo}) 1 = true :=\n"
                       f"  inPart_of_top (by decide) top{i} fun q hq => by\n" + "\n".join(proof) + "\n")
        out.append(f"theorem hV0 : inSearch {lean_args(a)}\n    v0 = true := by")
        prev = "vpart0"
        for i in range(1, len(vp)):
            out.append(f"  have j{i} := inPart_add' {prev} vpart{i} (by decide)")
            prev = f"j{i}"
        out.append(f"  exact inSearch_of_inPart {prev} (by decide) (by decide)\n")
        if a["nc"]:
            out.append(f"theorem hW : rotAllOK {p} v0 w = true := by decide +kernel\n")
            lists = "(lists_all_of_inSearch hV0 hW)"
        else:
            out.append(f"theorem hW : rotOK {p} v0 w = true := by decide +kernel\n")
            lists = "(lists_of_inSearch hV0 hW 1)"
        mult = "(Or.inl rfl)"
    if a["pt"] is not None:
        out.append(f"theorem hpt : ptOK {p} {s} w {a['pt']} = true := by decide +kernel\n")
        closer = "(closes_of_ptOK (by norm_num) (by norm_num) hpt)"
    else:
        out.append("/-- The certificate: per depth, vectors on the numbers `x = a p + b`. -/")
        out.append("def ws : List (List (List ℤ)) :=")
        out.append("  " + T.fmt([[list(x) for x in wd] for wd in a["ws"]], "  "))
        out.append("")
        out.append("/-- `certRows` of `ws`, stored so that `tomoGoL` reads them. -/")
        out.append("def rows : List (List Tomography.Row) :=")
        out.append("  " + T.fmt([[(list(Ps), t) for Ps, t in rd] for rd in a["R"]], "  "))
        out.append("")
        out.append(f"theorem hc : certOK {p} ws = true := by decide +kernel\n")
        out.append(f"theorem hR : certRows {p} {s} ws = rows := by decide +kernel\n")
        if a["tnodes"] <= TSLICE:
            out.append(f"-- {a['tnodes']} nodes")
            out.append(f"theorem hT : tomoGoL {p} (leafQ {p} {s} {c}) w rows [] = true := by decide +kernel\n")
        else:
            m = 0
            while True:
                m += 1
                Pf = T.front(p, W, a["R"], m)
                sizes = []
                for q in Pf:
                    st = [0]
                    assert tomo_go(p, s, c, W, a["R"][m:], q, st)
                    sizes.append(st[0])
                if max(sizes) <= TSLICE or m == p:
                    break
            bs = batch_by(Pf, sizes, TSLICE)
            leaf = f"(leafQ {p} {s} {c})"
            for j, (b, bn) in enumerate(bs):
                out.append(f"/-- Subtrees, batch {j} ({bn} nodes). -/")
                out.append(f"def batch_{j} : List (List (List ℤ)) :=\n  "
                           f"{T.fmt([[list(y) for y in q] for q in b], '  ')}\n")
                out.append(f"theorem tpart_{j} :\n    (batch_{j}.all fun q => tomoGoL {p} {leaf} w (rows.drop {m}) q) =\n"
                           f"      true := by\n  decide +kernel\n")
            chain, proof = join_mem("batch", len(bs), "tpart", "q", "front")
            out.append(f"/-- The nodes {m} levels down. -/\ndef front : List (List (List ℤ)) :=\n{chain}\n")
            out.append(f"theorem htop : tomoTopL {p} {leaf} w front {m} rows [] = true := by decide +kernel\n")
            out.append(f"-- {a['tnodes']} nodes in all\ntheorem hT : tomoGoL {p} {leaf} w rows [] = true :=\n"
                       f"  tomoGoL_of_top {m} rows [] htop fun q hq => by\n" + "\n".join(proof) + "\n")
        closer = "(closes_of_tomoGoL (by norm_num) hc hR hT)"
    if a["nc"]:
        call = (f"not_hasSDS_grp_nc (ms := {T.flat(ms)}) {p}\n    (A := {T.flat(A)}) (P := {T.flat(P)})\n"
                f"    (by decide) (by decide) _ (c := {c}) (by decide) (by norm_num)")
    else:
        call = (f"not_hasSDS_grp (ms := {T.flat(ms)}) {p}\n    (A := {T.flat(A)}) (P := {T.flat(P)})\n"
                f"    (by decide) (by decide) _ (c := {c}) (by decide) (by norm_num) (by decide) "
                f"(t := {a['t']})\n    {mult}")
    out.append(f"""/-- {id_}: `{group_name(ms)}` has no signed difference set
with parameters ({a['v']}, {k}, {lam}). -/
theorem not_hasSDS : ¬ HasSDS ({group_name(ms)}) {k} {lam} :=
  {call}
    {lists}
    {closer}

end SignedDifferenceSets.TomographyQuotRows.{id_}
""")
    os.makedirs(DIR, exist_ok=True)
    path = f"{DIR}/{id_}.lean"
    text = "\n".join(out)
    if a.get("split"):
        first = f"public import SignedDifferenceSets.{mod}\n"
        text = text.replace(first, first + "public import SignedDifferenceSets.TomographySplit\n", 1)
    open(path, "w", encoding="utf-8", newline="\n").write(text)
    for i, l in enumerate(open(path, encoding="utf-8").read().split("\n"), 1):
        assert len(l) <= 100, (path, i, len(l))
    return path

TEST = "lean/SignedDifferenceSets/Tests/TomographyQuot.lean"


def write_tests():
    """Controls not killed (N352 on C7 x C7, N31832 through C7^3 -> C7 x C7, both orbit lists; N49 by inSearch)
    and broken inputs refused (a list missing a vector, wrong orbit data, a wrong multiplier factor)."""
    a, b, d, e = analyse("N352"), analyse("N31832"), analyse("N49"), analyse("N5027")
    assert not a["killed"] and not b["killed"] and not d["killed"] and a["pt"] is None and b["pt"] is None
    assert d["pt"] is None
    out = ["""module

public import SignedDifferenceSets.TomographyQuot

/-!
# Tests: line tomography on a quotient (I23)

The checks must not kill an `exists` row: N352 (49, 33, 1) on C₇ × C₇ (`c = 1`) and N31832
(343, 172, 84) through C₇³ → C₇ × C₇ (`c = 7`), both with the multiplier `t = 2` (orbit lists,
complete by `orbSearch`): `ptOK` at the origin and `tomoGoL` find a choice. N49 (25, 12, 1) on
C₅ × C₅ through `inSearch`: likewise. Broken inputs are refused: a list missing a vector, orbit
data with a wrong exponent, a multiplier factorization with a wrong power. Generated by
`solver/tomoquot.py --tests`.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.TomographyQuot

open SignedDifferenceSets.Tomography

set_option maxRecDepth 100000
"""]
    for x, name in ((a, "N352"), (b, "N31832")):
        p, c, s = x["p"], x["c"], x["s"]
        out.append(f"""/-- {name}'s orbits of `h ↦ {x['t']} h`, sizes, smallest elements, exponents. -/
def orb{name} : List ℕ := {T.flat(x['orb'])}
def sz{name} : List ℕ := {T.flat(x['sz'])}
def rep{name} : List ℕ := {T.flat(x['reps'])}
def ex{name} : List ℕ := {T.flat(x['ex'])}

/-- {name}'s centred line vectors constant on the orbits. -/
def w{name} : List (List ℤ) :=
  {T.fmt([list(y) for y in x['W']], '  ')}

example : orbOK {p} {x['t']} orb{name} sz{name} rep{name} ex{name} = true := by decide +kernel

example : orbSearch {lean_args(x)}
    orb{name} sz{name} w{name} = true := by
  decide +kernel

/-- {name} exists: the origin does not rule it out. -/
example : ptOK {p} {s} w{name} 0 = false := by decide +kernel

/-- The certificate's rows for `p = {p}`, `s = {s}`. -/
def rows{name} : List (List Tomography.Row) :=
  {T.fmt([[(list(Ps), t_) for Ps, t_ in rd] for rd in x['R']], '  ')}

/-- {name} exists: `tomoGoL` finds a choice. -/
example : tomoGoL {p} (leafQ {p} {s} {c}) w{name} rows{name} [] = false := by decide +kernel
""")
    out.append(f"""/-- N49's vectors with `|w₀|` largest, and their centred rotations. -/
def v0N49 : List (List ℤ) :=
  {T.fmt([list(y) for y in d['V0']], '  ')}

def wN49 : List (List ℤ) :=
  {T.fmt([list(y) for y in d['W']], '  ')}

example : inSearch {lean_args(d)}
    v0N49 = true := by
  decide +kernel

example : rotOK 5 v0N49 wN49 = true := by decide +kernel

/-- The certificate's rows for `p = 5`, `s = 6`. -/
def rowsN49 : List (List Tomography.Row) :=
  {T.fmt([[(list(Ps), t_) for Ps, t_ in rd] for rd in d['R']], '  ')}

/-- N49 exists: `tomoGoL` finds a choice. -/
example : tomoGoL 5 (leafQ 5 6 1) wN49 rowsN49 [] = false := by decide +kernel

/-- A list missing a vector is refused (N5027). -/
example : orbSearch {lean_args(e)}
    {T.flat(e['orb'])} {T.flat(e['sz'])} {T.fmt([list(y) for y in e['W'][1:]], '    ')} = false := by
  decide +kernel

/-- Orbit data with a wrong exponent is refused. -/
example : orbOK 7 2 {T.flat(e['orb'])} {T.flat(e['sz'])} {T.flat(e['reps'])}
    {T.flat([e['ex'][0], e['ex'][1] + 1] + e['ex'][2:])} = false := by
  decide +kernel

/-- A factor whose power is not `t` is refused: `79² ≢ 2 (mod 7)`. -/
example : ¬ MultOK 7 2 79 [(79, 1, 2)] := by decide +kernel

example : MultOK 7 2 79 [(79, 1, 1)] := by decide +kernel

end SignedDifferenceSets.Tests.TomographyQuot
""")
    open(TEST, "w", encoding="utf-8", newline="\n").write("\n".join(out))
    for i, l in enumerate(open(TEST, encoding="utf-8").read().split("\n"), 1):
        assert len(l) <= 100, (TEST, i, len(l))
    print("wrote", TEST)


def main():
    if "--tests" in sys.argv:
        write_tests()
        return
    test = "--test" in sys.argv
    for arg in [x for x in sys.argv[1:] if not x.startswith("--")]:
        id_, _, p = arg.partition(":")
        a = analyse(id_, int(p) if p else None)
        print(id_, (a["v"], a["k"], a["lam"]), a["ms"], "p", a["p"], "c", a["c"], "s", a["s"], "t", a["t"],
              "|W|", len(a["W"]), "vnodes", a["vnodes"], "pt", a["pt"], "tnodes", a.get("tnodes"),
              "KILLED" if a["killed"] else "FOUND", flush=True)
        if not test and a["killed"]:
            print("  wrote", write_row(a), flush=True)


if __name__ == "__main__":
    main()
