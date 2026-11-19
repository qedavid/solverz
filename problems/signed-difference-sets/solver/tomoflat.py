"""I23 on a quotient Z_p^r (r >= 3): hyperplane tomography rows, the Lean files (TomographyFlat.not_hasSDS_flat).

tomoflat.py <id>:<p>:<r> [...] [--test] [--search]: for each row of instances.csv whose group has p-rank >= r and
p not dividing s, with fibres c = v / p^r: phi = reduction mod p of r factors divisible by p (forms A); the
hyperplane contractions (fibres C = v / p) meet C3's demands, so after centring each is one of W (inSearch with
fibres C, rotOK; tomoquot.py's lists). The certificate: the (p^r - 1)/(p - 1) normalized hyperplanes fs (unit
vectors first), the leaf flat (all of fs, alpha = (p^(r-1) - 1)/(p - 1), kappa = 1) and check points: the origin
alone (the default; every row whose root fails) or, with --search, every point of (Z_p)^r with the leaf's absolute
sum over all of them. Mirrors certOK, boundsOK and flatKill exactly (node counts) and writes
lean/SignedDifferenceSets/TomographyFlatRows/N<id>.lean when the kill passes. --test: verdicts and counts only.
tomorows.py and tomoquot.py are imported, not changed.
"""
import itertools
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tomorows as T  # noqa: E402
import tomoquot as TQ  # noqa: E402

DIR = "lean/SignedDifferenceSets/TomographyFlatRows"
WSLICE = int(os.environ.get("WSLICE", 40000))   # flatGo nodes times check points per kernel check


# ---------- mirrors of TomographyFlat's definitions ----------

def all_pts(ds):
    if not ds:
        return [[]]
    if len(ds) == 1:
        return [[a] for a in range(ds[0])]
    return [[a] + xs for a in range(ds[0]) for xs in all_pts(ds[1:])]


def dot_l(ds, f, xs):
    """dotL: sum over the factors of ds, missing coefficients and coordinates 0."""
    return sum((f[i] if i < len(f) else 0) * (xs[i] if i < len(xs) else 0) for i in range(len(ds)))


def members(fs, mem):
    return [f for f, b in zip(fs, mem) if b]


def zero_count(p, ds, hs, xs):
    return sum(1 for f in hs if dot_l(ds, f, xs) % p == 0)


def inc_ok(p, ds, fs, F):
    mem, alpha, kappa = F
    hs = members(fs, mem)
    N = len(hs)
    pts = all_pts(ds)
    return (alpha < N and all(zero_count(p, ds, hs, xs) in (N, alpha) for xs in pts)
            and sum(1 for xs in pts if zero_count(p, ds, hs, xs) == N) <= kappa)


def get_flat(flats, i):
    return flats[i] if i < len(flats) else ([], 0, 0)


def ix_of(p, ds, flats, d, f, q):
    mem = get_flat(flats, q[0])[0]
    return dot_l(ds, f, q[1]) % p if (d < len(mem) and mem[d]) else p


def cs_of(s, c, fs, flats, q):
    mem, alpha, kappa = get_flat(flats, q[0])
    g = max(len(members(fs, mem)) - alpha, 0)
    return (alpha * s, g, g * c * kappa)


def sep_ok(p, ds, hs, xss):
    for i, x in enumerate(xss):
        for x2 in xss[i + 1:]:
            if not any(dot_l(ds, f, x) % p != dot_l(ds, f, x2) % p for f in hs):
                return False
    return True


def len_ok(J, lv):
    return all(len(l[0]) == J and len(l[1]) == J and len(l[2]) == J for l in lv)


def cert_ok(p, ds, s, c, fs, flats, cps, cs, lv, L, H, m):
    J = len(cps)
    q0 = cps[0] if cps else (0, [])
    return (len(lv) == len(fs)
            and all(any(dot_l(ds, f, xs) % p == 1 for xs in all_pts(ds)) for f in fs)
            and all(inc_ok(p, ds, fs, F) for F in flats)
            and all(q[0] < len(flats) for q in cps)
            and cs == [cs_of(s, c, fs, flats, q) for q in cps]
            and len(L) == J and len(H) == J and len_ok(J, lv)
            and all(lv[d][0] == [ix_of(p, ds, flats, d, fs[d], q) for q in cps] for d in range(len(fs)))
            and m <= J
            and all(q[0] == q0[0] for q in cps[:m])
            and sep_ok(p, ds, members(fs, get_flat(flats, q0[0])[0]), [q[1] for q in cps[:m]]))


def getd(y, i):
    return y[i] if 0 <= i < len(y) else 0


def ok_one(t, l, h, c):
    ctr, g, w = c
    a = max(t + l - ctr, -w)
    b = min(t + h - ctr, w)
    return a <= g * (b // g) if g != 0 else a <= 0


def ok_all(P, L, H, cs):
    return all(ok_one(t, l, h, c) for t, l, h, c in zip(P, L, H, cs))


def add_vec(P, ix, y):
    return [t + getd(y, i) for t, i in zip(P, ix)]


def abs_sum_of(m, P, cs):
    return sum(abs((t - c[0]) // c[1]) if c[1] != 0 else 0 for t, c in list(zip(P, cs))[:m])


def opts_at(U, W, u):
    return W if u == 0 else U


def step_ok(L, H, L2, H2, ix, y):
    return all(l <= l2 + getd(y, i) and h2 + getd(y, i) <= h for l, h, l2, h2, i in zip(L, H, L2, H2, ix))


def bounds_ok(U, W, u, lv, L, H):
    for ix, L2, H2 in lv:
        if not all(step_ok(L, H, L2, H2, ix, y) for y in opts_at(U, W, u)):
            return False
        L, H, u = L2, H2, max(u - 1, 0)
    return all(x <= 0 for x in L) and all(x >= 0 for x in H)


def flat_go(k, m, cs, U, W, u, lv, P, st):
    """Mirror of flatGo; True when no path survives. st[0] counts the option evaluations."""
    if not lv:
        return not abs_sum_of(m, P, cs) <= k
    ix, L, H = lv[0]
    for y in opts_at(U, W, u):
        st[0] += 1
        P2 = add_vec(P, ix, y)
        if ok_all(P2, L, H, cs) and not flat_go(k, m, cs, U, W, max(u - 1, 0), lv[1:], P2, st):
            return False
    return True


def flat_kill(k, m, cs, U, W, u, L, H, lv, st):
    P0 = [0] * len(cs)
    if not ok_all(P0, L, H, cs):
        return True
    return flat_go(k, m, cs, U, W, u, lv, P0, st)


# ---------- the certificate ----------

def unit_l(j):
    """unitL j: j zeros, then 1."""
    return [0] * j + [1]


def hyperplanes(p, r):
    """Normalized nonzero coefficient vectors of (Z_p)^r: the r coordinates first (as unitL j), then in order."""
    units = [[int(i == j) for i in range(r)] for j in range(r)]
    rest = [list(f) for f in itertools.product(range(p), repeat=r)
            if any(f) and f[next(i for i in range(r) if f[i])] == 1 and list(f) not in units]
    return [unit_l(j) for j in range(r)] + rest


def bounds(lv_ix, U, W, u, J):
    n = len(lv_ix)
    lo = [[0] * J for _ in range(n + 1)]
    hi = [[0] * J for _ in range(n + 1)]
    for d in range(n - 1, -1, -1):
        opts = opts_at(U, W, max(u - d, 0))
        for j in range(J):
            vals = [getd(y, lv_ix[d][j]) for y in opts]
            lo[d][j] = lo[d + 1][j] + min(vals)
            hi[d][j] = hi[d + 1][j] + max(vals)
    return lo, hi


def forms(ms, p, r):
    idx = [i for i, m in enumerate(ms) if m % p == 0][:r]
    assert len(idx) == r, (ms, p, r)
    A = [[1 if i == j else 0 for i in range(len(ms))] for j in idx]
    return A, [list(a) for a in A]


def analyse(id_, p, r, search=False):
    v, k, lam, ms, status = TQ.row_of(id_)
    return build(id_, p, r, v, k, lam, ms, status, search)


def build(id_, p, r, v, k, lam, ms, status, search=False, kill=True):
    s2 = k + lam * (v - 1)
    s = math.isqrt(s2)
    assert s * s == s2, (id_, s2)
    c, C = v // p ** r, v // p
    assert c * p ** r == v
    nc = s % p == 0
    a = dict(id=id_, v=v, k=k, lam=lam, ms=ms, p=p, r=r, c=c, C=C, s=s, status=status, nc=nc)
    V0, per = TQ.in_search(p, C, k, lam, s)
    if nc:
        W = sorted({T.rot(p, rr, v_) for v_ in V0 for rr in range(p)})
        U, u = [list(y) for y in V0], r
    else:
        W = sorted({T.rot(p, rr, v_) for v_ in V0 for rr in range(p) if T.m1ok(p, T.rot(p, rr, v_))})
        U, u = None, 0
    W = [list(y) for y in W]
    U = U if U is not None else W
    a.update(V0=V0, per=per, W=W, U=U, u=u, vnodes=sum(per.values()))
    ds = [p] * r
    fs = hyperplanes(p, r)
    n = len(fs)
    alpha = (p ** (r - 1) - 1) // (p - 1)
    flats = [([True] * n, alpha, 1)]
    if search:
        cps = [(0, xs) for xs in all_pts(ds)]
        m = len(cps)
    else:
        cps = [(0, [0] * r)]
        m = 0
    J = len(cps)
    cs = [cs_of(s, c, fs, flats, q) for q in cps]
    ixs = [[ix_of(p, ds, flats, d, fs[d], q) for q in cps] for d in range(n)]
    lo, hi = bounds(ixs, U, W, u, J)
    lv = [(ixs[d], lo[d + 1], hi[d + 1]) for d in range(n)]
    L0, H0 = lo[0], hi[0]
    assert cert_ok(p, ds, s, c, fs, flats, cps, cs, lv, L0, H0, m)
    assert bounds_ok(U, W, u, lv, L0, H0)
    st = [0]
    sys.setrecursionlimit(10000)
    killed = flat_kill(k, m, cs, U, W, u, L0, H0, lv, st) if kill else None
    a.update(ds=ds, fs=fs, flats=flats, cps=cps, cs=cs, lv=lv, L0=L0, H0=H0, m=m, killed=killed,
             gnodes=st[0], root=not ok_all([0] * J, L0, H0, cs), alpha=alpha, A=forms(ms, p, r))
    return a


def norm_f(f, p):
    i = next(j for j in range(len(f)) if f[j])
    inv = pow(f[i], p - 2, p)
    return tuple(x * inv % p for x in f)


def subspaces(p, r, d):
    """The d-dim subspaces of the dual (Z_p)^r, as frozensets of normalized padded hyperplanes."""
    H = [tuple(f + [0] * (r - len(f))) for f in hyperplanes(p, r)]
    out = set()
    for basis in itertools.combinations(H, d):
        mem = set()
        for cs in itertools.product(range(p), repeat=d):
            if any(cs):
                f = tuple(sum(c * b[t] for c, b in zip(cs, basis)) % p for t in range(r))
                if any(f):
                    mem.add(norm_f(f, p))
        if len(mem) == (p ** d - 1) // (p - 1):
            out.add(frozenset(mem))
    return sorted(out, key=sorted)


def sub_cert(a, dims):
    """Replace the certificate by one with check points on sub-flats of the dims (each at one point per class) and
    every point of the leaf, the hyperplanes ordered flat-first (coordinates first); keep only the check points that
    prune in the mirror search (a second search confirms the kill with them), m = 0."""
    p, r, k, s, c = a["p"], a["r"], a["k"], a["s"], a["c"]
    ds = a["ds"]
    pts = all_pts(ds)
    pad = lambda f: tuple(f + [0] * (r - len(f)))  # noqa: E731
    H = [pad(f) for f in hyperplanes(p, r)]
    n = len(H)
    subs = {d: subspaces(p, r, d) for d in dims}
    order = list(H[:r])
    done = set(order)
    while len(order) < n:
        best = min(subs[min(dims)], key=lambda S: (len(S - done) if S - done else 99, sorted(S)))
        for b in sorted(best - done):
            order.append(b)
            done.add(b)
    units = {pad(unit_l(j)): unit_l(j) for j in range(r)}
    fs = [units.get(h, list(h)) for h in order]
    flats = [([True] * n, a["alpha"], 1)]
    cps = [(0, xs) for xs in pts]
    for d in dims:
        a_d = (p ** (d - 1) - 1) // (p - 1)
        for S in subs[d]:
            mem = [pad(f) in S for f in fs]
            hs = members(fs, mem)
            kappa = sum(1 for xs in pts if zero_count(p, ds, hs, xs) == len(hs))
            flats.append((mem, a_d, kappa))
            seen = {}
            for xs in pts:
                seen.setdefault(tuple(dot_l(ds, f, xs) % p for f in hs), xs)
            cps += [(len(flats) - 1, xs) for xs in seen.values()]

    def make(cps_):
        cs_ = [cs_of(s, c, fs, flats, q) for q in cps_]
        ixs = [[ix_of(p, ds, flats, d, fs[d], q) for q in cps_] for d in range(n)]
        lo, hi = bounds(ixs, a["U"], a["W"], a["u"], len(cps_))
        return cs_, [(ixs[d], lo[d + 1], hi[d + 1]) for d in range(n)], lo[0], hi[0]

    def prune_run(cps_):
        cs_, lv_, L0_, H0_ = make(cps_)
        pr, st = set(), [0]
        sys.setrecursionlimit(10000)

        def go(u, d, P):
            if d == n:
                return False
            ix, L, H = lv_[d]
            for y in opts_at(a["U"], a["W"], u):
                st[0] += 1
                P2 = add_vec(P, ix, y)
                bad = next((j for j in range(len(cps_)) if not ok_one(P2[j], L[j], H[j], cs_[j])), None)
                if bad is None:
                    if not go(max(u - 1, 0), d + 1, P2):
                        return False
                else:
                    pr.add(bad)
            return True
        root = next((j for j in range(len(cps_)) if not ok_one(0, L0_[j], H0_[j], cs_[j])), None)
        if root is not None:
            return True, {root}, st[0]
        return go(a["u"], 0, [0] * len(cps_)), pr, st[0]
    killed, pr, nodes = prune_run(cps)
    assert killed, "not killed with every check point"
    cps = [cps[j] for j in sorted(pr)]
    # drop the flats no check point uses, renumbering
    used = sorted({q[0] for q in cps})
    ren = {f: i for i, f in enumerate(used)}
    flats = [flats[f] for f in used]
    cps = [(ren[q[0]], q[1]) for q in cps]
    cs, lv, L0, H0 = make(cps)
    assert cert_ok(p, ds, s, c, fs, flats, cps, cs, lv, L0, H0, 0)
    assert bounds_ok(a["U"], a["W"], a["u"], lv, L0, H0)
    st = [0]
    killed = flat_kill(k, 0, cs, a["U"], a["W"], a["u"], L0, H0, lv, st)
    a.update(fs=fs, flats=flats, cps=cps, cs=cs, lv=lv, L0=L0, H0=H0, m=0, killed=killed, gnodes=st[0],
             root=not ok_all([0] * len(cps), L0, H0, cs), dims=dims)
    return a


def subtree_nodes(a, d, u, P):
    st = [0]
    assert flat_go(a["k"], a["m"], a["cs"], a["U"], a["W"], u, a["lv"][d:], P, st)
    return st[0]


def front_at(a, d):
    """The node sums d levels down that pass every node check (mirror of flatTop)."""
    out = []

    def rec(dd, u, P):
        if dd == d:
            out.append(P)
            return
        ix, L, H = a["lv"][dd]
        for y in opts_at(a["U"], a["W"], u):
            P2 = add_vec(P, ix, y)
            if ok_all(P2, L, H, a["cs"]):
                rec(dd + 1, max(u - 1, 0), P2)
    rec(0, a["u"], [0] * len(a["cps"]))
    return out


def split_front(a):
    """The smallest depth whose subtrees each fit WSLICE; the front and its subtree sizes."""
    J = len(a["cps"])
    for d in range(1, len(a["lv"])):
        F = front_at(a, d)
        u = max(a["u"] - d, 0)
        sizes = [subtree_nodes(a, d, u, P) for P in F]
        if max(sizes, default=0) * J <= WSLICE:
            return d, F, sizes
    raise ValueError("no split depth")


# ---------- Lean text ----------

def lflat(obj):
    if isinstance(obj, bool):
        return "true" if obj else "false"
    if isinstance(obj, tuple):
        return "(" + ", ".join(lflat(x) for x in obj) + ")"
    if isinstance(obj, list):
        return "[" + ", ".join(lflat(x) for x in obj) + "]"
    return str(obj)


def lfmt(obj, ind, width=98):
    one = lflat(obj)
    if len(ind) + len(one) <= width:
        return one
    if isinstance(obj, tuple):
        return "(" + (",\n" + ind + " ").join(lfmt(x, ind + " ", width) for x in obj) + ")"
    if all(not isinstance(x, (list, tuple)) for x in obj):
        return "[\n" + T.wrap([lflat(x) for x in obj], ind + "  ", width) + "]"
    return "[\n" + ",\n".join(ind + "  " + lfmt(x, ind + "  ", width) for x in obj) + "]"


def lean_args(a):
    p, C, k, lam, s = a["p"], a["C"], a["k"], a["lam"], a["s"]
    return (f"(Indexed.size (ZMod {p})) (Indexed.addIdx (ZMod {p})) ({C} : ℕ)\n"
            f"    (({k} : ℕ) + ({lam} : ℤ) * (({C} : ℕ) - 1)) (({lam} : ℤ) * ({C} : ℕ)) ({k} : ℕ) {s}")


def group_name(ms):
    return " × ".join(f"ZMod {m}" for m in ms)


def write_row(a):
    id_, p, r, c, C, k, lam, s, ms = (a[x] for x in ("id", "p", "r", "c", "C", "k", "lam", "s", "ms"))
    A, P = a["A"]
    W, n = a["W"], len(a["fs"])
    out = []
    if a["m"] == 0:
        y0 = sorted({y[0] for y in W})
        tot = a["L0"][0] if a["L0"][0] == a["H0"][0] else None
        if tot is not None:
            close = (f"All of them have `w(0) = {y0[0]}`, so at the origin the {n} hyperplanes give "
                     f"`{tot}`;\n`{p ** (r - 1)} Y(0) = {tot} − {a['alpha']}·{s} = {tot - a['alpha'] * s}` "
                     f"is not `{p ** (r - 1)} z` with `|z| ≤ {c}`: the root fails\n(`flatKill`).")
        else:
            close = ("At the origin the reachable sums of the hyperplanes' `w(0)` miss every\n"
                     f"`{a['alpha']} s + {p ** (r - 1)} z` with `|z| ≤ {c}`: the root fails (`flatKill`).")
    else:
        close = (f"`flatKill` ({a['gnodes']} nodes) chooses one per hyperplane, checks every point of "
                 f"`(ZMod {p})^{r}`\n(`{p ** (r - 1)} Y(x) = Σ_f y_f(f x) − {a['alpha']} s`, `|Y| ≤ {c}`) "
                 f"and at a leaf `Σ |Y| ≤ {k}`; none passes.")
    if a.get("dims") and not a["root"]:
        nf = len(a["flats"])
        close = (f"`flatKill` ({a['gnodes']} nodes) chooses one per hyperplane (flat by flat) and checks "
                 f"{len(a['cps'])} points\nof {nf} flats of dimension {', '.join(map(str, a['dims']))} or "
                 f"{r} (`p^(d−1) Y_S = Σ_(f ∈ S) y_f − α_d s`, `|Y_S| ≤ c p^(r−d)`);\nnone passes. "
                 f"Split below {split_front(a)[0]} levels (`flatKill_of_top`).")
    if a["nc"]:
        lists = (f"`{p} ∣ s`.\nNo centring (`not_hasSDS_flat_nc`): each hyperplane contraction (fibres of {C}) "
                 f"is a rotation\nof one of the {len(a['V0'])} of `v0` (`inSearch`, {a['vnodes']} nodes), one of "
                 f"the {len(W)} of `w`; a translate\nputs the largest entry of the {r} coordinate hyperplanes' "
                 f"at `0`, so these are in `v0`.")
    else:
        lists = (f"`{p} ∤ s`.\nEach centred hyperplane contraction (fibres of {C}) is a rotation of one of the "
                 f"{len(a['V0'])} of `v0`\n(`inSearch`, {a['vnodes']} nodes); after centring, it is one of the "
                 f"{len(W)} of `w`.")
    mod = "TomographyFlat"
    out.append(f"""module

public import SignedDifferenceSets.{mod}

/-!
# {id_}: no SDS ({a['v']}, {k}, {lam}) in {' × '.join(f'C{m}' for m in ms)} (I23, hyperplane tomography)

Reduction mod {p} of {r} factors maps onto `(ZMod {p})^{r}` with fibres of `c = {c}`; `s = {s}`, {lists}
{close}
Generated by `solver/tomoflat.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.TomographyFlatRows.{id_}

open Tomography TomographyFlat

set_option maxRecDepth 100000
-- one kernel check at a time
set_option Elab.async false

/-- `{p}` is prime. -/
local instance fact : Fact (Nat.Prime {p}) := ⟨by norm_num⟩

/-- The vectors meeting a hyperplane contraction's demands, `|w₀|` largest. -/
def v0 : List (List ℤ) :=
  {lfmt([list(x) for x in a['V0']], '  ')}

/-- {"All their rotations." if a["nc"] else f"Their rotations with `Σ t w(t) ≡ 0 (mod {p})`."} -/
def w : List (List ℤ) :=
  {lfmt(W, '  ')}
""")
    vp = T.vparts(a["per"], C)
    for i, (lo, mm, nn) in enumerate(vp):
        assert nn <= TQ.VSPLIT, "inSearch split not supported here"
        out.append(f"-- {nn} nodes")
        out.append(f"theorem vpart{i} : inPart {lean_args(a)}\n    v0 ({lo}) {mm} = true := by\n"
                   f"  decide +kernel\n")
    out.append(f"theorem hV0 : inSearch {lean_args(a)}\n    v0 = true := by")
    prev = "vpart0"
    for i in range(1, len(vp)):
        out.append(f"  have j{i} := inPart_add' {prev} vpart{i} (by decide)")
        prev = f"j{i}"
    out.append(f"  exact inSearch_of_inPart {prev} (by decide) (by decide)\n")
    out.append(f"theorem hW : {'rotAllOK' if a['nc'] else 'rotOK'} {p} v0 w = true := by decide +kernel\n")
    uw = f"v0 w {r}" if a["nc"] else "w w 0"
    out.append(f"""/-- The hyperplanes of `(ZMod {p})^{r}` (coefficients, first nonzero `1`), coordinates first. -/
def fs : List (List ℕ) :=
  {lfmt(a['fs'], '  ')}

/-- The leaf flat: every hyperplane, `α = {a['alpha']}`, kernel `{{0}}`. -/
def flats : List Flat :=
  {lfmt(a['flats'], '  ')}

/-- The check points: (flat, coordinates). -/
def cps : List (ℕ × List ℕ) :=
  {lfmt(a['cps'], '  ')}

/-- Per check point `(α s, N − α, (N − α) c κ)`. -/
def cs : List (ℤ × ℤ × ℤ) :=
  {lfmt(a['cs'], '  ')}

/-- The bounds before the first depth. -/
def lo0 : List ℤ :=
  {lfmt(a['L0'], '  ')}

def hi0 : List ℤ :=
  {lfmt(a['H0'], '  ')}

/-- Per depth: the check points' indices, then the bounds after it. -/
def lv : List Level :=
  {lfmt(a['lv'], '  ')}

theorem hcert : certOK {p} {lflat(a['ds'])} {s} {c} fs flats cps cs lv lo0 hi0 {a['m']} = true := by
  decide +kernel

theorem hb : boundsOK {uw} lv lo0 hi0 = true := by decide +kernel
""")
    if a["root"] or a["gnodes"] * len(a["cps"]) <= WSLICE:
        out.append(f"-- {a['gnodes']} nodes")
        out.append(f"theorem hkill : flatKill {k} {a['m']} cs {uw} lo0 hi0 lv = true := by\n"
                   f"  decide +kernel\n")
    else:
        d, F, sizes = split_front(a)
        bs = TQ.batch_by(F, [z * len(a["cps"]) for z in sizes], WSLICE)
        for j, (b, bn) in enumerate(bs):
            out.append(f"/-- Nodes {d} levels down, batch {j} ({bn // len(a['cps'])} nodes). -/")
            out.append(f"def batch_{j} : List (List ℤ) :=\n  {lfmt(b, '  ')}\n")
            out.append(f"theorem part_{j} :\n    (batch_{j}.all fun P => flatGo {k} {a['m']} cs {uw.rsplit(' ', 1)[0]} "
                       f"({a['u']} - {d}) (lv.drop {d}) P) = true := by\n  decide +kernel\n")
        chain, proof = TQ.join_mem("batch", len(bs), "part", "P'", "front")
        out.append(f"/-- The nodes {d} levels down. -/\ndef front : List (List ℤ) :=\n{chain}\n")
        out.append(f"theorem htop : flatTop {k} {a['m']} cs {uw.rsplit(' ', 1)[0]} front {d} {a['u']} lv\n"
                   f"    (List.replicate cs.length 0) = true := by\n  decide +kernel\n")
        proof = [ln.replace("hq", "hP'") for ln in proof]
        out.append(f"-- {a['gnodes']} nodes in all\ntheorem hkill : flatKill {k} {a['m']} cs {uw} lo0 hi0 lv = true :=\n"
                   f"  flatKill_of_top htop fun P' hP' => by\n" + "\n".join(proof) + "\n")
        out[0] = out[0].replace("public import SignedDifferenceSets.TomographyFlat\n",
                                "public import SignedDifferenceSets.TomographyFlatSplit\n", 1)
    sname = group_name(ms)
    if a["nc"]:
        out[0] = out[0].replace("public import SignedDifferenceSets.TomographyFlat",
                                "public import SignedDifferenceSets.TomographyQuotNC\npublic import "
                                "SignedDifferenceSets.TomographyFlat", 1)
        call = (f"not_hasSDS_flat_nc (ms := {lflat(ms)}) (ds := {lflat(a['ds'])}) (p := {p}) (by decide)\n"
                f"    (A := {lfmt(A, '      ')})\n    (P := {lfmt(P, '      ')})\n"
                f"    (by decide) (by decide) _ (c := {c}) (C := {C}) (by decide) (by decide) (by decide)\n"
                f"    (fun b hb hs hmax => mem_of_inSearch (H := ZMod {p}) hV0 hb hmax hs)\n"
                f"    (lists_all_of_inSearch hV0 hW) (r := {r}) (by decide) (by decide)")
    else:
        call = (f"not_hasSDS_flat (ms := {lflat(ms)}) (ds := {lflat(a['ds'])}) (p := {p}) (by decide)\n"
                f"    (A := {lfmt(A, '      ')})\n    (P := {lfmt(P, '      ')})\n"
                f"    (by decide) (by decide) _ (c := {c}) (C := {C}) (by decide) (by decide) (by decide)\n"
                f"    (by decide)\n"
                f"    (fun b hb hs hm => lists_of_inSearch hV0 hW 1 b hb hs hm fun _ => by simp)")
    out.append(f"""/-- {id_}: `{sname}` has no signed difference set
with parameters ({a['v']}, {k}, {lam}). -/
theorem not_hasSDS : ¬ HasSDS ({sname}) {k} {lam} :=
  {call}
    hcert hb hkill

end SignedDifferenceSets.TomographyFlatRows.{id_}
""")
    os.makedirs(DIR, exist_ok=True)
    path = f"{DIR}/{id_}.lean"
    text = "\n".join(out)
    open(path, "w", encoding="utf-8", newline="\n").write(text)
    for i, l in enumerate(text.split("\n"), 1):
        assert len(l) <= 100, (path, i, len(l), l)
    return path


TEST = "lean/SignedDifferenceSets/Tests/TomographyFlat.lean"


def cert_defs(a, tag):
    """Lean defs of a certificate's data, names suffixed by tag."""
    out = []
    for name, typ, val in (("v0", "List (List ℤ)", [list(x) for x in a["V0"]]), ("w", "List (List ℤ)", a["W"]),
                           ("fs", "List (List ℕ)", a["fs"]), ("flats", "List Flat", a["flats"]),
                           ("cps", "List (ℕ × List ℕ)", a["cps"]), ("cs", "List (ℤ × ℤ × ℤ)", a["cs"]),
                           ("lo0", "List ℤ", a["L0"]), ("hi0", "List ℤ", a["H0"]), ("lv", "List Level", a["lv"])):
        out.append(f"def {name}{tag} : {typ} :=\n  {lfmt(val, '  ')}\n")
    return "\n".join(out)


def uw_of(a, tag):
    return f"v0{tag} w{tag} {a['r']}" if a["nc"] else f"w{tag} w{tag} 0"


def write_tests():
    """Exists rows not killed (the five with a Z_3^3 quotient, no centring: N73 by the full search, N61, N67, N448,
    N463 by the origin; N31832 on Z_7^3, centred, by the origin), and broken certificates refused."""
    exists = [("N73", True), ("N61", False), ("N67", False), ("N448", False), ("N463", False)]
    rows = []
    for id_, search in exists:
        a = analyse(id_, 3, 3, search)
        assert a["killed"] is False and a["nc"], id_
        rows.append((id_, a))
    b = analyse("N1252", 3, 3, False)
    assert b["killed"] and not b["nc"]
    out = ["""module

public import SignedDifferenceSets.TomographyFlat
public import SignedDifferenceSets.TomographyQuotNC

/-!
# Tests: hyperplane tomography on a quotient (I23)

The checks must not kill an `exists` row: the five with a `(ZMod 3)^3` quotient, all with `3 ∣ s`
(no centring, the coordinate hyperplanes normalized by translation): N73 (27, 17, 8) with every
point of `(ZMod 3)^3` checked and the leaf's absolute sum, N61 (27, 10, 1), N67 (27, 14, 5),
N448 (54, 38, 2) on C₃ × C₃ × C₆ and N463 (54, 46, 10) with the origin: each certificate passes
`certOK` and `boundsOK`, and `flatKill` finds a choice. Broken inputs are refused (N1252's
certificate): a wrong `α`, a wrong target, a bound off by one, a wrong index, a list missing a
vector, members that are not a flat, a repeated point in the absolute-sum group. Generated by
`solver/tomoflat.py --tests`.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.TomographyFlat

open SignedDifferenceSets.Tomography SignedDifferenceSets.TomographyFlat

set_option maxRecDepth 100000
"""]
    for id_, a in rows:
        tag = id_
        out.append(f"/-! ### {id_} ({a['v']}, {a['k']}, {a['lam']}) on {group_name(a['ms'])}, "
                   f"{'every point' if a['m'] else 'the origin'} -/\n")
        out.append(cert_defs(a, tag))
        out.append(f"example : rotAllOK 3 v0{tag} w{tag} = true := by decide +kernel\n")
        out.append(f"example : certOK 3 {lflat(a['ds'])} {a['s']} {a['c']} fs{tag} flats{tag} cps{tag} cs{tag} "
                   f"lv{tag} lo0{tag}\n    hi0{tag} {a['m']} = true := by\n  decide +kernel\n")
        out.append(f"example : boundsOK {uw_of(a, tag)} lv{tag} lo0{tag} hi0{tag} = true := by decide +kernel\n")
        out.append(f"/-- {id_} exists: `flatKill` finds a choice ({a['gnodes']} nodes). -/")
        out.append(f"example : flatKill {a['k']} {a['m']} cs{tag} {uw_of(a, tag)} lo0{tag} hi0{tag} lv{tag} = false "
                   f":= by\n  decide +kernel\n")
    tag = "N1252"
    out.append("/-! ### Broken inputs (N1252's certificate) -/\n")
    out.append(cert_defs(b, tag))
    pre = f"certOK 3 {lflat(b['ds'])} {b['s']} {b['c']}"
    out.append(f"example : {pre} fs{tag} flats{tag} cps{tag} cs{tag} lv{tag} lo0{tag}\n    hi0{tag} 0 = true := "
               f"by\n  decide +kernel\n")
    mem, al, ka = b["flats"][0]
    out.append(f"/-- A wrong `α`. -/\ndef flatsBad : List Flat :=\n  {lfmt([(mem, al - 1, ka)], '  ')}\n")
    out.append(f"example : {pre} fs{tag} flatsBad cps{tag} cs{tag} lv{tag} lo0{tag}\n    hi0{tag} 0 = false := "
               f"by\n  decide +kernel\n")
    cs2 = [(b["cs"][0][0] + 1,) + tuple(b["cs"][0][1:])]
    out.append(f"/-- A wrong target. -/\ndef csBad : List (ℤ × ℤ × ℤ) :=\n  {lfmt(cs2, '  ')}\n")
    out.append(f"example : {pre} fs{tag} flats{tag} cps{tag} csBad lv{tag} lo0{tag}\n    hi0{tag} 0 = false := "
               f"by\n  decide +kernel\n")
    lo2 = [b["L0"][0] + 1]
    out.append(f"/-- A bound off by one. -/\nexample : boundsOK w{tag} w{tag} 0 lv{tag} {lflat(lo2)} hi0{tag} = false "
               f":= by\n  decide +kernel\n")
    lv2 = [([1], b["lv"][0][1], b["lv"][0][2])] + b["lv"][1:]
    out.append(f"/-- A wrong index. -/\ndef lvBad : List Level :=\n  {lfmt(lv2, '  ')}\n")
    out.append(f"example : {pre} fs{tag} flats{tag} cps{tag} cs{tag} lvBad lo0{tag}\n    hi0{tag} 0 = false := "
               f"by\n  decide +kernel\n")
    out.append(f"/-- A list missing a vector. -/\nexample : rotOK 3 v0{tag} {lflat(b['W'][1:])} = false := "
               f"by decide +kernel\n")
    n = len(b["fs"])
    mem3 = [i in (0, 1, 2) for i in range(n)]
    out.append(f"/-- The three coordinate hyperplanes are not a flat (no `α` fits). -/\n"
               f"def memBad : List Bool :=\n  {lfmt(mem3, '  ')}\n")
    out.append(f"example : incOK 3 [3, 3, 3] fs{tag} (memBad, 1, 1) = false := by decide +kernel\n")
    out.append(f"example : incOK 3 [3, 3, 3] fs{tag} (memBad, 2, 1) = false := by decide +kernel\n")
    out.append(f"/-- A repeated point in the absolute-sum group. -/\n"
               f"example : sepOK 3 [3, 3, 3] fs{tag} [[0, 1, 2], [0, 1, 2]] = false := by decide +kernel\n")
    out.append(f"end SignedDifferenceSets.Tests.TomographyFlat\n")
    text = "\n".join(out)
    open(TEST, "w", encoding="utf-8", newline="\n").write(text)
    for i, l in enumerate(text.split("\n"), 1):
        assert len(l) <= 100, (TEST, i, len(l), l)
    print("wrote", TEST)


def main():
    if "--tests" in sys.argv:
        write_tests()
        return
    test = "--test" in sys.argv
    search = "--search" in sys.argv
    for arg in [x for x in sys.argv[1:] if not x.startswith("--")]:
        id_, p, r = arg.split(":")
        sub = next((x.split("=")[1] for x in sys.argv if x.startswith("--sub=")), None)
        if sub:
            v, k, lam, ms, status = TQ.row_of(id_)
            a = sub_cert(build(id_, int(p), int(r), v, k, lam, ms, status, kill=False),
                         [int(x) for x in sub.split(",")])
        else:
            a = analyse(id_, int(p), int(r), search)
        if a["killed"] is None:
            print(id_, "skip", a["why"], flush=True)
            continue
        print(id_, (a["v"], a["k"], a["lam"]), a["ms"], "p", p, "r", r, "c", a["c"], "s", a["s"],
              "|W|", len(a["W"]), "vnodes", a["vnodes"], "J", len(a["cps"]), "gnodes", a["gnodes"],
              "root" if a["root"] else "", "KILLED" if a["killed"] else "FOUND", flush=True)
        if not test and a["killed"]:
            print("  wrote", write_row(a), flush=True)


if __name__ == "__main__":
    main()
