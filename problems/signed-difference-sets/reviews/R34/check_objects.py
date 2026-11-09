"""Independent recheck of the 16 P4 objects (refuter, 2026-11-09).

For each object file: parse group and (v,k,lam); build the sign array on the
product group; check (a) count k, (b) signed autocorrelation over every nonzero
shift by explicit translation (np.roll per axis), (c) the same by characters
(FFT): |D^(chi)|^2 = k - lam for chi != 1 and D^(1)^2 = k + lam (v-1);
(d) controls: one flipped sign and one dropped element must fail;
(e) the Lean file's masks decode (mixed radix, first factor most significant)
to exactly the object's set; (f) the row key in instances.csv and Gordon's
sds.json entry match the object's header.
"""
import csv, itertools, json, re, sys
import numpy as np

ROOT = sys.argv[1]
TARGETS = [(61, 236), (62, 1008), (63, 11602), (64, 14597), (65, 14828), (66, 31880),
           (67, 31994), (103, 14472), (79, 448), (80, 463), (81, 3539), (82, 933),
           (83, 934), (84, 931), (101, 449), (104, 939)]


def parse_object(path):
    lines = [l.strip() for l in open(path, encoding="utf-8") if l.strip()]
    m = re.fullmatch(r"(\S+) \((\d+),(\d+),(-?\d+)\)", lines[0])
    dims = [int(t) for t in m.group(1).replace("C", "").split("x")]
    v, k, lam = int(m.group(2)), int(m.group(3)), int(m.group(4))
    D = np.zeros(dims, dtype=np.int64)
    seen = set()
    for l in lines[1:]:
        parts = l.split()
        coords, s = tuple(int(c) for c in parts[:-1]), parts[-1]
        assert len(coords) == len(dims), (path, l)
        assert all(0 <= c < d for c, d in zip(coords, dims)), (path, l)
        assert coords not in seen, ("duplicate", path, l)
        seen.add(coords)
        assert s in "+-"
        D[coords] = 1 if s == "+" else -1
    return dims, v, k, lam, D


def autocorr_ok(D, k, lam):
    dims = D.shape
    if int(np.count_nonzero(D)) != k:
        return False, "count %d" % np.count_nonzero(D)
    bad = 0
    for g in itertools.product(*[range(d) for d in dims]):
        if not any(g):
            continue
        S = np.roll(D, shift=[-gi for gi in g], axis=tuple(range(len(dims))))  # S[x] = D[x+g]
        if int((D * S).sum()) != lam:
            bad += 1
    return bad == 0, "bad shifts %d" % bad


def fourier_ok(D, k, lam):
    F = np.fft.fftn(D.astype(float))
    p = np.abs(F) ** 2
    v = D.size
    p0 = p.flat[0]
    rest = np.delete(p.ravel(), 0)
    return (abs(p0 - (k + lam * (v - 1))) < 1e-6 and np.max(np.abs(rest - (k - lam))) < 1e-6), \
        "max dev %.3g" % np.max(np.abs(rest - (k - lam)))


def lean_masks(path):
    txt = open(path, encoding="utf-8").read()
    P = int(re.search(r"def plus : ℕ := (0x[0-9a-f]+|\d+)", txt).group(1), 0)
    N = int(re.search(r"def minus : ℕ := (0x[0-9a-f]+|\d+)", txt).group(1), 0)
    stmt = re.search(r"theorem hasSDS :\s*HasSDS \((.*?)\) (\d+) (-?\d+) :=", txt, re.S)
    return P, N, stmt.group(1), int(stmt.group(2)), int(stmt.group(3))


def decode(P, N, dims):
    D = np.zeros(dims, dtype=np.int64)
    v = int(np.prod(dims))
    assert P >> v == 0 and N >> v == 0, "mask beyond v"
    for idx, coords in enumerate(itertools.product(*[range(d) for d in dims])):
        # itertools.product enumerates with the last coordinate fastest = first factor most significant
        if (P >> idx) & 1:
            D[coords] = 1
        elif (N >> idx) & 1:
            D[coords] = -1
    overlap = bin(P & N).count("1")
    return D, overlap


def invariant_factors(dims):
    # Smith form of a diagonal: combine prime powers.
    def factorint(n):
        f, q = {}, 2
        while q * q <= n:
            while n % q == 0:
                f[q] = f.get(q, 0) + 1; n //= q
            q += 1
        if n > 1:
            f[n] = f.get(n, 0) + 1
        return f
    pp = {}
    for d in dims:
        for p, e in factorint(d).items():
            pp.setdefault(p, []).append(p ** e)
    r = max(len(x) for x in pp.values()) if pp else 0
    out = [1] * r
    for p, xs in pp.items():
        xs = sorted(xs, reverse=True)
        for i, x in enumerate(xs):
            out[r - 1 - i] *= x
    return [x for x in out if x > 1]


rows = {r["id"]: r for r in csv.DictReader(open(ROOT + "/instances.csv", encoding="utf-8"))}
gordon = json.load(open(ROOT + "/scratch/data/gordon/sds.json", encoding="utf-8"))
rng = np.random.default_rng(20261109)
allok = True
for o, n in TARGETS:
    dims, v, k, lam, D = parse_object(f"{ROOT}/objects/O{o}.txt")
    row = rows[f"N{n}"]
    key = row["key"]
    km = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", key)
    kv, kk, kl = int(km.group(1)), int(km.group(2)), int(km.group(3))
    kfac = [int(t) for t in km.group(4).split(",")]
    g = gordon.get(key, {})
    a_ok, a_msg = autocorr_ok(D, k, lam)
    f_ok, f_msg = fourier_ok(D, k, lam)
    # controls
    nz = np.argwhere(D != 0)
    c1 = D.copy(); i = tuple(nz[rng.integers(len(nz))]); c1[i] = -c1[i]
    c2 = D.copy(); j = tuple(nz[rng.integers(len(nz))]); c2[j] = 0
    ctrl_flip = autocorr_ok(c1, k, lam)[0] or fourier_ok(c1, k, lam)[0]
    ctrl_drop = autocorr_ok(c2, k - 1, lam)[0] or autocorr_ok(c2, k, lam)[0] or fourier_ok(c2, k - 1, lam)[0]
    P, Nm, lgroup, lk, ll = lean_masks(f"{ROOT}/lean/SignedDifferenceSets/Answer/N{n}.lean")
    ldims = [int(t) for t in re.findall(r"ZMod (\d+)", lgroup)]
    LD, overlap = decode(P, Nm, ldims) if ldims == dims else (None, -1)
    same = LD is not None and np.array_equal(LD, D)
    checks = dict(
        header_v=(v == int(np.prod(dims))),
        key_vkl=((kv, kk, kl) == (v, k, lam)),
        key_group=(invariant_factors(dims) == kfac),
        lean_group=(ldims == dims and invariant_factors(ldims) == kfac),
        lean_kl=((lk, ll) == (k, lam)),
        status_exists=(row["status"] == "exists"),
        gordon_open=(g.get("status") == "Open"),
        autocorr=a_ok, fourier=f_ok,
        flip_rejected=not ctrl_flip, drop_rejected=not ctrl_drop,
        lean_masks_equal_object=same, mask_overlap0=(overlap == 0),
    )
    ok = all(checks.values())
    allok &= ok
    pos, neg = int((D == 1).sum()), int((D == -1).sum())
    print(f"O{o} N{n} {key} dims={dims} +{pos} -{neg} sum={D.sum()} {'OK' if ok else 'FAIL'}",
          "" if ok else {kk_: vv for kk_, vv in checks.items() if not vv}, a_msg, f_msg)
print("ALL OK" if allok else "SOME FAIL")
