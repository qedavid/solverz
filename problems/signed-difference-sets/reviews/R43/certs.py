"""Parse each MaDivided2Rows/N<id>.lean (theorem type, w, cert) and every search module's arguments; recompute
independently from instances.csv and the exploration line. Own code."""
import csv, re, sys, math, glob, os
ROOT = sys.argv[1]
LD = f"{ROOT}/lean/SignedDifferenceSets/MaDivided2Rows"
inst = {r["id"]: r for r in csv.DictReader(open(f"{ROOT}/instances.csv", encoding="utf-8"))}
it = {l.split()[0]: l.strip() for l in open(f"{ROOT}/scratch/x_ma_iterated.out", encoding="utf-8")}
settle = [l.split("\t") for l in open(f"{ROOT}/scratch/maedge/settle-c36.tsv", encoding="utf-8") if l.strip()]
def vp(x, p):
    c = 0
    while x and x % p == 0: x //= p; c += 1
    return c
def L(s): return [int(t) for t in re.findall(r"-?\d+", s)]
bad = 0
rows_files = sorted(f for f in glob.glob(f"{LD}/N*.lean") if re.fullmatch(r"N\d+\.lean", os.path.basename(f)))
print("row files:", len(rows_files))
ids_files = {os.path.basename(f)[:-5] for f in rows_files}
print("settle ids == row files:", ids_files == {s[0] for s in settle})
for sid, st, ev, thm in settle:
    thm = thm.strip()
    assert thm == f"SignedDifferenceSets.MaDivided2Rows.{sid}.not_hasSDS", thm
    src = open(f"{LD}/{sid}.lean", encoding="utf-8").read()
    key = inst[sid]["key"]
    m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", key)
    v, k, lam = int(m[1]), int(m[2]), int(m[3]); ms = L(m[4])
    assert math.prod(ms) == v
    grp = " × ".join(f"ZMod {x}" for x in ms)
    lam_l = f"({lam})" if lam < 0 else str(lam)
    want = f"theorem not_hasSDS : ¬ HasSDS ({grp}) {k} {lam_l} :="
    if want not in src: print(sid, "THEOREM TYPE MISMATCH"); bad += 1
    w = re.search(r"\(w := ⟨(\d+), \[([\d, ]+)\], (\d+), \(?(-?\d+)\)?⟩\)", src)
    if not (int(w[1]) == int(sid[1:]) and L(w[2]) == ms and int(w[3]) == k and int(w[4]) == lam):
        print(sid, "W MISMATCH", w.groups()); bad += 1
    cm = re.search(r"\(c := ⟨(.*?)⟩\)", src, re.S)[1]
    parts = re.match(r"\s*(\d+), (\d+), (\d+), (\d+), (\d+), (\[[^\]]*\]),\s*(\[.*?\]\]),\s*(\[.*?\]\]),\s*(\[[^\]]*\]), (-?\d+), (-?\d+), (-?\d+)\s*$", cm, re.S)
    p, r, i, e, b = (int(parts[t]) for t in range(1, 6))
    ks = L(parts[6]); bounds = L(parts[9]); Q, t, s1 = int(parts[10]), int(parts[11]), int(parts[12])
    # exploration line
    km = re.search(r"KILL (\d+) (\d+) (\d+) \[([\d,]+)\] (\S+)", it[sid])
    pe, je, le, He = int(km[1]), int(km[2]), int(km[3]), L(km[4])
    # my recomputation
    n = k - lam
    my = {}
    my["p"] = pe; my["r"] = pe ** (je - 2); my["e"] = vp(n, pe); my["b"] = my["e"] // 2
    oddH = sorted(x // pe ** vp(x, pe) for x in He if x // pe ** vp(x, pe) > 1)
    c = v // (my["r"] * pe * pe * math.prod(ks))
    s = math.isqrt(k + lam * (v - 1)); assert s * s == k + lam * (v - 1)
    ok = (p == pe and r == my["r"] and e == my["e"] and b == my["b"] and b >= 2 and le == 2
          and sorted(x for x in ks if x > 1) == oddH
          and pe ** 4 * Q == k + lam * (pe * pe * c - 1) and pe * pe * t == lam * c and (pe * pe * s1) ** 2 == s * s
          and s1 > 0 and math.prod(He) == my["r"] * math.prod(ks)
          and v % (my["r"] * pe * pe * math.prod(ks)) == 0)
    # bounds cover every admissible A
    cover = all(any(a <= kk and (kk - a) % 2 == 0 for kk in bounds) for a in range(k + 1)
                if p * p * a <= k and (k - p * p * a) % 2 == 0)
    # i: p^i = -1 mod each ks
    conj = i > 0 and all((p ** i + 1) % d == 0 for d in ks)
    # search modules: arguments
    sargs = []
    for kk in bounds:
        f = f"{LD}/{sid}B{kk}.lean"
        sf = open(f, encoding="utf-8").read()
        sm = re.search(r"noVector \(@Indexed.size \(Grp \[([\d, ]+)\]\) _ \(Grp.indexed _ hpos\)\)\s*\(@Indexed.addIdx \(Grp \[([\d, ]+)\]\) _ \(Grp.indexed _ hpos\)\)\s*\((\d+) : ℕ\) \((-?\d+) : ℤ\) \((-?\d+) : ℤ\) \((\d+) : ℕ\) (-?\d+) = true", sf)
        if sm is None:
            print(sid, kk, "SEARCH STATEMENT NOT PARSED"); bad += 1; continue
        g1, g2 = L(sm[1]), L(sm[2])
        sargs.append((g1, int(sm[3]), int(sm[4]), int(sm[5]), int(sm[6]), int(sm[7])))
        if not (g1 == g2 == [r] + ks and int(sm[3]) == c and int(sm[4]) == Q and int(sm[5]) == t and int(sm[6]) == kk and int(sm[7]) == s1):
            print(sid, kk, "SEARCH ARGS MISMATCH", sm.groups(), (r, ks, c, Q, t, s1)); bad += 1
        # Check.lean / parts if split
        cd = f"{LD}/{sid}B{kk}"
        if os.path.isdir(cd):
            ck = open(f"{cd}/Check.lean", encoding="utf-8").read()
            cmm = re.search(r"\((\d+) : ℕ\) \((-?\d+) : ℤ\) \((-?\d+) : ℤ\) \((\d+) : ℕ\) (-?\d+)", ck)
            if not cmm or [int(x) for x in cmm.groups()] != [c, Q, t, kk, s1]:
                print(sid, kk, "CHECK ARGS MISMATCH", cmm and cmm.groups()); bad += 1
            if f"Grp {[r] + ks}".replace(" ", "") not in ck.replace(" ", ""):
                print(sid, kk, "CHECK GROUP MISMATCH"); bad += 1
    if not (ok and cover and conj): print(sid, "CERT MISMATCH", dict(p=p, r=r, i=i, e=e, b=b, ks=ks, bounds=bounds, Q=Q, t=t, s1=s1), my, He, ok, cover, conj); bad += 1
    print(f"{sid} {key:28s} st={inst[sid]['status']:4s} p={p} j={je} H'={He} ->Grp{[r]+ks} c={c} Q={Q} t={t} s'={s1} bounds={bounds} nodes={km[5]}")
print("mismatches:", bad)
