"""Check 3: each TomographyFlatRows row against instances.csv, and an independent verdict (own code).
Verdict: enumerate valid hyperplane vectors on Z_p (fibres C = v/p) with own code; p = 3 centred: brute force over all
choices when small, else the origin argument; p = 2 (2 | s): the leaf condition by the T-argument / brute force."""
import csv, re, glob, math, itertools, sys, os

ROOT = os.path.dirname(os.path.abspath(__file__)) + '/../../..'
inst = {}
for row in csv.DictReader(open(ROOT + '/instances.csv', encoding='utf-8')):
    m = re.match(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]*)\]\)', row['key'])
    inst[row['id']] = (int(m[1]), int(m[2]), int(m[3]), [int(a) for a in m[4].split(',')], row['status'])

def valid_vectors(p, C, k, lam, s, centred):
    """All b on Z_p meeting C3's demands (own enumeration, p = 2, 3)."""
    Q = k + lam * (C - 1); out = []
    for b in itertools.product(range(-C, C + 1), repeat=p - 1):
        last = s - sum(b)
        if abs(last) > C: continue
        y = list(b) + [last]
        if sum(a * a for a in y) != Q: continue
        if any(sum(y[t] * y[(t + g) % p] for t in range(p)) != lam * C for g in range(1, p)): continue
        A = sum(abs(a) for a in y)
        if A > k or (k - A) % 2: continue
        if centred and sum(t * y[t] for t in range(p)) % p: continue
        out.append(tuple(y))
    return out

def hyperplanes(p, r):
    return [f for f in itertools.product(range(p), repeat=r) if any(f) and [a for a in f if a][0] == 1] if r else []

def verdict(p, r, c, C, k, lam, s):
    centred = s % p != 0
    V = valid_vectors(p, C, k, lam, s, centred)
    hs = hyperplanes(p, r); N = len(hs); al = (p ** (r - 1) - 1) // (p - 1)
    Qs = list(itertools.product(range(p), repeat=r))
    dot = lambda f, q: sum(a * b for a, b in zip(f, q)) % p
    info = 'p=%d r=%d c=%d C=%d s=%d |V|=%d %s' % (p, r, c, C, s, len(V), 'centred' if centred else 'nc')
    if not V: return 'KILL (no vector)', info
    if not centred:
        # NC: unit hyperplanes normalised (largest |.| at 0), others any vector (all rotations are in V already)
        pass
    zeros = sorted(set(y[0] for y in V))
    if centred and len(zeros) == 1:
        a = zeros[0]; val = N * a - al * s; g = p ** (r - 1)
        if val % g or abs(val // g) > c:
            return 'KILL origin (%d*%d-%d*%d=%d, /%d)' % (N, a, al, s, val, g), info + ' w0=%d' % a
    # brute force over all choices when small
    U = [y for y in V if all(abs(y[h]) <= abs(y[0]) for h in range(p))]
    nunit = 0 if centred else r
    sizes = [len(U)] * nunit + [len(V)] * (N - nunit)
    tot = math.prod(sizes)
    info += ' choices=%d' % tot
    if tot > 3 * 10 ** 7: return 'TOO BIG', info
    hs_order = [tuple(1 if i == j else 0 for i in range(r)) for j in range(r)]
    hs_order += [f for f in hs if f not in hs_order]
    nsurv = 0
    for choice in itertools.product(*[U if i < nunit else V for i in range(N)]):
        ok = True; Wsum = 0
        for q in Qs:
            tq = sum(choice[i][dot(hs_order[i], q)] for i in range(N)) - al * s
            if tq % p ** (r - 1): ok = False; break
            w = tq // p ** (r - 1)
            if abs(w) > c: ok = False; break
            Wsum += abs(w)
        if ok and Wsum <= k and (k - Wsum) % 2 == 0: nsurv += 1
    return ('KILL search' if nsurv == 0 else 'SURVIVES %d' % nsurv), info

if __name__ == '__main__':
    files = sorted(glob.glob(ROOT + '/lean/SignedDifferenceSets/TomographyFlatRows/N*.lean'))
    for fn in files:
        nid = os.path.basename(fn)[:-5]
        txt = open(fn, encoding='utf-8').read()
        m = re.search(r'theorem not_hasSDS : ¬ HasSDS \(([^)]*)\) (\d+) (-?\d+) :=\s*\n\s*(not_hasSDS_flat\w*) \(ms := \[([\d, ]*)\]\) \(ds := \[([\d, ]*)\]\) \(p := (\d+)\)', txt)
        grp = [int(a) for a in re.findall(r'ZMod (\d+)', m[1])]
        k, lam = int(m[2]), int(m[3]); thm = m[4]
        ms = [int(a) for a in m[5].split(',')]; ds = [int(a) for a in m[6].split(',')]; p = int(m[7])
        cC = re.search(r'\(c := (\d+)\) \(C := (\d+)\)', txt)
        c, C = int(cC[1]), int(cC[2])
        v, k0, lam0, inv, st = inst[nid]
        problems = []
        if grp != inv: problems.append('group %s vs %s' % (grp, inv))
        if (k, lam) != (k0, lam0): problems.append('params')
        if ms != inv: problems.append('ms')
        if any(d != p for d in ds): problems.append('ds')
        r = len(ds)
        if c * p ** r != v or C * p != v: problems.append('c/C')
        prank = sum(1 for n in inv if n % p == 0)
        if prank < r: problems.append('rank')
        s = math.isqrt(k + lam * (v - 1))
        if s * s != k + lam * (v - 1): problems.append('s')
        if (thm == 'not_hasSDS_flat') != (s % p != 0): problems.append('route %s with s=%d' % (thm, s))
        vd, info = verdict(p, r, c, C, k, lam, s)
        print(nid, st, 'stmt', 'OK' if not problems else problems, '|', vd, '|', info, flush=True)
