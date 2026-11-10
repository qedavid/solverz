"""Known SDS objects with an odd Z_p x Z_p quotient: check C41's identity, centring, multiplier claim and that the
search over my own lists FINDS them (the certificate shape must not kill an existing set). Own code."""
import os, re, sys, itertools, math, time
import numpy as np
import indep
from stmts import factor, mult_group

OBJ = os.path.join(os.path.dirname(__file__), '..', '..', '..', 'objects')

def load(path):
    lines = open(path).read().split('\n')
    m = re.match(r'(\S+) \((\d+),(\d+),(-?\d+)\)', lines[0])
    ms = [int(x[1:]) for x in m.group(1).split('x')]
    v, k, lam = int(m.group(2)), int(m.group(3)), int(m.group(4))
    D = {}
    for l in lines[1:]:
        if not l.strip(): continue
        *xs, sg = l.split()
        D[tuple(int(x) for x in xs)] = 1 if sg == '+' else -1
    return ms, v, k, lam, D

def check_sds(ms, k, lam, D):
    els = list(itertools.product(*[range(m) for m in ms]))
    if sum(1 for x in D if D[x]) != k: return False
    arr = np.zeros(ms, dtype=np.int64)
    for x, s in D.items(): arr[x] = s
    F = np.fft.fftn(arr)
    ac = np.real(np.fft.ifftn(F * np.conj(F)))
    ac = np.rint(ac).astype(np.int64)
    flat = ac.flatten()
    return all(flat[i] == lam for i in range(1, len(flat))) and flat[0] == k

def lines_of(p):
    return [(lambda a, b, m=m: (a + m * b) % p) for m in range(p)] + [lambda a, b: b % p]

def run(path):
    ms, v, k, lam, D = load(path)
    out = []
    if not check_sds(ms, k, lam, D):
        return ['%s NOT AN SDS?' % os.path.basename(path)]
    n = k - lam
    for p in sorted(set(q for m in ms for q in factor(m))):
        idxs = [i for i, m in enumerate(ms) if m % p == 0]
        if p == 2 or len(idxs) < 2: continue
        i1, i2 = idxs[0], idxs[1]
        c = v // (p * p)
        s0 = sum(D.values())
        s = abs(s0)
        Dp = dict(D) if s0 >= 0 else {x: -y for x, y in D.items()}
        phi = lambda x: (x[i1] % p, x[i2] % p)
        els = list(itertools.product(*[range(m) for m in ms]))
        def contr(Dd):
            Wq = np.zeros((p, p), dtype=np.int64)
            for x, y in Dd.items(): Wq[phi(x)] += y
            return Wq
        def lines(Wq):
            Ys = []
            for f in lines_of(p):
                Y = [0] * p
                for a in range(p):
                    for b in range(p): Y[f(a, b)] += int(Wq[a, b])
                Ys.append(tuple(Y))
            return Ys
        centred = s % p != 0
        Dc = Dp
        if centred:
            for t0 in els:
                Dt = {tuple((x[i] - t0[i]) % ms[i] for i in range(len(ms))): y for x, y in Dp.items()}  # D(x + t0)
                Wq = contr(Dt)
                m1 = sum(int(Wq[a, b]) * a for a in range(p) for b in range(p)) % p
                m2 = sum(int(Wq[a, b]) * b for a in range(p) for b in range(p)) % p
                if m1 == 0 and m2 == 0:
                    Dc = Dt; break
            else:
                out.append('%s p=%d: NO CENTRING TRANSLATE' % (os.path.basename(path), p)); continue
        Wq = contr(Dc)
        Ys = lines(Wq)
        fs = lines_of(p)
        ident = all(sum(Ys[j][fs[j](a, b)] for j in range(p + 1)) == p * int(Wq[a, b]) + s for a in range(p) for b in range(p))
        C = c * p
        U = mult_group(p, n) if centred else None
        Ut = sorted(U - {1}) if U else []
        fixed = all(all(Y[(t * h) % p] == Y[h] for h in range(p)) for Y in Ys for t in Ut)
        t = max(Ut, key=lambda u: len(indep.orbits(p, u))) if False else (min(Ut, key=lambda u: len(indep.orbits(p, u))) if Ut else 1)
        valid = all(indep.valid(list(Y), p, C, k, lam, s) for Y in Ys)
        mom = all(indep.moment0(Y, p) for Y in Ys) if centred else True
        res = '%s %s (%d,%d,%d) p=%d c=%d s=%d centred=%s U=%s identity=%s lines_valid=%s moment0=%s t_fixed(all t in U)=%s' % (
            os.path.basename(path), 'x'.join(map(str, ms)), v, k, lam, p, c, s, centred, sorted(U) if U else U, ident, valid, mom, fixed)
        # search with my own lists, if cheap
        norb = len(indep.orbits(p, t))
        if norb <= 5 or (norb <= 7 and C <= 25):
            t1 = time.time()
            V = indep.enum_vectors(p, C, k, lam, s, t)
            Wl = [b for b in V if indep.moment0(b, p)] if centred else V
            inW = all(Y in set(Wl) for Y in Ys)
            if len(Wl) ** ((p + 1) // 2) > 3e6:
                res += ' | t=%d |W|=%d own_lines_in_W=%s choice search skipped (too many tuples)' % (t, len(Wl), inW)
            else:
                ni, nb, ex = indep.choices(p, s, c, Wl)
                res += ' | t=%d |W|=%d own_lines_in_W=%s integral=%d box=%d %s (%.1fs)' % (t, len(Wl), inW, ni, nb, 'FOUND' if nb else 'KILLED(!)', time.time() - t1)
        else:
            res += ' | search skipped (p=%d, C=%d, %d orbits)' % (p, C, norb)
        out.append(res)
    return out

if __name__ == '__main__':
    files = sorted((f for f in os.listdir(OBJ) if re.match(r'O\d+\.txt$', f)), key=lambda f: int(f[1:-4])) if len(sys.argv) < 2 else sys.argv[1:]
    for f in files:
        hdr = open(os.path.join(OBJ, f)).readline()
        ms = [int(x[1:]) for x in hdr.split()[0].split('x')]
        if not any(sum(1 for m in ms if m % q == 0) >= 2 for q in (3, 5, 7, 11, 13, 17, 19)): continue
        for line in run(os.path.join(OBJ, f)): print(line, flush=True)
