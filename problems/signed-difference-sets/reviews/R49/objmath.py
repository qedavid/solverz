"""Check 1: C43's identities on every known SDS with a Z_p^r quotient (r >= 2), own code.
For each object and prime p with p-rank R >= 2: random onto maps phi : G -> Z_p^r (r = 2..min(R,4)),
then (a) leaf identity p^(r-1) W(q) = sum_f y_f(f.q) - ((p^(r-1)-1)/(p-1)) s at every q;
(b) the flat identity for the hyperplanes through a random subspace K (sum = alpha s + (N-alpha) Z(q));
(c) demands of every y_f; (d) centring (p !| s): a translate makes every y_f's first moment 0 mod p;
(e) no-centring normalisation: a translate puts each unit hyperplane's largest |y| at 0."""
import itertools, random, sys
random.seed(1)

def load(fn):
    L = open(fn).read().split('\n')
    head = L[0].split()
    ns = [int(t) for t in head[0][1:].split('xC')]
    v, k, lam = map(int, head[1].strip('()').split(','))
    D = {}
    for ln in L[1:]:
        t = ln.split()
        if not t: continue
        D[tuple(int(a) for a in t[:-1])] = 1 if t[-1] == '+' else -1
    return ns, v, k, lam, D

def hyperplanes(p, r):
    out = []
    for f in itertools.product(range(p), repeat=r):
        nz = [a for a in f if a]
        if nz and nz[0] == 1: out.append(f)
    return out

def rank_mod_p(M, p):
    M = [list(row) for row in M]; rk = 0; cols = len(M[0]) if M else 0
    for c in range(cols):
        piv = next((i for i in range(rk, len(M)) if M[i][c] % p), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [a * inv % p for a in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] % p:
                fac = M[i][c]; M[i] = [(a - fac * b) % p for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk

def main(files):
    nbad = 0; ncase = 0
    for fn in files:
        ns, v, k, lam, D = load(fn)
        s = sum(D.values())
        G = list(itertools.product(*[range(n) for n in ns]))
        for p in [2, 3, 5, 7]:
            idx = [i for i, n in enumerate(ns) if n % p == 0]
            R = len(idx)
            if R < 2: continue
            for r in range(2, min(R, 4) + 1):
                if p ** r > 2500 or len(G) * (p ** r - 1) // (p - 1) > 3_000_000: continue
                for trial in range(2):
                    while True:
                        A = [[random.randrange(p) for _ in range(R)] for _ in range(r)]
                        if rank_mod_p(A, p) == r: break
                    phi = {x: tuple(sum(A[a][b] * x[idx[b]] for b in range(R)) % p for a in range(r)) for x in G}
                    c = v // p ** r; C = v // p
                    Q = list(itertools.product(range(p), repeat=r))
                    W = {q: 0 for q in Q}
                    for x, d in D.items(): W[phi[x]] += d
                    hs = hyperplanes(p, r)
                    dot = lambda f, q: sum(a * b for a, b in zip(f, q)) % p
                    Y = {}
                    for f in hs:
                        y = [0] * p
                        for q in Q: y[dot(f, q)] += W[q]
                        Y[f] = y
                    alpha = (p ** (r - 1) - 1) // (p - 1)
                    bad = []
                    for q in Q:
                        if p ** (r - 1) * W[q] != sum(Y[f][dot(f, q)] for f in hs) - alpha * s: bad.append(('leaf', q))
                    # (b) flats through a random subspace K of dim d0
                    for d0 in range(0, r - 1):
                        while True:
                            Kb = [tuple(random.randrange(p) for _ in range(r)) for _ in range(d0)]
                            if d0 == 0 or rank_mod_p(Kb, p) == d0: break
                        K = set()
                        for co in itertools.product(range(p), repeat=d0):
                            K.add(tuple(sum(co[i] * Kb[i][j] for i in range(d0)) % p for j in range(r)))
                        flat = [f for f in hs if all(dot(f, z) == 0 for z in K)]
                        N = len(flat)
                        cnts = {}
                        for z in Q:
                            cnts.setdefault(sum(1 for f in flat if dot(f, z) == 0), 0)
                        al = [a for a in cnts if a != N]
                        if len(al) != 1: bad.append(('flatcount', d0, sorted(cnts))); continue
                        al = al[0]
                        for q in Q:
                            Z = sum(W[tuple((q[j] + z[j]) % p for j in range(r))] for z in K)
                            if sum(Y[f][dot(f, q)] for f in flat) != al * s + (N - al) * Z: bad.append(('flat', d0, q))
                            if abs(Z) > c * len(K): bad.append(('box', d0, q))
                    # (c) demands
                    for f in hs:
                        y = Y[f]
                        ok = (sum(y) == s and sum(a * a for a in y) == k + lam * (C - 1)
                              and all(sum(y[t] * y[(t + g) % p] for t in range(p)) == lam * C for g in range(1, p))
                              and sum(abs(a) for a in y) <= k and (k - sum(abs(a) for a in y)) % 2 == 0
                              and max(abs(a) for a in y) <= C)
                        if not ok: bad.append(('demands', f, y))
                    # (d) centring
                    if s % p:
                        m = [sum(d * phi[x][j] for x, d in D.items()) % p for j in range(r)]
                        u = pow(s % p, p - 2, p)
                        t = tuple(u * a % p for a in m)  # translate in Q: D'(x)=D(x+t~), phi t~ = t
                        Wc = {q: W[tuple((q[j] + t[j]) % p for j in range(r))] for q in Q}
                        for f in hs:
                            y = [0] * p
                            for q in Q: y[dot(f, q)] += Wc[q]
                            if sum(i * y[i] for i in range(p)) % p: bad.append(('centre', f))
                    # (e) NC normalisation: unit hyperplanes
                    t = []
                    for j in range(r):
                        e = tuple(1 if i == j else 0 for i in range(r))
                        y = Y[e]; t.append(max(range(p), key=lambda h: abs(y[h])))
                    Wn = {q: W[tuple((q[j] + t[j]) % p for j in range(r))] for q in Q}
                    for j in range(r):
                        e = tuple(1 if i == j else 0 for i in range(r))
                        y = [0] * p
                        for q in Q: y[dot(e, q)] += Wn[q]
                        if any(abs(y[h]) > abs(y[0]) for h in range(p)): bad.append(('nc', j))
                    ncase += 1
                    if bad: nbad += 1; print('BAD', fn, p, r, bad[:5])
                    else: print('ok', fn.split('/')[-1], ns, (v, k, lam), 'p', p, 'r', r, 's', s, 'p|s' if s % p == 0 else 'centred')
    print('cases', ncase, 'bad', nbad)

if __name__ == "__main__": main(sys.argv[1:])
