"""Parse the 67 row files; check statement vs instances.csv key, cert validity (own code), Params link."""
import csv, re, glob, os, math, ast
from itertools import product
P_ROOT = os.path.join(os.path.dirname(__file__), '..', '..', '..')
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
rows = {r['id']: r for r in csv.DictReader(open(os.path.join(P_ROOT, 'instances.csv'), encoding='utf-8'))}
DS = [2, 2, 3]
bad = 0; n = 0; sets = set()
for f in sorted(glob.glob(os.path.join(P_ROOT, 'lean/SignedDifferenceSets/KleinTomographyRows/N*.lean'))):
    rid = os.path.basename(f)[:-5]; txt = open(f, encoding='utf-8').read(); n += 1
    st = re.search(r'theorem not_hasSDS : ¬ HasSDS \((.*?)\) (\d+) (-?\d+) :=', txt)
    w = re.search(r'\(w := ⟨(\d+), \[([\d, ]+)\], (\d+), (-?\d+)⟩\)', txt)
    c = re.search(r'\(c := ⟨(\[.*?\]\]), (\[.*?\]\])⟩\)', txt)
    pk = re.search(r'Params\.kills_(\d+)_(\d+)_(-?\d+) _', txt)
    v, k, lam, ms = KEY.match(rows[rid]['key']).groups(); v, k, lam = int(v), int(k), int(lam); ms = [int(x) for x in ms.split(',')]
    errs = []
    if rows[rid]['status'] != 'open': errs.append('status ' + rows[rid]['status'])
    if st.group(1) != ' × '.join(f'ZMod {m}' for m in ms): errs.append('group ' + st.group(1))
    if (int(st.group(2)), int(st.group(3))) != (k, lam): errs.append('k lam')
    if int(w.group(1)) != int(rid[1:]) or [int(x) for x in w.group(2).split(',')] != ms or (int(w.group(3)), int(w.group(4))) != (k, lam): errs.append('w')
    if tuple(map(int, pk.groups())) != (v, k, lam): errs.append('params')
    A = ast.literal_eval(c.group(1)); P = ast.literal_eval(c.group(2))
    Af = [a + [0]*(len(ms)-len(a)) for a in A]; Pf = [p + [0]*(len(ms)-len(p)) for p in P]
    if len(A) != 3 or len(P) != 3: errs.append('shape')
    for t, d in enumerate(DS):
        if any((Af[t][i]*ms[i]) % d for i in range(len(ms))): errs.append(f'form {t} not hom')
    img = lambda x: tuple(sum(Af[t][i]*x[i] for i in range(len(ms))) % DS[t] for t in range(3))
    for t in range(3):
        if img(Pf[t]) != tuple(int(u == t) for u in range(3)): errs.append(f'preimage {t}')
    # brute-force image of the generators spans Z2 x Z2 x Z3
    gens = [img([int(i == j) for i in range(len(ms))]) for j in range(len(ms))]
    span = {(0, 0, 0)}; fr = [(0, 0, 0)]
    while fr:
        x = fr.pop()
        for g in gens:
            y = tuple((x[t]+g[t]) % DS[t] for t in range(3))
            if y not in span: span.add(y); fr.append(y)
    if len(span) != 12: errs.append('not onto')
    sets.add((v, k, lam))
    if errs: bad += 1; print(rid, errs)
print(n, 'rows', bad, 'bad', len(sets), 'parameter sets')
