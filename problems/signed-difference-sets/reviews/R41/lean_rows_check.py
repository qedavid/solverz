"""Parse FieldDescentChainRows.lean: every Row literal (theorems and list) vs instances.csv; re-check
each certificate with the refuter's own reading of Kills (map, preimage, steps, witnesses, bound)."""
import csv, re, sys, math

def factor(x):
    f, p = {}, 2
    while p * p <= x:
        while x % p == 0: f[p] = f.get(p, 0) + 1; x //= p
        p += 1
    if x > 1: f[x] = f.get(x, 0) + 1
    return f
def phi(x):
    r = x
    for p in factor(x): r = r // p * (p - 1)
    return r

lean, csvf = sys.argv[1], sys.argv[2]
src = open(lean, encoding='utf-8').read()
tab = {r['id']: r for r in csv.DictReader(open(csvf, encoding='utf-8'))}
lists = lambda s: eval(s.replace('⟨', '(').replace('⟩', ')'))  # literal tuples/lists only
thm = re.findall(r'theorem fieldDescentChainKill_(N\d+) :\s*FieldDescentChainCert\.Kills (⟨.*?⟩)\s*\n\s*(⟨.*?⟩) := by', src, re.S)
lst = re.findall(r'\(⟨(\d+), (\[[\d, ]*\]), (\d+), (-?\d+)⟩,', src.split('def fieldDescentChainRows')[1])
print('theorems', len(thm), 'list entries', len(lst))
bad, p2rows, steps_hist = 0, 0, {}
for name, row, cert in thm:
    rid, ms, k, lam = lists(row)
    m, A, P, steps = lists(' '.join(cert.split()))
    key = f"SDS({math.prod(ms)},{k},{lam},[{','.join(map(str, ms))}])"
    r = tab[name]
    ok = (name == f'N{rid}') and r['key'] == key and r['status'] == 'open'
    v, n = math.prod(ms), k - lam
    ok &= all(x > 0 for x in ms) and m > 1 and v % m == 0 and n > 0
    ok &= all((a * mi) % m == 0 for a, mi in zip(A, ms)) and len(A) == len(ms) == len(P)
    ok &= sum(a * x for a, x in zip(A, P)) % m == 1 % m
    d, rad = m, list(factor(m))
    for p, ws in steps:
        ok &= len(factor(p)) == 1 and factor(p)[p] == 1 and d % (p * p) == 0
        ok &= p % 2 == 1 or d % 8 == 0
        dp = d // p
        ok &= all(dp % r_ == 0 for r_ in rad)
        for q in factor(n):
            w = [x for x in ws if x[0] == q]
            good = False
            for (_, t, a, e) in w:
                M = m // q ** a if m % q ** a == 0 else None
                if M and math.gcd(t, m) == 1 and t % d == (1 + dp) % d and t % M == pow(q, e, M):
                    good = True
            ok &= good
        d = dp
    F, c = d, v // m
    ok &= m * F * c * c < phi(m) * n
    if any(p == 2 for p, _ in steps): p2rows += 1
    steps_hist[len(steps)] = steps_hist.get(len(steps), 0) + 1
    if not ok: bad += 1; print('BAD', name)
for (rid, ms, k, lam) in lst:
    key = f"SDS({math.prod(eval(ms))},{k},{lam},[{','.join(map(str, eval(ms)))}])"
    if tab[f'N{rid}']['key'] != key: bad += 1; print('BAD list', rid)
print('bad', bad, 'rows with a p=2 step', p2rows, 'steps', steps_hist)
