"""Check each row's statement and numbers against instances.csv and against each other. Own code."""
import re, math, parse
from collections import Counter

def factor(n):
    f, d = Counter(), 2
    n = abs(n)
    while d * d <= n:
        while n % d == 0:
            f[d] += 1; n //= d
        d += 1
    if n > 1: f[n] += 1
    return f

def primary(ms):
    out = Counter()
    for m in ms:
        for q, e in factor(m).items():
            out[q ** e] += 1
    return out

def prank(ms, p):
    return sum(1 for m in ms if m % p == 0)

def isqrt_exact(x):
    if x < 0: return None
    r = math.isqrt(x)
    return r if r * r == x else None

def mult_group(p, n):
    """t mod p in <q mod p> for every prime q | n (C10' on Z_p); requires p ∤ n."""
    if n == 0 or n % p == 0: return None
    U = set(range(1, p))
    for q in factor(n):
        g, x = set(), 1
        for _ in range(p):
            g.add(x); x = x * (q % p) % p
        U &= g
    return U

if __name__ == '__main__':
    rows = parse.all_rows()
    tab = parse.table()
    corr = open(parse.ROOT + '/corrections.md', encoding='utf-8').read()
    bad = []
    summary = Counter()
    for r in rows:
        e = []
        rid, p, c, k, lam, ms = r['id'], r['p'], r['c'], r['k'], r['lam'], r['ms']
        if r['stmt_group'] != ms: e.append('stmt group != ms')
        key = tab[rid]['key']
        m = re.match(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]*)\]\)', key)
        v_, k_, l_, g_ = int(m.group(1)), int(m.group(2)), int(m.group(3)), [int(x) for x in m.group(4).split(',')]
        if (k_, l_) != (k, lam): e.append('k,lam %s vs table %s' % ((k, lam), (k_, l_)))
        if primary(g_) != primary(ms): e.append('group %s vs table %s' % (ms, g_))
        v = math.prod(ms)
        if v != v_ or v != c * p * p: e.append('v/c mismatch')
        if prank(ms, p) < 2: e.append('p-rank < 2')
        if tab[rid]['status'] != 'open': e.append('status ' + tab[rid]['status'])
        if re.search(r'\b%s\b' % rid, corr): e.append('in corrections.md')
        ch = r['chk']
        if not (ch['p'] == ch['p1'] == ch['p3'] == ch['p4'] == p and ch['c'] == ch['c2'] == ch['c3'] == c
                and ch['p2'] == p and ch['k'] == ch['k2'] == k and ch['lam'] == ch['lam2'] == lam):
            e.append('kernel-check params %s' % ch)
        s = ch['s']
        if s * s != k + lam * (v - 1): e.append('s^2')
        if r['nc'] != (s % p == 0): e.append('nc route vs p|s')
        if r['pt'] and r['pt'][:2] != (p, s): e.append('pt params')
        for lq in r['leafQ']:
            if lq != (p, p, s, c): e.append('leafQ params %s' % (lq,))
        n = k - lam
        U = mult_group(p, n)
        t = r['t']
        if r['nc']:
            if t is not None: e.append('nc with t')
        elif t == 1:
            if r['mult'] is not None: e.append('t=1 with mult')
        else:
            if U is None or t % p not in U or t % p in (0, 1): e.append('t=%s not in U=%s' % (t, U))
            if r['mult'][0] != n: e.append('mult n')
            if math.prod(q ** a for q, a, f in r['mult'][1]) != n: e.append('fs product')
            for q, a, f in r['mult'][1]:
                if factor(q) != Counter({q: 1}) or pow(q, f, p) != t % p: e.append('fs entry %s' % ((q, a, f),))
            if r['orbOK'] != (p, t): e.append('orbOK params')
        if r['sorry']: e.append('forbidden token')
        route = ('nc' if r['nc'] else ('t=1' if t == 1 else 't=%d' % t)) + '/' + r['closer'] + '/' + r['lists'] + ('/split' if 'inPart_of_top' in open(parse.ROWS + '/' + r['file'], encoding='utf-8').read() else '')
        summary[(p, route)] += 1
        r['s'] = s; r['U'] = U; r['route'] = route
        if e: bad.append((rid, e))
    print('rows', len(rows))
    for kk, vv in sorted(summary.items()): print(kk, vv)
    print('problems:', bad if bad else 'none')
