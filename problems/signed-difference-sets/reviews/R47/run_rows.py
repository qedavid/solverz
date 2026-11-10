"""Recompute every row's lists and verdict with indep.py; compare with the row's w / v0."""
import sys, time, parse, indep

def rot(b, r, p):
    return tuple(b[(h + r) % p] for h in range(p))

def run(r):
    p, c, k, lam, s = r['p'], r['c'], r['k'], r['lam'], r['chk']['s']
    C = c * p
    t = r['t'] if r['t'] else 1
    t0 = time.time()
    V = indep.enum_vectors(p, C, k, lam, s, t)
    if r['nc']:
        W = V
    else:
        W = [b for b in V if indep.moment0(b, p)]
    rw = sorted(tuple(x) for x in r['w'])
    same = sorted(W) == rw
    sup = set(W) <= set(rw)
    extra = ''
    if r['v0'] is not None:
        Vfull = indep.enum_vectors(p, C, k, lam, s, 1) if t != 1 else V
        rv0 = set(tuple(x) for x in r['v0'])
        rots = {rot(b, q, p) for b in rv0 for q in range(p)}
        extra = ' V=%d v0=%d v0inV=%s Vinrots=%s' % (len(Vfull), len(rv0), rv0 <= set(Vfull), set(Vfull) <= rots)
    vals, reach = indep.origin_residues(p, s, W)
    ni, nb, ex = indep.choices(p, s, c, W)
    verdict = 'FOUND' if nb else 'KILLED'
    return ('%s p=%d c=%d (%d,%d) s=%d t=%d nc=%s |V|=%d |W|=%d w==W:%s W<=w:%s origin_vals=%s s_reachable_at_0=%s integral=%d box=%d %s%s %.1fs'
            % (r['id'], p, c, k, lam, s, t, r['nc'], len(V), len(W), same, sup, vals, reach, ni, nb, verdict, extra, time.time() - t0))

if __name__ == '__main__':
    ids = set(sys.argv[1:])
    for r in parse.all_rows():
        if ids and r['id'] not in ids: continue
        print(run(r), flush=True)
