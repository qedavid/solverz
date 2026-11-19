"""Every Z (27,14,5) (Z(0)=-1, sum 12; and all its translates) and every T (27,9,0) with sum 3 has its
coset-sum vector b -> sum_a f(9a+b) in rots(zList) / rots(tList) of PairRows/N464/Lists.lean."""
import re, sys
P = sys.argv[1]
src = open(f"{P}/lean/SignedDifferenceSets/PairRows/N464/Lists.lean", encoding="utf-8").read()
def lst(name):
    body = re.search(r"def %s : List \(List ℤ\) :=\s*\[(.*?)\]\]" % name, src, re.S).group(1) + "]"
    return [tuple(int(x) for x in v.split(',')) for v in re.findall(r"\[([-\d, ]+)\]", body)]
zL, tL = lst('zList'), lst('tList')
rots = lambda L: {tuple(w[(b + h) % 9] for b in range(9)) for w in L for h in range(9)}
rz, rt = rots(zL), rots(tL)
print('zList', len(zL), 'tList', len(tL), '| rots:', len(rz), len(rt))
cos = lambda f: tuple(sum(f[9 * a + b] for a in range(3)) for b in range(9))
def tr(f, a0, b0): return [f[9 * ((a + a0) % 3) + (b + b0) % 9] for a in range(3) for b in range(9)]
rd = lambda fn: [[int(x) for x in l.split()] for l in open(fn) if l.strip()]
Z = rd('rs/zsN464.txt'); T = rd('rs/tall.txt')
zall = {tuple(tr(z, a, b)) for z in Z for a in range(3) for b in range(9)}
print('Z normalised', len(Z), 'all Z with sum 12:', len(zall), 'coset vectors outside rots(zList):',
      sum(1 for z in zall if cos(z) not in rz))
print('T with sum 3:', len(T), 'outside rots(tList):', sum(1 for t in T if cos(t) not in rt))
print('distinct Z coset vectors', len({cos(z) for z in zall}), 'of rots(zList)', len(rz),
      '| distinct T coset vectors', len({cos(t) for t in T}), 'of rots(tList)', len(rt))
