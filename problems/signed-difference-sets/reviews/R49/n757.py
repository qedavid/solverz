"""N757/N758 leaf check by meet in the middle: y_f in {(28,24),(24,28)} (eps_f = +-1), coordinate hyperplanes eps = +1
(translate); 16 W(q) = sum_f y_f(f.q) - 15*52 must be integral with |W| <= 2 at every q of Z_2^5. Also without fixing units."""
import itertools
from collections import defaultdict
r = 5; Q = list(itertools.product(range(2), repeat=r))
hs = [f for f in Q if any(f)]
units = [f for f in hs if sum(f) == 1]
def run(fix_units):
    free = [f for f in hs if not (fix_units and f in units)]
    fixed = [f for f in hs if fix_units and f in units]
    base = [sum(28 if sum(a * b for a, b in zip(f, q)) % 2 == 0 else 24 for f in fixed) for q in Q]
    half = len(free) // 2; A, B = free[:half], free[half:]
    def tab(part):
        out = defaultdict(list)
        for eps in itertools.product((1, -1), repeat=len(part)):
            vals = tuple(sum((28 if sum(a * b for a, b in zip(f, q)) % 2 == 0 else 24) if e == 1 else
                             (24 if sum(a * b for a, b in zip(f, q)) % 2 == 0 else 28) for f, e in zip(part, eps)) for q in Q)
            out[tuple(v % 16 for v in vals)].append(vals)
        return out
    TA, TB = tab(A), tab(B)
    target = [(15 * 52 - b) % 16 for b in base]
    sols = 0; matches = 0
    for key, la in TA.items():
        need = tuple((t - x) % 16 for t, x in zip(target, key))
        for va in la:
            for vb in TB.get(need, []):
                matches += 1
                W = [(b + x + y - 15 * 52) // 16 for b, x, y in zip(base, va, vb)]
                if all(abs(w) <= 2 for w in W): sols += 1
    return len(free), matches, sols
for fu in (True, False):
    print('fix units' if fu else 'all free', 'free=%d integral=%d in-box=%d' % run(fu), flush=True)
