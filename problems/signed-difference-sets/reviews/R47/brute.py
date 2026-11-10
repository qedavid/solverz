"""Plain brute force over all (p+1)-tuples from the row's own w (no hashing), as a cross-check of indep.choices."""
import sys, itertools, numpy as np, parse, indep
for rid in sys.argv[1:]:
    r = parse.parse_row(parse.ROWS + '/' + rid + '.lean')
    p, c, s = r['p'], r['c'], r['chk']['s']
    W = np.array(r['w'], dtype=np.int64)
    idx = indep.line_index(p)
    # contributions: for line L and vector i, the p*p vector W[i][idx[L]]
    contrib = np.stack([W[:, idx[L]] for L in range(p + 1)])  # (p+1, nW, p*p)
    nW = len(W)
    # enumerate tuples of the first p lines in chunks, last line vectorised
    nint = nbox = 0
    for tup in itertools.product(range(nW), repeat=p):
        S = sum(contrib[L][tup[L]] for L in range(p))
        T = S[None, :] + contrib[p] - s   # (nW, p*p)
        integ = np.all(T % p == 0, axis=1)
        nint += int(integ.sum())
        nbox += int((integ & np.all(np.abs(T) <= p * c, axis=1)).sum())
    print(rid, 'p=%d |w|=%d tuples=%d integral=%d box=%d' % (p, nW, nW ** (p + 1), nint, nbox), flush=True)
