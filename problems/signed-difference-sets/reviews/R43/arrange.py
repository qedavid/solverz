"""Exhaustive arrangement search: given a multiset on a group prod Z_{n_i} (shape), every distinct arrangement with one
copy of the largest value at 0 (translation), autocorrelation t at every nonzero shift (numpy FFT, exact ints). Own code."""
import numpy as np
def perms(cnt):
    vals = sorted(cnt); cnt = dict(cnt); n = sum(cnt.values()); cur = []
    def rec():
        if len(cur) == n: yield list(cur); return
        for a in vals:
            if cnt[a]:
                cnt[a] -= 1; cur.append(a)
                yield from rec()
                cur.pop(); cnt[a] += 1
    yield from rec()
def search(shape, cnt, t, cap=10 ** 7, batch=20000):
    a0 = max(cnt); rest = dict(cnt); rest[a0] -= 1
    rest = {a: n for a, n in rest.items() if n}
    buf = []; tried = 0
    def flush(buf):
        X = np.array([[a0] + b for b in buf], dtype=np.float64).reshape((len(buf),) + tuple(shape))
        ax = tuple(range(1, len(shape) + 1))
        F = np.fft.fftn(X, axes=ax); ac = np.rint(np.fft.ifftn(F * np.conj(F), axes=ax).real).astype(np.int64)
        ac = ac.reshape(len(buf), -1)
        ok = (ac[:, 1:] == t).all(axis=1)
        return [buf[i] for i in np.nonzero(ok)[0]]
    for p in perms(rest):
        buf.append(p); tried += 1
        if len(buf) == batch:
            f = flush(buf); buf = []
            if f: return ("found", [a0] + f[0], tried)
        if tried >= cap: return ("cut", None, tried)
    if buf:
        f = flush(buf)
        if f: return ("found", [a0] + f[0], tried)
    return ("none", None, tried)
