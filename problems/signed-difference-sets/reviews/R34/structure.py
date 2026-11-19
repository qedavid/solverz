"""Structure of the I19 X1 sets: character values, symmetry, and the Q - B decomposition test."""
import sys, numpy as np
sys.argv = [sys.argv[0], "."]
src = open("R34/check_objects.py", encoding="utf-8").read().split("rows = {r")[0]
co = {}; exec(compile(src, "co", "exec"), co)

def neg(A):
    return np.flip(np.roll(A, shift=[-1]*A.ndim, axis=tuple(range(A.ndim))), axis=tuple(range(A.ndim)))  # A(-x)

def ds_params(S):
    F = np.fft.fftn(S.astype(float)); p = np.abs(F)**2
    return sorted(set(np.round(p.ravel()[1:], 6)))

for o in [64, 65, 66, 67, 61, 62, 63]:
    dims, v, k, lam, D = co["parse_object"](f"objects/O{o}.txt")
    Dn = neg(D)
    F = np.fft.fftn(D.astype(float))
    vals = np.round(F.ravel()[1:], 6)
    real = np.allclose(vals.imag, 0)
    print(f"O{o} {dims} ({v},{k},{lam}) symmetric D(-x)=D(x): {np.array_equal(Dn, D)}, antisym: {np.array_equal(Dn, -D)}, chars real: {real}, #distinct chi(D): {len(set(vals))}, D(0)={D.flat[0]}")
    if o in (64,):
        P = (D == 1).astype(int); N = (D == -1).astype(int)
        Q = P + neg(N); B = N + neg(N)
        print("   Q=P+(-N) 0/1:", Q.max() <= 1, "|Q|=", Q.sum(), "|chi(Q)|^2:", ds_params(Q)[:3], " B=N+(-N):", B.max() <= 1, "|B|=", B.sum(), "chi(B) values:", sorted(set(np.round(np.fft.fftn(B.astype(float)).ravel()[1:].real, 6))))
        print("   Q skew (Q + Q(-x) = G - 0):", np.array_equal(Q + neg(Q), 1 - (np.indices(Q.shape).sum(0) == 0).astype(int) if False else None))
        G0 = np.ones_like(Q); G0.flat[0] = 0
        print("   Q + (-Q) == G - {0}:", np.array_equal(Q + neg(Q), G0))
