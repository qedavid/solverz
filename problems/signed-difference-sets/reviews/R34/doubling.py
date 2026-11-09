"""I21 objects: find an involution u with |D(y)| = |D(y+u)| for all y; then Z = halved 'same-sign' part on G/<u>
must be an SDS (v/2, (k+lam)/4, lam/2), and W = 'opposite-sign' part must satisfy |chi(W)|^2 = n for chi(u) = -1."""
import itertools, numpy as np
src = open("R34/check_objects.py", encoding="utf-8").read().split("rows = {r")[0]
co = {}; exec(compile(src.replace("ROOT = sys.argv[1]", "ROOT = None"), "co", "exec"), co)

def shift(A, g):
    return np.roll(A, shift=[-x for x in g], axis=tuple(range(A.ndim)))  # S[y] = A[y+g]

for o in [79, 80, 81, 82, 83, 84, 101, 104]:
    dims, v, k, lam, D = co["parse_object"](f"objects/O{o}.txt")
    n = k - lam
    found = []
    for u in itertools.product(*[range(d) for d in dims]):
        if not any(u) or any((2 * a) % d for a, d in zip(u, dims)):
            continue
        Du = shift(D, u)
        if not np.array_equal(np.abs(D), np.abs(Du)):
            continue
        Y = np.where(D == Du, D, 0)     # (1+u)Z
        W = np.where(D == -Du, D, 0)    # (1-u)T part
        # Z's autocorrelation on G/<u>: YY* = (1+u)(ZZ*) lifted; check via characters with chi(u)=1
        FY, FW = np.fft.fftn(Y.astype(float)), np.fft.fftn(W.astype(float))
        idx = np.indices(dims).reshape(len(dims), -1).T
        phase = np.array([sum(i * a / d for i, a, d in zip(ix, u, dims)) for ix in idx]) % 1  # chi(u) = exp(2 pi i phase)
        plus = np.isclose(phase, 0); minus = np.isclose(phase, 0.5)
        aY, aW = np.abs(FY.ravel()) ** 2, np.abs(FW.ravel()) ** 2
        zero = np.zeros(len(plus), bool); zero[0] = True
        # chi(u)=1, chi != 1: |chi((1+u)Z)|^2 = 4|chi(Z)|^2 = 4 (n/4) = n ; chi(u)=-1: chi(Y)=0 and |chi(W)|^2 = n
        okZ = np.allclose(aY[plus & ~zero], n) and np.allclose(aY[minus], 0)
        okW = np.allclose(aW[minus], n) and np.allclose(aW[plus], 0)
        kz = int(np.count_nonzero(Y)) // 2; kt = int(np.count_nonzero(W)) // 2
        found.append((u, okZ, okW, kz, kt))
    good = [f for f in found if f[1] and f[2]]
    print(f"O{o} {dims} ({v},{k},{lam}) n={n}: involutions with |D(y)|=|D(y+u)|: {len(found)}, doubling-consistent: {len(good)};",
          (f"e.g. u={good[0][0]} |Z|={good[0][3]} (expect {(k+lam)//4}) |T|={good[0][4]} (n/4={n//4})" if good else ""))
