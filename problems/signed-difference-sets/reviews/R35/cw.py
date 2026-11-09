"""C29 (and C21 alone) on circulant weighing matrices CW(n, k) = SDS(n, k, 0) in Z_n, n <= 200, k = s^2 <= 100."""
from scan import best
open14 = {(112, 36), (117, 36), (180, 36), (195, 36), (156, 81), (195, 81), (198, 81),
          (112, 100), (120, 100), (155, 100), (156, 100), (165, 100), (182, 100), (195, 100)}
for s in range(2, 11):
    k = s * s
    for n in range(k + 1, 201):
        res = best([n], k, 0)
        if res is not None:
            tag = "C21" if res[-1] else "C29only"
            print(f"CW({n},{k})", tag, "OPEN14" if (n, k) in open14 else "", res[:-1])
