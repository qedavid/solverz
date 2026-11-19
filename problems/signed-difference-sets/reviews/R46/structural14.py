"""C38's 14 rows by hand: Q - t = M^2 forces Z = u + eps*M*delta_g (see report); list the (u, eps, sign) meeting
sum and square sum, and whether |Z| <= c and the absolute-sum bounds allow them."""
import ast
for l in open("check_rows.out"):
    d = ast.literal_eval(l)
    if d["sub"] != "MaDividedResRows": continue
    N, Q, t, s1, M, c = d["N"], d["Q"], d["t"], d["s1"], d["M"], d["c"]
    assert Q - t == M * M, d["name"]
    sols = []
    for u in range(-Q - 1, Q + 2):
        for eps in (1, -1):
            for sg in (1, -1):
                if N * u + eps * M == sg * s1 and (N - 1) * u * u + (u + eps * M) ** 2 == Q:
                    assert N * u * u + 2 * eps * M * u == t
                    A = (N - 1) * abs(u) + abs(u + eps * M)
                    sols.append((u, eps, sg, max(abs(u), abs(u + eps * M)) <= c, A, d["bounds"]))
    print(d["name"], f"N={N} Q={Q} t={t} M={M} s'={s1} c={c}", "two-valued candidates:", sols or "none")
