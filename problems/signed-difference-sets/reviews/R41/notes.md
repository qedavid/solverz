# Refuter notes, C35 (2026-11-10)

Scripts (all in this folder, Python at nice 10):
- indep.py instances.csv > indep.out — independent chain kills over the whole table (126 open = M1 60 + M2 66; 0 exists).
- variants.py instances.csv {nop2|four} — no p = 2 steps (36 of 66 still killed) / 4 | d relaxed (+N12202, N12223, N56819, N56896).
- lean_rows_check.py <Rows.lean> instances.csv — 132 Row literals vs CSV; 66 certificates re-checked.
- objects_check.py objects — known sets: bound + descent at every reachable F (860 cases, 0 failures);
  objects_relaxed.py objects [noq] — controls (noq: 1,384 descent failures, 60 bound violations).
- brute.py m c — exhaustive f : Z_m -> [-c, c] (m = 8, c <= 3; m = 16, c = 1): brute_a.out.
- xsearch.py m c — all small X in Z[zeta_m] (power basis) with X Xbar = n: xsearch_a.out, xsearch_<m>_1.out.
- transversal_exact.py m trials seed — X = prod over a transversal of sigma_t(Y), exact norm: transversal_exact_<m>.out.
  (transversal.py = first version with a float norm: WRONG n for large m, superseded; check_fail.py shows it.)
- compare_F.py M, compare_F3.py M — chain's F vs Schmidt/Tan F(m, n): equal in 45,747 + 178,502 cases.
- ProbeC35.lean (probe.out), ProbeC35b.lean (probe_b.out) — Lean through scratch/lean-slot.sh env refuter.
