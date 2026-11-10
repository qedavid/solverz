# C41 refuter notes (2026-11-10)
- report: scratch/refuter/C41-2026-11-10-1748.md
- stmts.py: all 141 rows: statement group == ms, (group, k, λ) == instances.csv key (primary decomposition), status open,
  none in corrections.md, p-rank >= 2, v = c p^2, kernel-check numbers consistent (p, c, k, λ, s), s^2 = k + λ(v-1),
  NC route iff p | s, t in my own C10' group U, fs product = n, each q prime with q^f ≡ t. Routes: p=7 t=2 ptOK 86,
  t=2 tomoGoL 21; t=1 18 (11 split); nc 3; p=13 t=3 3; p=19 t=4 10.
- axioms: 72 built rows + 17 core theorems standard (ax_0..2.out); negative control rejected.
- build logs: 72 rows + 4 core + 2 tests: --wfail logs clean and newer than sources.
- explorer U0 (x_tomo_box.rs:278) skips self-conjugate q and q = p; Lean uses the strict intersection with p ∤ n.
- docs: c, s, |w|, n, t and q^f ≡ t congruences in the row docstrings consistent (own regex; title-group regex of mine was wrong, ignored).
- literature: He–Wu arXiv:2608.22936 abstract (v1 2026-08-24, v2 2026-09-20): four obstructions, 45,361 of 67,823 cases; no tomography.
  De Winter–Wang arXiv:1707.08662 (PDS order 8p^3): abstract only (PDF protected) — projective-plane incidence of Z_p / Z_p^2 subgroups.
- rows.out: 141/141 KILLED by own MITM; w == own W on all; 102 origin kills; 22 no integral; 17 box-only.
- brute.py agrees with MITM on N5085, N9398, N32153, N38726, N1028, N20237, N8571.
- objcheck.out: all objects with odd Z_p^2 quotient: identity, centring, validity, moment 0, t-fixed (O12 n=175, O24 n=32,
  O106 n=88: non-squarefree n) all True; searches FOUND where run (O12 search skipped |W|=18; p=7 NC C=49 skipped).
- 13 more rows built after the snapshot (N2096 N2097 N32213 N35656 N35786 N35802 N35810 N35814 N35836 N35838 N35842 N35877
  N6742): logs clean; AxC41_3 running. N6744's build was KILLED by the watchdog at 17:55 (stray lane file) - not built.
- Lane bug still writes result files into the problem folder root (untracked, 18 files at 18:07).
- final: SURVIVES; report scratch/refuter/C41-2026-11-10-1748.md. ctrl.py 361 still running in background at hand-back
  (N35840, N35872, N63319).
