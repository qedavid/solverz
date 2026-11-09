# Refuter notes, P18 M1 / C32 (2026-11-09)

- indep.py: independent M1 kill search over instances.csv -> indep.out (60 open = settle-m1.tsv = Lean rows; 0 exists).
- lean_rows_vs_csv.py: Lean Row literals vs instances.csv keys: 120/120 match.
- objects_check.py: 107 known sets, 19 quotients with odd p, p^2 | m; 9 meet hypotheses, bound + descent + restriction hold;
  6 of 10 failing the q-condition have no descending translate.
- brute_small.py: Z_9 c = 1..3 exhaustive, no violation; control n = 19 (c = 2) exceeds bound with q-condition failing.
  Z_18 c = 1 (3^18) run -> brute18.out.
- ls_equiv.py: M1 q-condition == Schmidt/Tan exponent test at one odd prime (14,784 agree).
- subset_tan.py: all 3,335 M1 (row, m, p) kills are Tan F-bound kills with F(m,n) | m/p.
- Probe.lean (env slot, 47 s): #check types, axioms clean, row theorems as literal ¬HasSDS (N10381, N54948 on
  ZMod 3 × ZMod 147, N69420), non-vacuity on SDS(9, 9, 5) in C9, p = 2 rejected. probe.out.
- recompile.out: lake env lean on the three source files (current sources, not the oleans).
- Literature: Tan arXiv:1610.01914v4 HTML opened (Def 2.10, Results 2.11-2.12); He-Wu abstract; AMS/NTU PDFs unreadable.
