# notes c44 refuter
- check1.py: exhaustive vectors (p=2 B20, 3 B12, 5 B7, 7 B4): n=p^2, 4p^2, p^3 all const mod p; n=p (3,5,7) and n=14 (p=7) give 138/130/98/140 non-const (controls bite). Known sets: 26 objects k-lam=p^2, 1103 Z_p maps, 0 non-const; Z_p^2 line identity 0 failures; lines always q±1; box never holds on known sets.
- stmts.py: 27 row statements (15 sq, 2 twist, 10 last) match instances.csv; no sorry/native_decide/axiom in core files.
- check2.py/2b: scan = 20 kills (18 open, 2 none, 0 exists), matches sq1.out; 5 rows enumerated vectors = rotations of (q+1)1 - p e_j.
- check3: N1575 9z/18d, 162 integral pairs min sum|W| 20>18; N1593 162 integral, none |W|<=5. Both killed without congruences.
- check4: 7 param sets killed mod 7 (0 residue matches), controls 25/49/343(172,84) found.
- check3b: 208 maps on 10 known sets, 0 failures.
- lit: Yayla 1408.6883 (Turyn Lemma 1, Ma Lemma 2) opened via pdftotext; He-Wu Thm 3.2 needs v_p(n) odd; Gordon repo no commits after e3bf810.
- 21:52 coordinator: limits 4 threads, Lean only light env jobs <=5GB, one slot at a time. Ax1 (4GB env) queued; python single-thread.
- p=11 row N14382 has 1.16e9 (sum,sq) candidates: exhaustive enumeration skipped; p=13 4e11.
- 21:53 limits lifted back to brief's.
- check4b: rows' w lists = my centred lists (7 param sets).
- Ax1: 33/33 standard axioms.
- 22:03 PAUSE (coordinator): killed my Ax2 env job (N31745 axioms, never ran) and wait loops; removed my stale slot file job.253963. Nothing of mine running.
## State at pause
Done: checks 1-6 written in C44-2026-11-10-2131.md (all SURVIVES so far); Ax1 33/33 standard axioms.
Left: (a) Ax2.lean (#print axioms N31745, built 22:00 clean 821 s 4.21 GB) — rerun via lean-slot env (4 GB);
(b) the other 8 tomolast rows (N31746, N32195/6, N15414, N15434, N31778/9, N5089) are not built yet: axioms once built;
(c) write the final verdict section and hand back.
