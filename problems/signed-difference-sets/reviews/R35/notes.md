# Refuter C29 notes
- 20:53 report started (header + restatement). No Lean job queued yet.
- 20:58 scan.py (independent, from scratch): with and without maPairs, exactly the 11 open rows are C29-only kills;
  0 exists rows hit; 699 none rows C29-only, 4360 none by C21 alone.
- Next: controls (<= instead of <, drop q selfconj) must hit exists rows; brute-force map check of certs;
  intermediate claims on known sets (objects/); Lean axioms + statement probes via lenv-locked.sh; literature.
- 21:05 controls.py: <= hits 8 exists, drop q-selfconj hits 3 exists (N1181 j=3) -> scan sensitive. Finding 1 written.
- certs.py: all 11 certs brute-force OK (fixed a precedence bug in the ALL flag first). Finding 2 written.
- c5alone.py: composite-modulus C5 alone kills none of the rows (best Q/2c <= 0.6).
- 21:10 Probe.lean queued via lenv-locked.sh (bg task boht4r2q3): axioms, statement types, N1181 j=3 refusal probes.
- Next: literature (Ma 1985, Pott, Arasu-Dillon-Leung-Ma, Leung-Schmidt, CWM: Tan, Arasu-Gordon...).
- 21:25 Literature: AGZ 1908.08447 (ar5iv): Lander/Turyn only, no Ma. Tan 2608.18468 (html): no Ma, no CW order 195.
- !! cw.py: C29 applied to CW(n,k)=SDS(n,k,0) in Z_n (n<=200, k<=100) kills CW(195,100) [p=5, H=Z5xZ13, c=3, q=2],
  one of the 14 open CW cases (README: AGZ Table 10 minus Tan 2026). Plus many C29-only CW(n,36), CW(n,100) kills
  (n even, p=2, q=3 or 5). MUST check against known existing CWs (Strassler / Gordon CW table / AGZ).
- 21:40 AGZ Table 11 known proper CWs: 36: 26m(m>=2),48m,91,168; 100: 62m,66m(m>=2),142. No clash. AGZ Table 9: CW(195,100)
  searched only on Z39 (6 ICWs). Finding 3 written. Next: Probe2.lean with CW(195,100) cert; literature.
- 21:15 findings 4 (math), 5 (Lean statement), 6 (objects_test: 107 sets, 344 quotients, 0 failures) written.
  Lean lock held by researcher (N6970 big build); Probe.lean (boht4r2q3) and Probe2.lean (b66f5pwgg) queued.
- 21:20 literature section written. No sorry/native_decide in C29 files. Remaining: Lean probe results (Probe.lean:
  axioms + N1181 refusals; Probe2.lean: CW(195,100) theorem + CW(52,36) control) -> finding 7 (axioms) + verdict.
- 21:5x Probe2 done: cw195_100_not_hasSDS compiles, axioms clean; CW(52,36) control refused. Finding 7 written.
- Probe done: all axioms clean, refusals pass. Finding 8 + verdict written. DONE.
