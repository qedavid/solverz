# notes (refuter c40)
- 14:35 indep.py: N49 FOUND 160/160, N352 FOUND 672 int/224 SDS; N346/N348/N354 KILLED (|V| 14/28/56, |W| 2/4/8, 0 integral);
  p=11 orbit rows all KILLED, Wfix = Lean w (2 vectors each). p=7 W = Lean w exactly.
- C40 cites C10 but Lean uses C16's `exists_translate_fixed_contract` (squarefree n); C10 is the primed one.
- Tests build log 13:30 succeeded (an earlier failure for privateModule warning was fixed).
- 14:50 objcheck: O6, O24, O12 pass all steps; O6/O24 reached by the search. Tests' wN352 = my W(N352).
- Rust vfull (no normalisation): N3044 22, N3074 22, N3058 22 (others running).
- axioms run restarted with declared 4 GB (first attempt waited for admission at 5 GB; killed).
- tomo N3074 build waiting (heavy) behind researcher jobs.
- Literature opened: arXiv 2608.22936 abs + html v2 (He-Wu; no projections onto all lines; nine sets not mentioned);
  mardi Q1344521 (Arasu-Sehgal 1995); arXiv 1908.07055 abs (irrelevant).
- 15:05 full-W p=11: all six |V| 22, W == Wfix, KILLED. Origin kill: N346 + six p=11 rows die at g = 0.
- Build logs (lean-build.ps1 uses --wfail): Search 13:12, Tomography 13:14, Orbit 13:15, N3044 13:19, N348 13:24, N346 13:26,
  Tests 13:30, N354 13:36, N3058 13:41, N3068 13:45, N3072 14:29; all after their files' last edits (rows 13:01-13:03,
  Tests 13:28, Search 13:11, Tomography 12:44, Orbit 12:56). Grep: no sorry/native_decide/axiom/implemented_by/extern/opaque.
- Waiting: axioms_a.out (slot admission), N3074/N3104 builds (tomo heavy, queued).
- 15:12 N3074, N3104 built (143 s, 133 s); axioms_b standard. Report finished: SURVIVES.
