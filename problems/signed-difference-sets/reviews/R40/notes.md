# C33 refuter notes (2026-11-09)
- rows_check.py: rule hits open 151 = settle.tsv, none 1869, exists 0. thm_vs_table.py: 151/151 match.
- grtest.py: Z9 c=2,3 no violations; Z3xZ3 control violates (as it should). Big runs: grtest_big.log.
- objects_check.py: 107 objects all SDS; 70 quotient tests; 4 corollary cases; 0 problems.
- gordon_no.py: 8 Gordon-No rows hit (consistent), 0 Yes/All.
- edge_bruteforce.py (researcher's) tests only p=2 (vacuous: lambda even for v even).
- Lean: Probe.lean (slow, waiting on disk), Probe2.lean (axioms + type probes only).
- Probe2/Probe3: axioms standard; type probes and non-vacuity (CW(4,4)) pass; length 151.
- grtest_big: Z18 (c=1) no hits; Z9 c=4 1296 hits 0 violations; Z3xZ2 c=2 0 violations.
- Verdict: SURVIVES (all four checks).
