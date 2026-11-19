# refuter c38 notes
- check_rows.out: 66 certs re-derived, 0 bad; 52 count rows die by DP without abs bound.
- count deaths: 30 by |s'| > Q, 3 by parity (N40375 N41125 N41305: Q - s' odd), 19 by min #nonzero > N.
- C38 rows: Q - t = M^2 in all 14 -> structural: Z = u + eps*M*delta (see report).
- run14.out: own Rust search (vsearch.rs), with and without residue.
- objects_check.out: 107 sets, 12,445 l1 + 1,234 l2 quotients, 0 bad; control2 (non-self-conj K): p | W still holds on 430 -> known sets don't discriminate Ma's step.
- exists_check.out: 229 exists rows, 245 certs, 0 bad (42 residue certs feasible).
- open_scan.out: 84 count kills = 52 (C39) + 32 already in settle-c34/c36.
- probe.log: 83 constants standard axioms; recheck.log: N34201, N61887 recompiled from source.
- res14.out: own search kills all 14 with residue (<= 530 nodes); nores14.out: 7 p=3 rows die without residue (26.7M nodes).
