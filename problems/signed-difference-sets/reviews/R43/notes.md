# C36 refuter notes
- 2026-11-10: read C36, C34, R42, C33, I22, MaDivided2.lean, madivided2rows.py, x_ma_iterated.rs.
- Exploration line format: `KILL p j l [H'] nodes`; H' = d with e[si] *= p^(j-l).
- N16815 sanity: Z on Z16 with sum 10 = sum sq 10 -> 0/1, a (16,10,6) cyclic DS (complement (16,6,2)), known not to exist (Turyn).
- rowset.py: 65 level-2 kills in x_ma_iterated.out; 16 also killed at single level (all `none` now); settle list = the other 49 exactly.
  4 of the 49 (N12314, N12363, N12426, N56207) are already `none` by C35 (FieldDescentChainRows): C36 newly settles 45.
- certs.py: all 49 row files parsed; theorem type = ¬HasSDS (instances group) k λ; w, cert (p, r, e, b, ks, Q, t, s', bounds
  cover every A, p^i ≡ -1 on ks) and each search module's / Check.lean's args (Grp [r]::ks, c, Q, t, k', s') match my
  recomputation: 0 mismatches. Divided groups: Z8 (Grp[8,1]), Z16 (Grp[16,1]), Z8×Z3 (Grp[8,3]); c in 4..15; all p = 2, l = 2.
- Paused 02:2x at coordinator's request (usage limit). Next: indep.py (multisets + arrangements on the 49 rows, exists rows,
  sample of open rows), objects_c36.py (known sets, p=2 included), literature, Lean probe last.
- 02:47 resumed. objects_c36.py: 107 known sets re-verified (FFT); every surjection G -> Z_{p^j} x K (all hom images, j >= 2,
  self-conjugate d): 1234 C36 quotients (b >= 2; 1072 at p = 2, 162 at p = 3): 0 violations of Ma step, W1 = pY, W2 = pW1
  (mod p^b), p^2 | W2, any demand or bound. Level 3 (b >= 3): 240 quotients, p^3 | W3 always. Control b = 1: 944 quotients,
  all 944 have p^2 ∤ W2 somewhere.
- count49.py: 35 of 49 rows have no value multiset (sum, square sum, |.| <= c, A <= floor(k/4)); 14 (Z16 rows) have 1 multiset,
  3003 or 5005 arrangements with Z(0) fixed.
- brute_ms.py: multisets() = brute force on all m <= 5, c <= 3 (35,067 cases, 0 differences).
- indep49.py (multisets + every arrangement, own FFT check): all 49 rows KILL. 27 die by parity (Q - s' odd, as ΣZ² ≡ ΣZ mod 2),
  4 by Q < |s'| (N40206, N40212, N40221, N40227), 4 have no multiset (N41151, N41157, N41271, N41277), 14 Z16 rows have one
  0/1-shifted multiset ({1^6,0^10}, {1^10,0^6}, +1, +2, +3) = a (16,6,2) DS or complement in Z16 (classically none) -> none fit.
- exists_c36.py on all `exists` rows: 35 level-2 quotients on 22 rows, all `found`. On all open rows (open.log, 4m):
  4592 quotients: found 4425, cut 76 (cap 20,000 arrangements), nomultiset 77, none 14.
- compare: 0 disagreements (no quotient x_ma_iterated marks found that I kill); every x_ma_iterated level-2 kill on an open row
  I kill at the same quotient (31 nomultiset + 14 none). BUT 24 open rows I kill (no multiset) that x_ma_iterated leaves
  open: its quotient was `cut` at 2M nodes (27 quotients cut/nomultiset). To verify.
- extra24.py: all 77 no-multiset quotients rechecked: 48 by parity (Q − s' odd), 21 by direct count loops (c = 2), 8 (c = 4,
  among the 49) by multisets() only. The 24 extra rows are all parity or c = 2 loops.
- 65 exploration notes not in my open.log: rows settled `none` since the run (e.g. N12286, N17171), not a discrepancy.
- Source scan: 273 files under MaDivided2Rows + MaDivided2.lean: no sorry/native_decide/axiom/implemented_by/extern/unsafe/admit;
  options only Elab.async, maxHeartbeats, maxRecDepth. MaDivided2.olean (02:06:47) newer than source (02:06:07); no row oleans.
- Literature written (check 4). Probe.lean submitted via lean-slot (env, 4 GB) ~03:1x; waiting.
- Probe finished (32 min incl. slot wait): axioms standard, all examples pass, n8944_plain proved. Report complete.
