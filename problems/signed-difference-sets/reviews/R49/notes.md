# Refuter notes, C43 (+ C41 later rows), 2026-11-10

## Build state (21:18)
- TomographyFlat, TomographyFlatSplit, Tests/TomographyFlat: olean newer than source; logs (`scratch/build-*.log`) "Build
  completed successfully", no warning/error/sorry lines.
- TomographyFlatRows: 41 of 42 rows built (olean newer than source, log clean); N758 NOT built (no olean).

## Check 1, math on objects (`objmath.py` -> `objmath.out`)
- 248 (object, p, r, random onto phi) cases over 64 objects, p = 2,3,5,7, r = 2..4: leaf identity at every q, flat identity
  for the hyperplanes through a random subspace K (d0 = 0..r-2; incidence all-or-alpha confirmed), box |Z| <= c|K|,
  demands of every y_f, centring (p !| s) and NC normalisation: 0 failures.
- Gap: no known set gives a CENTRED Z_3^r (r >= 3) case: every Z_3^r object has 3 | s. Centred cases: p = 2,5,7 (r = 2), p = 7 r = 3.
- C43 text "At p = 3 with p !| s every centred hyperplane vector has the same value a at 0" is FALSE as a general
  statement (`p3origin.py`: e.g. s = 1, Q = 33: (-4, 4, 1) and (5, -2, -2) both centred). It holds per row only where the
  row's list shows it; Lean checks it per row (boundsOK with lo = hi), so no row depends on the general sentence.

## N757/N758 by hand
- y_f in {(28,24),(24,28)}; W = (52 + 4 sum_f eps_f chi_f)/32 on Z_2^5, |W| <= 2. T = 2 - W >= 0: sum T = 12, sum T^2 = 20,
  autocorrelation 4 at every d != 0. sum T(T-1) = 8 forces two points with T >= 2 (2,2,2,2 or 3,2), whose difference has
  autocorrelation >= 8 > 4. No W: both rows killed at the leaf alone (sub-flats only prune).

## Check 3, rows (`rows.py` -> `rows.out`, own enumeration of valid vectors, own verdicts)
- 42 row files: final theorem's group (ZMod list) = instances.csv invariants, (k, lambda) = row, ms = invariants,
  ds = [p]*r, c = v/p^r, C = v/p, p-rank >= r, s integral, route (centred iff p !| s): all 42 OK.
- Verdicts: 39 origin rows KILL at the origin (each has exactly 2 centred vectors, one shared w(0)); values match the
  row docs (e.g. N1252 13*10 - 4*19 = 54 = 9*6 > 9*3). N23597: brute force over all 2^13 = 8192 choices, 0 survive
  (integral, |W| <= 11, sum|W| <= 41, parity). N757/N758: `n757.py` meet in the middle: 523,776 integral choices
  (units fixed), 16,760,832 with all 31 free, 0 in the box |W| <= 2 (agrees with the hand argument).
- Controls (`controls.py`): SDS that exist with 3 !| s on a Z_3^r quotient (delta_0, 1 - 2 delta_0, (4,4,0)xdelta,
  (7,4,0)xdelta): own verdict and generator both NOT killed. (Weak: their lists have one vector.)

## Lists (`listcmp.py`)
- Own enumeration equals each row's `w` as a set: 42 flat rows + 62 Part B rows, 0 differ.
## Part B (`partb.py` -> `partb.out`)
- 62 built rows not in R47's lists: statements OK (group, k, lambda, c, route, multiplier t vs own factoring of n): 62/62;
  own MITM search over the p + 1 lines: KILL 62/62 (59 no integral tuple, 3 integral but out of box: N20163, N20237, N38727).
- 20 Part B rows not built at 21:40 (see partB_state.txt).

## Axioms (21:46)
- AxC43a: 47/47 standard (6 core + 41 rows), statements from instances.csv elaborate. AxC43b: 62/62 standard.
## Report: scratch/refuter/C43-2026-11-10-2137.md (verdict SURVIVES; findings: N758 unbuilt, p=3 origin sentence false
## in general, count 53 vs 49, no known-set control for the centred Z_3^r route, TomographyLast unlisted in C41).
- partb_ctrl stopped at 19 lines (all SURVIVES, 0 KILLED); stopped to free CPU.
