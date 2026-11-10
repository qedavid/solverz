import SignedDifferenceSets.Tests.PairSearch

/-! Refuter mutations for C37: each `example` marked FAIL must fail; PASS must pass. -/

open SignedDifferenceSets PairCheck PairRows.N464

-- FAIL: on N449's halved parameters a pair exists under this candidate, so zSearch is false.
example : zSearch 33 [1, 2, 0] 9 9 (rots tList) [[-1, 1, 0, 2, 1, 0, 2, 1, 0]] = true := by
  decide +kernel

-- PASS: group 19's front has exactly 15 nodes (the last cut), so dropping the last slice leaves a gap.
example : (zFront 37 [1, 0] 13 keys19 grp19).length = 15 := by decide +kernel

-- FAIL: a tighter front bound than the last cut.
example : (zFront 37 [1, 0] 13 keys19 grp19).length ≤ 14 := by decide +kernel

-- FAIL: N464's search with the T weight changed to 8 is not what `slices` proves; the
-- claim that it equals the proved one must not be provable by rfl-evaluation if T matters.
-- (sanity on the leaf: the Z-only search with no T check at all, tw = 0 lets every Z leaf pass)
example : zSearch 37 [1, 0] 13 0 (rots tList) grp19 = true := by decide +kernel
