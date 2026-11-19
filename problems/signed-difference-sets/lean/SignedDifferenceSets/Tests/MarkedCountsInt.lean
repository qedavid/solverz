module

public import SignedDifferenceSets.MarkedCountsInt
public import SignedDifferenceSets.Answer.N19

/-!
# Tests for C7's integer counts

Controls where integer counts exist, so the search must find them: N27692 itself with `k`
lowered to 304 (its best integer vector; 305 fails), and the rows N19 and N1640, where sets
exist: C5's data is valid there, yet `CountsKill` fails. On N19 the counts of the known set's
coset sums meet `CountsOk`.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

-- N27692, `s' = 228`, `t₀ = 0`: `{0 ↦ 1, 3 ↦ 1, 6 ↦ 15, 9 ↦ 15}` has 304 marked, none more.
example : CountsOk (classVals 3 0 10)
    (fun x => if x = 0 ∨ x = 3 then 1 else if x = 6 ∨ x = 9 then 15 else 0)
    32 228 1764 10 304 := by
  constructor <;> decide +kernel
example : anyCounts 10 (orderVals 228 (classVals 3 0 10)) 32 228 1764 304 = true := by
  decide +kernel
example : anyCounts 10 (orderVals 228 (classVals 3 0 10)) 32 228 1764 305 = false := by
  decide +kernel

-- N19 exists (C₃ × C₆ → C₂, `p = 3`): valid data, but the integer test does not kill it.
example : (⟨3, 1, 1, [1, 2], 9⟩ : ScCert).Valid ⟨19, [3, 6], 13, 4⟩ := by
  unfold ScCert.Valid; decide +kernel
example : ¬ (⟨3, 1, 1, [1, 2], 9⟩ : ScCert).CountsKill ⟨19, [3, 6], 13, 4⟩ := by
  decide +kernel

-- N1640 exists (C₉₁ → C₁₃, `p = 2`, `q = 4`): valid data, not killed.
example : (⟨2, 2, 6, [13], 74⟩ : ScCert).Valid ⟨1640, [91], 76, 60⟩ := by
  unfold ScCert.Valid; decide +kernel
example : ¬ (⟨2, 2, 6, [13], 74⟩ : ScCert).CountsKill ⟨1640, [91], 76, 60⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
-- N19's set (O100): its coset sums 6, 3 on C₂ meet `CountsOk` (sum 9, squares 45, 17 ≥ 13).
example : CountsOk (classVals 3 0 9)
    (countOf (contract (quot [3, 6] [1, 2] (by decide)) Answer.N19.sds)) 2 9 45 9 13 := by
  constructor <;> decide +kernel

end SignedDifferenceSets.Tests
