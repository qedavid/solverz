module

public import SignedDifferenceSets.MaDividedCounts

/-!
# Tests for the value-count kills below a Ma quotient

The count search on hand-made demands: the counts of `(2, 1, 1, 1, 1, 0, 0, 0)` are found, and
none once the absolute-sum bound or the parity is off. Controls where an SDS exists, so every
hypothesis of `MaCountCert` holds and only the count search can tell: N131 (`SDS(32,20,4)` in
`C₂ × C₁₆`) at level 1 and level 2 (`p = 2`), N19 (`SDS(18,13,4)` in `C₃ × C₆`) at `p = 3`; none
is killed. Wrong certificates are refused: a killed row's certificate with a changed `λ`, sum, level
or bound.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

example : magVals 3 = [3, -3, 2, -2] := by decide

-- `(2, 1, 1, 1, 1, 0, 0, 0)`: 8 values, sum 6, square sum 8, absolute sum 6.
example : anyCountsMag 2 8 6 8 10 = true := by decide +kernel
example : anyCountsMag 2 8 6 8 6 = true := by decide +kernel
-- absolute sum at most 5 < |6|: none
example : anyCountsMag 2 8 6 8 5 = false := by decide +kernel
-- square sum 9 and sum 6 differ in parity: none
example : anyCountsMag 2 8 6 9 10 = false := by decide +kernel

-- N131 exists: level 2 (`ZMod 16 → ZMod 4`, `c = 2`) and level 1 (`ZMod 16 → ZMod 8`): valid,
-- not killed.
example : (⟨2, 4, 1, 4, 2, 2, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], 5, 3, 3⟩ :
    MaCountCert).Valid ⟨131, [2, 16], 20, 4⟩ := by decide +kernel
example : ¬ (⟨2, 4, 1, 4, 2, 2, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], 5, 3, 3⟩ :
    MaCountCert).Kills ⟨131, [2, 16], 20, 4⟩ := by decide +kernel
example : (⟨2, 8, 1, 4, 2, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], 10, 8, 6⟩ :
    MaCountCert).Valid ⟨131, [2, 16], 20, 4⟩ := by decide +kernel
example : ¬ (⟨2, 8, 1, 4, 2, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], 10, 8, 6⟩ :
    MaCountCert).Kills ⟨131, [2, 16], 20, 4⟩ := by decide +kernel

-- N19 exists: `p = 3`, level 1 (`C₃ × C₆ → C₃ × C₂ → C₂`), valid, not killed.
example : (⟨3, 1, 1, 2, 1, 1, [2], [[1], [0, 1]], [[1], [0, 1]], 4, 5, 3⟩ : MaCountCert).Valid
    ⟨19, [3, 6], 13, 4⟩ := by decide +kernel
example : ¬ (⟨3, 1, 1, 2, 1, 1, [2], [[1], [0, 1]], [[1], [0, 1]], 4, 5, 3⟩ : MaCountCert).Kills
    ⟨19, [3, 6], 13, 4⟩ := by decide +kernel

-- N33881's certificate kills it; changed `λ`, sum, level, bound or level 3 are refused.
example : (⟨2, 4, 5, 4, 2, 2, [11], [[0, 1], [0, 1]], [[0, 33], [0, 144]], 40, 17, 19⟩ :
    MaCountCert).Kills ⟨33881, [2, 176], 160, 16⟩ := by decide +kernel
example : ¬ (⟨2, 4, 5, 4, 2, 2, [11], [[0, 1], [0, 1]], [[0, 33], [0, 144]], 40, 17, 19⟩ :
    MaCountCert).Valid ⟨33881, [2, 176], 160, 15⟩ := by decide +kernel
example : ¬ (⟨2, 4, 5, 4, 2, 2, [11], [[0, 1], [0, 1]], [[0, 33], [0, 144]], 40, 17, 17⟩ :
    MaCountCert).Valid ⟨33881, [2, 176], 160, 16⟩ := by decide +kernel
example : ¬ (⟨2, 4, 5, 4, 2, 1, [11], [[0, 1], [0, 1]], [[0, 33], [0, 144]], 40, 17, 19⟩ :
    MaCountCert).Valid ⟨33881, [2, 176], 160, 16⟩ := by decide +kernel
example : ¬ (⟨2, 4, 5, 4, 2, 2, [11], [[0, 1], [0, 1]], [[0, 33], [0, 144]], 39, 17, 19⟩ :
    MaCountCert).Valid ⟨33881, [2, 176], 160, 16⟩ := by decide +kernel
example : ¬ (⟨2, 4, 5, 4, 2, 3, [11], [[0, 1], [0, 1]], [[0, 33], [0, 144]], 40, 17, 19⟩ :
    MaCountCert).Valid ⟨33881, [2, 176], 160, 16⟩ := by decide +kernel

end SignedDifferenceSets.Tests
