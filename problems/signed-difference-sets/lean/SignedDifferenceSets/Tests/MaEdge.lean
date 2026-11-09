module

public import SignedDifferenceSets.MaEdgeRows

/-!
# Tests for C33's row check (`MaEdge`, `MaEdgeRows`)

Row N2847 (`SDS(117, 53, 17)` in `ℤ₁₁₇`, `k − λ = 36`, `p = 3`, `ℤ₁₁₇ → ℤ₉`, `c = 13`) is killed:
`3 ∤ 17 · 13`. Certificates without `b ≥ 1` or with `r = 1` are refused. The existing sets
`SDS(80, 44, 8)` and `SDS(80, 72, 36)` in `ℤ₈₀` (N1181, N1216, Gordon's table),
`SDS(312, 300, 200)` in `ℤ₃₁₂` (N26075, checked in Lean) and `SDS(72, 40, 4)` in `ℤ₃ × ℤ₂₄`
(N933, checked in Lean) have a cyclic Sylow `2`-subgroup of order at least `4` and `4 ∣ k − λ`;
`2 ∣ λ c` there, so no certificate on `ℤ₄`, `ℤ₈` or `ℤ₁₆` kills them.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

/-- N2847 is killed on `ℤ₉`. -/
example : (⟨3, 3, 1, 2, 1, [1], [[1], [1]], [[1], [0]]⟩ : MaEdgeCert).Kills
    ⟨2847, [117], 53, 17⟩ := by decide +kernel

/-- `b = 0` is refused. -/
example : ¬ (⟨3, 3, 1, 2, 0, [1], [[1], [1]], [[1], [0]]⟩ : MaEdgeCert).Kills
    ⟨2847, [117], 53, 17⟩ := by decide +kernel

/-- `r = 1` (`ℤ₃`, no nonzero shift on `ℤ₁`) is refused. -/
example : ¬ (⟨3, 1, 1, 2, 1, [1], [[1], [1]], [[1], [0]]⟩ : MaEdgeCert).Kills
    ⟨2847, [117], 53, 17⟩ := by decide +kernel

/-- N1181, N1216: `ℤ₈₀ → ℤ₄, ℤ₈, ℤ₁₆` are refused. -/
example : ∀ r ∈ [2, 4, 8], ∀ w ∈ [(⟨1181, [80], 44, 8⟩ : Row), ⟨1216, [80], 72, 36⟩],
    ¬ (⟨2, r, 1, 2, 1, [1], [[1], [1]], [[1], [0]]⟩ : MaEdgeCert).Kills w := by decide +kernel

/-- N26075: `ℤ₃₁₂ → ℤ₄, ℤ₈` are refused. -/
example : ∀ r ∈ [2, 4],
    ¬ (⟨2, r, 1, 2, 1, [1], [[1], [1]], [[1], [0]]⟩ : MaEdgeCert).Kills
      ⟨26075, [312], 300, 200⟩ := by
  decide +kernel

/-- N933: `ℤ₃ × ℤ₂₄ → ℤ₄, ℤ₈` are refused. -/
example : ∀ r ∈ [2, 4],
    ¬ (⟨2, r, 1, 2, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]]⟩ : MaEdgeCert).Kills
      ⟨933, [3, 24], 40, 4⟩ := by
  decide +kernel

end SignedDifferenceSets.Tests
