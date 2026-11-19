module

public import SignedDifferenceSets.FieldDescent

/-!
# Tests for P18 M1 (one step of field descent)

The step kills N10381 (207, 118, 1) in `C₂₀₇`. It does not fire where the bound would kill but a
prime `q ∣ n` misses the congruence: N627 (63, 38, 1), N52 (25, 16, 2). Nor on rows with sets,
where the congruence holds but the bound does not: N63320 (475, 241, 120), N3408 (126, 96, 32),
N31722 (343, 54, 5).
-/

@[expose] public section

namespace SignedDifferenceSets

/-- N10381: `m = 207 = 3² · 23`, `p = 3`, `n = 117`: `70 ≡ 1 (mod 23)`, `70 ≡ 13¹¹ (mod 207)`, and
`207 · 69 = 14283 < φ(207) · 117 = 15444`. -/
example : ¬ HasSDS (ZMod 207) 118 1 :=
  FieldDescentCert.not_hasSDS (w := ⟨10381, [207], 118, 1⟩) (c := ⟨207, 3, [1], [1]⟩)
    (by decide +kernel) _

/-- N627: `63 · 21 = 1323 < φ(63) · 37 = 1332`, but `22` is no power of `37` mod `63`. -/
example : ¬ FieldDescentCert.Kills ⟨627, [63], 38, 1⟩ ⟨63, 3, [1], [1]⟩ := by decide +kernel

/-- N52 (no set): `25 · 5 < φ(25) · 14`, but `6` is no power of `7` mod `25`. -/
example : ¬ FieldDescentCert.Kills ⟨52, [25], 16, 2⟩ ⟨25, 5, [1], [1]⟩ := by decide +kernel

/-- The step needs an odd prime: `p = 2` is rejected on N10381's quotient. -/
example : ¬ FieldDescentCert.Kills ⟨10381, [207], 118, 1⟩ ⟨207, 2, [1], [1]⟩ := by decide +kernel

/-- N63320 exists: `96 ≡ 11¹² (mod 475)`, but `475 · 95 = 45125 ≥ φ(475) · 121 = 43560`. -/
example : ¬ FieldDescentCert.Kills ⟨63320, [475], 241, 120⟩ ⟨475, 5, [1], [1]⟩ := by
  decide +kernel

/-- N3408 exists: on `C₁₈`, `c = 7`, `18 · 6 · 49 ≥ φ(18) · 64`. -/
example : ¬ FieldDescentCert.Kills ⟨3408, [126], 96, 32⟩ ⟨18, 3, [1], [1]⟩ := by decide +kernel

/-- N31722 exists: on `C₄₉` (from `C₇ × C₄₉`), `c = 7`, `49 · 7 · 49 ≥ φ(49) · 49`. -/
example : ¬ FieldDescentCert.Kills ⟨31722, [7, 49], 54, 5⟩ ⟨49, 7, [0, 1], [0, 1]⟩ := by
  decide +kernel

end SignedDifferenceSets
