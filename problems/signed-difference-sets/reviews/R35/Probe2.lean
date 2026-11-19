import SignedDifferenceSets.MaCombRows

/-! Refuter probe: C29 on CW(195, 100) = SDS(195, 100, 0) in ℤ₁₉₅, with N9200's certificate. -/

open SignedDifferenceSets

theorem cw195_100_not_hasSDS : ¬ HasSDS (ZMod 195) 100 0 :=
  MaCombCert.not_hasSDS (w := ⟨0, [195], 100, 0⟩)
    (c := ⟨5, 1, 2, 2, 1, [13], [[1], [1]], [[26], [40]], [(2, 6, 1)]⟩) (by decide +kernel) _

#print axioms cw195_100_not_hasSDS

/-- Control: CW(52, 36) exists (AGZ Table 11); N6822-style certificates on ℤ₅₂ → ℤ₂ × ℤ₁₃ (or ℤ₄ × ℤ₁₃) are refused. -/
example : ∀ iq ∈ List.range 30, ∀ jq ∈ List.range 3,
    ¬ (⟨2, 1, 6, 2, 1, [13], [[1], [1]], [[13], [40]], [(3, iq, jq)]⟩ : MaCombCert).Kills ⟨0, [52], 36, 0⟩ := by
  decide +kernel
