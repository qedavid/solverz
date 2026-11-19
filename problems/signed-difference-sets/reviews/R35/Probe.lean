import SignedDifferenceSets.MaCombRows

/-! Refuter probes for C29: axioms, statement shapes, and certificates that must be refused. -/

open SignedDifferenceSets SignedDifferenceSets.MaCombRows

#print axioms maCombRule
#print axioms MaCombCert.not_hasSDS
#print axioms n6822_not_hasSDS
#print axioms n9200_not_hasSDS
#print axioms n44532_not_hasSDS
#print axioms n44533_not_hasSDS
#print axioms n44562_not_hasSDS
#print axioms n44563_not_hasSDS
#print axioms n44662_not_hasSDS
#print axioms n44663_not_hasSDS
#print axioms n44752_not_hasSDS
#print axioms n44753_not_hasSDS
#print axioms n58644_not_hasSDS

-- The statements as the kernel sees them (instances must be the standard ones).
#check (n44533_not_hasSDS : ¬ HasSDS (ZMod 4 × ZMod 100) 235 10)
#check (n6822_not_hasSDS : ¬ @HasSDS (ZMod 170) (ZMod.commRing 170).toAddCommGroup (ZMod.fintype 170) 146 2)

/-- N1181 SDS(80,44,8) exists (Gordon). On `ℤ₈₀ → ℤ₈ × ℤ₅` with `p = 2`, `b = 1`, `c = 2`, `q = 3` would give
`p^b Q = 6 > 4 = 2c`; it must be refused because `3^i ≢ −1 mod 8` for every `i`. -/
def certN1181j3 (qs : List (ℕ × ℕ × ℕ)) : MaCombCert := ⟨2, 4, 2, 2, 1, [5], [[1], [1]], [[25], [16]], qs⟩

example : (certN1181j3 []).Valid ⟨1181, [80], 44, 8⟩ ∧ ¬ (certN1181j3 []).Kills ⟨1181, [80], 44, 8⟩ := by
  decide +kernel

example : ∀ iq ∈ List.range 41, ¬ (certN1181j3 [(3, iq, 1)]).Kills ⟨1181, [80], 44, 8⟩ := by decide +kernel

/-- The same for N1216 SDS(80,72,36) (exists). -/
example : ∀ iq ∈ List.range 41, ¬ (certN1181j3 [(3, iq, 1)]).Kills ⟨1216, [80], 72, 36⟩ := by decide +kernel

/-- N9200 with a wrong group size in the row (v = 390) must not be accepted by the 195-certificate. -/
example : ¬ (⟨5, 1, 2, 2, 1, [13], [[1], [1]], [[26], [40]], [(2, 6, 1)]⟩ : MaCombCert).Kills
    ⟨9200, [390], 115, 15⟩ := by decide +kernel

/-- N6822 with b = 3 (p^6 ∤ 144) is refused; with e = 4, b = 2 it kills. -/
example : ¬ (⟨2, 1, 4, 4, 3, [17], [[1], [1]], [[17], [18]], [(3, 8, 1)]⟩ : MaCombCert).Kills
    ⟨6822, [170], 146, 2⟩ := by decide +kernel
example : ¬ (⟨2, 1, 4, 6, 3, [17], [[1], [1]], [[17], [18]], [(3, 8, 1)]⟩ : MaCombCert).Kills
    ⟨6822, [170], 146, 2⟩ := by decide +kernel

/-- `q = 3` with `j_q = 2` (3⁴ ∤ 225) refused on N44532. -/
example : ¬ (⟨5, 5, 1, 2, 1, [2, 2], [[0, 1], [1], [0, 1]], [[0, 26], [1], [0, 25]], [(3, 10, 2)]⟩ :
    MaCombCert).Kills ⟨44532, [2, 200], 235, 10⟩ := by decide +kernel
