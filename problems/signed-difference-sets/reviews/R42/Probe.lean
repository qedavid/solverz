import SignedDifferenceSets.MaDividedRows.N38250
import SignedDifferenceSets.MaDividedRows.N11253
open SignedDifferenceSets

#print axioms SignedDifferenceSets.Ma.dvd_contract_quot
#print axioms SignedDifferenceSets.false_of_noVectorQ'
#print axioms SignedDifferenceSets.IsSDS.false_of_maDivided
#print axioms SignedDifferenceSets.MaDivCert.not_hasSDS
#print axioms SignedDifferenceSets.MaDividedRows.N38250.not_hasSDS
#print axioms SignedDifferenceSets.MaDividedRows.N11253.not_hasSDS
#check @SignedDifferenceSets.IsSDS.false_of_maDivided
#check @SignedDifferenceSets.MaDivCert.not_hasSDS

-- the row theorems written out, without HasSDS
example : ¬ ∃ D : ZMod 5 × ZMod 75 → SignType,
    (Finset.univ.filter fun x => D x ≠ 0).card = 26 ∧
      ∀ g : ZMod 5 × ZMod 75, g ≠ 0 → ∑ x, ((D x : ℤ) * (D (x + g) : ℤ)) = 1 :=
  MaDividedRows.N38250.not_hasSDS
example : ¬ ∃ D : ZMod 6 × ZMod 36 → SignType,
    (Finset.univ.filter fun x => D x ≠ 0).card = 40 ∧
      ∀ g : ZMod 6 × ZMod 36, g ≠ 0 → ∑ x, ((D x : ℤ) * (D (x + g) : ℤ)) = 4 :=
  MaDividedRows.N11253.not_hasSDS

-- non-vacuity: an existing SDS (N62, SDS(27,10,1) in ZMod 3 × ZMod 9, object O8) meets every cert hypothesis,
-- and its divided search is `false` (a vector exists), so only the search separates kills from existing sets
example : MaDivCert.Valid ⟨62, [3, 9], 10, 1⟩ ⟨3, 3, 1, 2, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], 2, 2, 1, 2⟩ := by
  decide +kernel
theorem hpos31 : ∀ m ∈ [3, 1], 0 < m := by decide
example : noVector (@Indexed.size (Grp [3, 1]) _ (Grp.indexed _ hpos31))
    (@Indexed.addIdx (Grp [3, 1]) _ (Grp.indexed _ hpos31)) ((3 : ℕ) : ℤ) 2 1 (2 : ℕ) 2 = false := by
  decide +kernel
-- Valid refuses: k' too small (k < p (k' + 2) fails), b = 0, p = 2 (N62 data with p := 2 is not even prime-consistent)
example : ¬ MaDivCert.Valid ⟨62, [3, 9], 10, 1⟩ ⟨3, 3, 1, 2, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], 0, 2, 1, 2⟩ := by
  decide +kernel
example : ¬ MaDivCert.Valid ⟨62, [3, 9], 10, 1⟩ ⟨3, 3, 1, 2, 0, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], 2, 2, 1, 2⟩ := by
  decide +kernel
-- N38250's cert with a wrong λ (2 instead of 1) is refused
example : ¬ MaDivCert.Valid ⟨38250, [5, 75], 26, 2⟩ ⟨5, 5, 1, 2, 1, [3], [[0, 1], [0, 1]], [[0, 51], [0, 25]], 4, 2, 1, 4⟩ := by
  decide +kernel
