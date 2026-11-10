import SignedDifferenceSets.MaDivided2

open SignedDifferenceSets

#print axioms Ma.dvd_contract_quot_sub
#print axioms IsSDS.false_of_maDivided2
#print axioms MaDiv2Cert.not_hasSDS
#check @IsSDS.false_of_maDivided2
#check @MaDiv2Cert.not_hasSDS

/-! Non-vacuity on an existing SDS: N131, SDS(32,20,4) in ZMod 2 × ZMod 16 (exists, Gordon Yes). -/
example : MaDiv2Cert.Valid ⟨131, [2, 16], 20, 4⟩
    ⟨2, 4, 1, 4, 2, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], [5, 4], 3, 2, 3⟩ := by decide +kernel
theorem hpos131 : ∀ m ∈ [4, 1], 0 < m := by decide
example : noVector (@Indexed.size (Grp [4, 1]) _ (Grp.indexed _ hpos131))
    (@Indexed.addIdx (Grp [4, 1]) _ (Grp.indexed _ hpos131)) (2 : ℕ) (3 : ℤ) (2 : ℤ) (5 : ℕ) 3 = false := by
  decide +kernel
example : noVector (@Indexed.size (Grp [4, 1]) _ (Grp.indexed _ hpos131))
    (@Indexed.addIdx (Grp [4, 1]) _ (Grp.indexed _ hpos131)) (2 : ℕ) (3 : ℤ) (2 : ℤ) (4 : ℕ) 3 = true := by
  decide +kernel
/-! Valid refuses: one bound only at p = 2, b = 1, a wrong λ. -/
example : ¬ MaDiv2Cert.Valid ⟨131, [2, 16], 20, 4⟩
    ⟨2, 4, 1, 4, 2, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], [5], 3, 2, 3⟩ := by decide +kernel
example : ¬ MaDiv2Cert.Valid ⟨131, [2, 16], 20, 4⟩
    ⟨2, 4, 1, 4, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], [5, 4], 3, 2, 3⟩ := by decide +kernel
example : ¬ MaDiv2Cert.Valid ⟨8944, [2, 96], 150, 4⟩
    ⟨2, 8, 1, 4, 2, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], [37, 36], 18, 9, 9⟩ := by decide +kernel

/-! N8944 re-proved here, stated without `HasSDS`/`Grp`. -/
theorem hpos8 : ∀ m ∈ [8, 1], 0 < m := by decide
theorem n8944_plain : ¬ ∃ D : ZMod 2 × ZMod 96 → SignType,
    (Finset.univ.filter fun x => D x ≠ 0).card = 150 ∧
      ∀ g : ZMod 2 × ZMod 96, g ≠ 0 → ∑ x, ((D x : ℤ) * (D (x + g) : ℤ)) = 6 :=
  MaDiv2Cert.not_hasSDS (w := ⟨8944, [2, 96], 150, 6⟩)
    (c := ⟨2, 8, 1, 4, 2, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], [37, 36], 18, 9, 9⟩)
    (by decide +kernel) hpos8 _
    (fun k' hk' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
      rcases hk' with rfl | rfl <;> decide +kernel)
#print axioms n8944_plain
