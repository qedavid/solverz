import SignedDifferenceSets.MaEdgeRows
open SignedDifferenceSets

set_option maxRecDepth 100000 in
example : List.length MaEdgeRows.maEdgeRows = 151 := by decide +kernel

-- non-vacuity: CW(4,4) = (1, 1, 1, -1) on ZMod 4 meets every hypothesis (p = 2, r = 2, K = ZMod 1, c = 1)
def cw44 (x : ZMod 4) : SignType := if x = 3 then -1 else 1
theorem cw44_sds : IsSDS 4 0 cw44 := by unfold IsSDS cw44; decide
def phi44 : ZMod 4 →+ ZMod (2 * 2) × ZMod 1 := AddMonoidHom.prod (AddMonoidHom.id _) 0
example : (2 : ℤ) ∣ 0 * (1 : ℕ) :=
  IsSDS.dvd_lam_mul_of_ma (p := 2) (r := 2) (i := 1) (e := 2) (b := 1) (c := 1) (hp := ⟨Nat.prime_two⟩)
    (φ := phi44) (by intro y; exact ⟨y.1, by ext <;> simp [phi44]; exact Subsingleton.elim _ _⟩)
    (by simp) (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (MaRows.cycloFacts_of_mem_maPairs (pr := (2, 2)) (by decide)) cw44_sds (g := ((1 : ZMod 2), (0 : ZMod 1)))
    (by decide)
