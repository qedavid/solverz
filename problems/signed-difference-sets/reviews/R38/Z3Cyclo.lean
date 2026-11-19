import SignedDifferenceSets.Check

/-! E14 check 3: P2's cyclotomic (25,12,1) set, built from GF(25) = F₅[w]/(w² − 2), g = 1 + 2w. -/

namespace E14

/-- Multiplication in F₅[w]/(w² − 2) on pairs (a, b) = a + b w. -/
def mulW (x y : ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 :=
  (x.1 * y.1 + 2 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- g ^ i for g = 1 + 2w. -/
def gpow : ℕ → ZMod 5 × ZMod 5
  | 0 => (1, 0)
  | i + 1 => mulW (gpow i) (1, 2)

/-- g is primitive: its first 24 powers are distinct (and nonzero). -/
theorem g_primitive : ((List.range 24).map gpow).Nodup ∧ (0, 0) ∉ (List.range 24).map gpow := by decide

/-- The eighth-power class C_i = g^i ⟨g^8⟩. -/
def cls (i : ℕ) : List (ZMod 5 × ZMod 5) := [gpow i, gpow (i + 8), gpow (i + 16)]

/-- D = C₀ ∪ C₁ ∪ C₅ marked +1, C₃ marked −1. -/
def sds : ZMod 5 × ZMod 5 → SignType := fun p =>
  if p ∈ cls 0 ++ cls 1 ++ cls 5 then 1 else if p ∈ cls 3 then -1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem isSDS : SignedDifferenceSets.IsSDS 12 1 sds := by decide

theorem hasSDS : SignedDifferenceSets.HasSDS (ZMod 5 × ZMod 5) 12 1 := ⟨sds, isSDS⟩

#print axioms hasSDS
#print axioms g_primitive

end E14
