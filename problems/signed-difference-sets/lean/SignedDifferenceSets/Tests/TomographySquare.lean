module

public import SignedDifferenceSets.TomographySquare

/-!
# Tests for `TomographySquare`

`congr_of_autocorr_sq` on `(4, 1, 1)` (autocorrelation `9 [g = 0] + 9` on `ZMod 3`) and on
`(−1, 4, 4, 4, 4)` (`25 [g = 0] + 40` on `ZMod 5`); `modEq_succ_of_const` on `(1, 4, 4)` (`q = 3`,
`p = 3`), while the other sign `(5, 2, 2)` breaks its bound; a vector that is not constant mod `p`
has no such autocorrelation. Controls: the `exists` rows with `k − λ = p²` and a `ZMod p × ZMod p`
quotient (N2, N19, N61, N170, N3243, N31722) all fail the box `c p < q + p − 1`, so
`not_hasSDS_grp_sq` does not apply to them.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.TomographySquare

open Tomography

/-- `3` is prime. -/
local instance fact3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- `5` is prime. -/
local instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `(4, 1, 1)`: `9 [g = 0] + 9`. -/
def y3 : ZMod 3 → ℤ := ![4, 1, 1]

theorem y3_autocorr (g : ZMod 3) :
    ∑ t, y3 t * y3 (t + g) = (if g = 0 then ((3 : ℕ) : ℤ) ^ 2 else 0) + 9 := by
  revert g; decide

example (t : ZMod 3) : y3 t ≡ y3 0 [ZMOD 3] := congr_of_autocorr_sq y3 9 y3_autocorr t

/-- `(−1, 4, 4, 4, 4)`: `25 [g = 0] + 40`. -/
def y5 : ZMod 5 → ℤ := ![-1, 4, 4, 4, 4]

theorem y5_autocorr (g : ZMod 5) :
    ∑ t, y5 t * y5 (t + g) = (if g = 0 then ((5 : ℕ) : ℤ) ^ 2 else 0) + 40 := by
  revert g; decide

example (t : ZMod 5) : y5 t ≡ y5 0 [ZMOD 5] := congr_of_autocorr_sq y5 40 y5_autocorr t

/-- `(1, 2, 0)`, not constant mod `3`: autocorrelation `5, 2, 2`, not `9 [g = 0] + μ`. -/
def z3 : ZMod 3 → ℤ := ![1, 2, 0]

example (μ : ℤ) : ¬ ∀ g : ZMod 3, ∑ t, z3 t * z3 (t + g) = (if g = 0 then 9 else 0) + μ := by
  intro h
  have h0 := h 0
  have h1 := h 1
  rw [show ∑ t, z3 t * z3 (t + 0) = 5 by decide] at h0
  rw [show ∑ t, z3 t * z3 (t + 1) = 2 by decide] at h1
  simp only [↓reduceIte, one_ne_zero] at h0 h1
  omega

/-- `(1, 4, 4) = (q + 1) − p δ₀` with `q = p = 3`. -/
def u3 : ZMod 3 → ℤ := ![1, 4, 4]

example : u3 0 ≡ 3 + 1 [ZMOD 3] :=
  modEq_succ_of_const u3 (q := 3) (f := 4) (by decide) (by decide) (by decide) (by decide)
    (by norm_num)

/-- The other sign `(5, 2, 2) = (q − 1) + p δ₀` has sum and square sum right but breaks
`f < q + p − 1`. -/
example : ∑ t, (![5, 2, 2] : ZMod 3 → ℤ) t = 3 * 3 ∧
    ∑ t, (![5, 2, 2] : ZMod 3 → ℤ) t * (![5, 2, 2] : ZMod 3 → ℤ) t = 3 * 3 ^ 2 + 3 * (3 - 1) ∧
    ¬ ∀ t, (![5, 2, 2] : ZMod 3 → ℤ) t < 3 + 3 - 1 := by
  decide

/-! ### Controls: the `exists` rows fail the box -/

/-- N2 `(9, 8, −1)`, `ZMod 3 × ZMod 3`: `p = 3`, `c = 1`, `s = 0`. -/
example : ¬ ((1 : ℤ) * 3 < 0 + 3 - 1) := by norm_num

/-- N19 `(18, 13, 4)`, `ZMod 3 × ZMod 6`: `c = 2`, `s = 9 = 3·3`. -/
example : (9 : ℤ) * 9 = 13 + 4 * (2 * 3 * 3 - 1) ∧ ¬ ((2 : ℤ) * 3 < 3 + 3 - 1) := by norm_num

/-- N61 `(27, 10, 1)`, `ZMod 3 × ZMod 3 × ZMod 3`: `c = 3`, `s = 6 = 3·2`. -/
example : (6 : ℤ) * 6 = 10 + 1 * (3 * 3 * 3 - 1) ∧ ¬ ((3 : ℤ) * 3 < 2 + 3 - 1) := by norm_num

/-- N170 `(36, 11, 2)`, `ZMod 6 × ZMod 6`: `c = 4`, `s = 9 = 3·3`. -/
example : (9 : ℤ) * 9 = 11 + 2 * (4 * 3 * 3 - 1) ∧ ¬ ((4 : ℤ) * 3 < 3 + 3 - 1) := by norm_num

/-- N3243 `(125, 28, 3)`, `ZMod 5 × ZMod 25`: `c = 5`, `s = 20 = 5·4`. -/
example : (20 : ℤ) * 20 = 28 + 3 * (5 * 5 * 5 - 1) ∧ ¬ ((5 : ℤ) * 5 < 4 + 5 - 1) := by norm_num

/-- N31722 `(343, 54, 5)`, `ZMod 7 × ZMod 49`: `c = 7`, `s = 42 = 7·6`. -/
example : (42 : ℤ) * 42 = 54 + 5 * (7 * 7 * 7 - 1) ∧ ¬ ((7 : ℤ) * 7 < 6 + 7 - 1) := by norm_num

end SignedDifferenceSets.Tests.TomographySquare
