module

public import SignedDifferenceSets.TwistSelfConj

/-!
# Tests for `TwistSelfConj`

The kills need each hypothesis: on `K = ZMod 3 × ZMod 3`, `z = (2, …, 2, −2)` (sum `14`,
`≡ 2 mod 4`) and `d = 4 δ₀` meet everything `kill_mod_four` asks but the absolute sum
(`40 > 36`); `z = (4, …, 4, −4)` (sum `28`) and `d = 8 δ₀` meet everything `kill_mod_eight`
asks but the box (`12 > 10`). Controls: the `exists` rows N448 `(54, 38, 2)` and N931
`(72, 40, 4)` have a quotient onto `ZMod 2 × ZMod 3 × ZMod 3` but `k − λ = 36`, so
`2^(2j) ∣ k − λ` only for `j ≤ 1`: the mod-4 kill does not apply.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.TwistSelfConj

open TwistBox

/-- `(2, …, 2, −2)` on `ZMod 3 × ZMod 3`. -/
def z4 : ZMod 3 × ZMod 3 → ℤ := fun h => if h = (2, 2) then -2 else 2

/-- `4 δ₀`. -/
def d4 : ZMod 3 × ZMod 3 → ℤ := fun h => if h = 0 then 4 else 0

example : (∀ h, z4 h ≡ z4 0 [ZMOD 4]) ∧ (∀ h, d4 h ≡ d4 0 [ZMOD 4]) ∧
    (∑ h, z4 h) * (∑ h, z4 h) = 196 ∧ (∑ h, d4 h) * (∑ h, d4 h) = 16 ∧
    ∑ h, (|z4 h + d4 h| + |z4 h - d4 h|) = 40 := by
  decide

/-- `(4, …, 4, −4)`. -/
def z8 : ZMod 3 × ZMod 3 → ℤ := fun h => if h = (2, 2) then -4 else 4

/-- `8 δ₀`. -/
def d8 : ZMod 3 × ZMod 3 → ℤ := fun h => if h = 0 then 8 else 0

example : (∀ h, z8 h ≡ z8 0 [ZMOD 8]) ∧ (∀ h, d8 h ≡ d8 0 [ZMOD 8]) ∧
    (∑ h, z8 h) * (∑ h, z8 h) = 784 ∧ (∑ h, d8 h) * (∑ h, d8 h) = 64 ∧
    (∀ h, |z8 h + d8 h| ≤ 12 ∧ |z8 h - d8 h| ≤ 12) ∧ ¬ (∀ h, |z8 h + d8 h| ≤ 10) := by
  decide

example : ¬ (2 : ℤ) ^ (2 * 2) ∣ 38 - 2 ∧ ¬ (2 : ℤ) ^ (2 * 2) ∣ 40 - 4 := by decide

end SignedDifferenceSets.Tests.TwistSelfConj
