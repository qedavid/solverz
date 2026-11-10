import SignedDifferenceSets.FieldDescentChain
import SignedDifferenceSets.Check

/-! Refuter probe for C35: non-vacuity with an odd prime `q = 5 ∣ n` at a `p = 2` step, on a known
set (O98, SDS(104, 29, 4) in `C₁₀₄`, quotient `ZMod 8`, chain `8 → 4`, witness `t = 5 = 5¹`). -/

open SignedDifferenceSets

def o98 : ZMod 104 → SignType := fun x =>
  if x.val ∈ [13, 39, 65, 91] then -1
  else if x.val ∈ [1, 3, 5, 6, 8, 9, 15, 17, 21, 22, 25, 28, 30, 36, 40, 45, 46, 63, 64, 68, 75, 76,
    78, 85, 96] then 1 else 0

theorem o98_isSDS : IsSDS 29 4 o98 := by decide +kernel

def q8 : ZMod 104 →+ ZMod 8 := (ZMod.castHom (show 8 ∣ 104 by norm_num) (ZMod 8)).toAddMonoidHom

theorem q8_surjective : Function.Surjective q8 :=
  ZMod.castHom_surjective (show 8 ∣ 104 by norm_num)

theorem o98_chain : (Nat.totient 8 : ℤ) * ((29 : ℕ) - (4 : ℤ)) ≤
    ((8 : ℕ) : ℤ) * (([2].foldl (· / ·) 8 : ℕ) : ℤ) * ((13 : ℕ) : ℤ) ^ 2 :=
  IsSDS.totient_mul_le_of_chain o98_isSDS (m := 8) (by norm_num) q8 q8_surjective
    (by simp [ZMod.card]) (by norm_num) [2]
    (StepsOk.descentChain (by decide) 8 [⟨2, [⟨5, 5, 0, 1⟩]⟩] (by decide +kernel))

/-- The same step is refused for `n = 9` (`q = 3`, `⟨3⟩ = {1, 3}` mod 8 does not contain 5). -/
example : ∀ t < 8, ¬ (t.Coprime 8 ∧ t ≡ 1 + 8 / 2 [MOD 8] ∧ ∃ e < 2, t ≡ 3 ^ e [MOD 8]) := by
  decide

#print axioms o98_chain
