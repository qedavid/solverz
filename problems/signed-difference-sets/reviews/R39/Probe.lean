import SignedDifferenceSets.FieldDescentRows
import SignedDifferenceSets.Check

/-! Refuter probe for C32 (P18 M1): statement types, axioms, row theorems as `¬ HasSDS`, non-vacuity. -/

open SignedDifferenceSets

#check @IsSDS.totient_mul_le_of_descent
#check @IsSDS.totient_mul_le_of_descent'
#check @FieldDescent.totient_mul_le_of_descent_aux
#check @FieldDescentCert.not_hasSDS
#check @fieldDescentRows_not_hasSDS
#print FieldDescentCert.Kills

#print axioms IsSDS.totient_mul_le_of_descent
#print axioms IsSDS.totient_mul_le_of_descent'
#print axioms FieldDescent.totient_mul_le_of_descent_aux
#print axioms FieldDescentCert.not_hasSDS
#print axioms fieldDescentRows_kill
#print axioms fieldDescentRows_not_hasSDS

/-- The row theorem on N10381 is literally `¬ HasSDS (ZMod 207) 118 1`. -/
example : ¬ HasSDS (ZMod 207) 118 1 :=
  fieldDescentRows_not_hasSDS (x := (⟨10381, [207], 118, 1⟩, ⟨207, 3, [1], [1]⟩))
    (by decide +kernel) _

/-- N54948 on `C₃ × C₁₄₇`: literally `¬ HasSDS (ZMod 3 × ZMod 147) 364 21`. -/
example : ¬ HasSDS (ZMod 3 × ZMod 147) 364 21 :=
  fieldDescentRows_not_hasSDS (x := (⟨54948, [3, 147], 364, 21⟩, ⟨147, 7, [49, 3], [1, 33]⟩))
    (by decide +kernel) _

/-- N69420, the last row. -/
example : ¬ HasSDS (ZMod 495) 482 41 :=
  fieldDescentRows_not_hasSDS (x := (⟨69420, [495], 482, 41⟩, ⟨495, 3, [1], [1]⟩))
    (by decide +kernel) _

/-- Non-vacuity: SDS(9, 9, 5) on `C₉` (n = 4, q = 2 with `1 + 3 = 2²`), the theorem applies. -/
def d9 : ZMod 9 → SignType := fun x => if x = 8 then 1 else -1

theorem d9_isSDS : IsSDS 9 5 d9 := by decide +kernel

example : (Nat.totient 9 : ℤ) * ((9 : ℕ) - (5 : ℤ)) ≤ 9 * (9 / 3) * 1 ^ 2 :=
  d9_isSDS.totient_mul_le_of_descent (m := 9) (c := 1) (p := 3) (by norm_num)
    (AddMonoidHom.id _) Function.surjective_id (by simp) (by norm_num) Nat.prime_three
    (by norm_num) (by norm_num) fun q hq hqn => by
      have h4 : q ∣ 2 ^ 2 := by
        have : (q : ℤ) ∣ 4 := by simpa using hqn
        exact_mod_cast this
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h4)
      exact ⟨2, by norm_num [Nat.ModEq]⟩

/-- A wrong `p`-condition must not prove a false kill: `p = 2` on 207 is rejected (sanity). -/
example : ¬ FieldDescentCert.Kills ⟨10381, [207], 118, 1⟩ ⟨207, 2, [1], [1]⟩ := by decide +kernel
