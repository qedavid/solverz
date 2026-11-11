module

public import SignedDifferenceSets.TwistBox

/-!
# Self-conjugacy on the twist (I23): `(90, 18, 2)` and `(90, 72, 8)`

On `φ : G →+ ZMod 2 × K` onto (fibres `c`) let `z` be the contraction to `K` and `d` its twist by
the character of `ZMod 2`. Both have autocorrelation `n [g = 0] + μ` (`n = k − λ`), so when `2` is
self-conjugate on `K` (`2^i h = −h`, `|K|` odd) and `2^(2j) ∣ n`, both are constant mod `2^j`
(C5, `congr_pow_of_autocorr`); `(Σ z)² = s²`, `(Σ d)² = n`, `z ± d = 2 W(e, ·)` with `|W| ≤ c` and
`Σ |W| ≤ k` (`twist_facts`). On `K = ZMod 3 × ZMod 3`, `|G| = 90`:
`(18, 2)`: `n = 16`, mod 4: `z ≡ 2`, `d ≡ 0`, some `|d| ≥ 4`, so `Σ (|z + d| + |z − d|) ≥ 40 > 2k`;
`(72, 8)`: `n = 64`, mod 8: `z ≡ 4`, `d ≡ 0`, some `|d| ≥ 8`, so some `|z ± d| ≥ 12 > 2c`.
-/

@[expose] public section

namespace SignedDifferenceSets.TwistBox

open KleinTomography

section Facts

variable {G K : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- The facts the kills use: `z` and `d` constant mod `2^j`, their squared sums, the box and the
absolute sum of `z ± d = 2 W(e, ·)`. -/
theorem twist_facts {k : ℕ} {lam s : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ ZMod 2 × K) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * (2 * Fintype.card K))
    (hs : s * s = k + lam * ((Fintype.card G : ℤ) - 1)) {i j : ℕ} (hi : 0 < i)
    (hc : ∀ h : K, 2 ^ i • h = -h) (hK : (Fintype.card K : ZMod 2) ≠ 0) (hK1 : ∃ g : K, g ≠ 0)
    (hn : (2 : ℤ) ^ (2 * j) ∣ k - lam) :
    (∀ h, contract (baseOf φ) D h ≡ contract (baseOf φ) D 0 [ZMOD 2 ^ j]) ∧
    (∀ h, twist (epsOf φ) (baseOf φ) D h ≡ twist (epsOf φ) (baseOf φ) D 0 [ZMOD 2 ^ j]) ∧
    (∑ h, contract (baseOf φ) D h) * (∑ h, contract (baseOf φ) D h) = s * s ∧
    (∑ h, twist (epsOf φ) (baseOf φ) D h) * (∑ h, twist (epsOf φ) (baseOf φ) D h) = k - lam ∧
    (∀ h, |contract (baseOf φ) D h + twist (epsOf φ) (baseOf φ) D h| ≤ 2 * c ∧
      |contract (baseOf φ) D h - twist (epsOf φ) (baseOf φ) D h| ≤ 2 * c) ∧
    ∑ h, (|contract (baseOf φ) D h + twist (epsOf φ) (baseOf φ) D h| +
      |contract (baseOf φ) D h - twist (epsOf φ) (baseOf φ) D h|) ≤ 2 * k := by
  set z := contract (baseOf φ) D with hz
  set d := twist (epsOf φ) (baseOf φ) D with hd
  have hψ : Function.Surjective (baseOf φ) := fun h => by
    obtain ⟨x, hx⟩ := hφ (0, h)
    exact ⟨x, by simp [baseOf, hx]⟩
  obtain ⟨u, hu⟩ := hφ (1, 0)
  have hu0 : baseOf φ u = 0 := by simp [baseOf, hu]
  have hu1 : epsOf φ u = 1 := by simp [epsOf, hu]
  have hcK : Fintype.card G = (2 * c) * Fintype.card K := by rw [hcard]; ring
  have hdz := vecDemands_contract hD (baseOf φ) hψ hcK
  have hzc : ∀ h, z h ≡ z 0 [ZMOD 2 ^ j] := fun h => by
    have := congr_pow_of_autocorr (p := 2) hi hc hK hK1 j z (k - lam) (lam * ((2 * c : ℕ) : ℤ))
      (fun g => by
        by_cases hg : g = 0
        · subst hg
          simp only [add_zero, ↓reduceIte]
          rw [hdz.sq]
          ring
        · rw [hdz.corr g hg]
          simp [hg]) hn h 0
    exact_mod_cast this
  have hdc : ∀ h, d h ≡ d 0 [ZMOD 2 ^ j] := fun h => by
    have := congr_pow_of_autocorr (p := 2) hi hc hK hK1 j d (k - lam) 0
      (fun g => by rw [twist_autocorr_of_isSDS hD _ _ hu0 hu1 g, add_zero]) hn h 0
    exact_mod_cast this
  have hfib := card_fibre_eq hφ (by rw [hcard, Fintype.card_prod, ZMod.card])
  have hW (e : ZMod 2) (h : K) : |contract φ D (e, h)| ≤ c := by
    have := abs_contract_le φ D (e, h)
    rwa [hfib] at this
  have hplus (h : K) : z h + d h = 2 * contract φ D (0, h) := by
    have := contract_add_twist φ D 0 h
    rwa [bitSign_zero, one_mul] at this
  have hminus (h : K) : z h - d h = 2 * contract φ D (1, h) := by
    have := contract_add_twist φ D 1 h
    rw [bitSign_one] at this
    linear_combination this
  refine ⟨hzc, hdc, sum_sq_contract hD (baseOf φ) hψ hcK hs,
    twist_sum_sq_of_isSDS hD _ _ hu0 hu1, fun h => ⟨?_, ?_⟩, ?_⟩
  · rw [hplus, abs_mul]
    have := hW 0 h
    norm_num
    linarith
  · rw [hminus, abs_mul]
    have := hW 1 h
    norm_num
    linarith
  · have hsum := hD.sum_abs_contract_le φ
    rw [sum_prod_two] at hsum
    simp only [hplus, hminus, abs_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    norm_num
    linarith

end Facts

/-! ### The two kills on `K = ZMod 3 × ZMod 3` -/

section Kills

variable {K : Type*} [Fintype K]

theorem two_abs_le_abs_add_abs_sub (a b : ℤ) : 2 * |a| ≤ |a + b| + |a - b| := by
  rcases abs_cases a with ⟨h, _⟩ | ⟨h, _⟩ <;>
    linarith [le_abs_self (a + b), neg_abs_le (a + b), le_abs_self (a - b), neg_abs_le (a - b)]

/-- Constant mod `M`: the sum is `|K|` times the first value, mod `M`. -/
theorem dvd_sum_sub {M : ℤ} (z : K → ℤ) (z0 : ℤ) (hz : ∀ h, z h ≡ z0 [ZMOD M]) :
    M ∣ ∑ h, z h - Fintype.card K * z0 := by
  have e : ∑ h, z h - Fintype.card K * z0 = ∑ h, (z h - z0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [e]
  exact Finset.dvd_sum fun h _ => (hz h).symm.dvd

/-- `(18, 2)` on `|K| = 9`: `z ≡ 2`, `d ≡ 0 (mod 4)` and `Σ d ≠ 0` leave
`Σ (|z + d| + |z − d|) ≥ 40`. -/
theorem kill_mod_four (hK : Fintype.card K = 9) (z d : K → ℤ) (z0 d0 : ℤ)
    (hz : ∀ h, z h ≡ z0 [ZMOD 4]) (hd : ∀ h, d h ≡ d0 [ZMOD 4])
    (hzs : (∑ h, z h) * (∑ h, z h) = 196) (hds : (∑ h, d h) * (∑ h, d h) = 16)
    (habs : ∑ h, (|z h + d h| + |z h - d h|) ≤ 36) : False := by
  classical
  have hz1 := dvd_sum_sub z z0 hz
  have hd1 := dvd_sum_sub d d0 hd
  rw [hK] at hz1 hd1
  push_cast at hz1 hd1
  have hZ : ∑ h, z h = 14 ∨ ∑ h, z h = -14 := by
    rcases mul_self_eq_mul_self_iff.1 (hzs.trans (by norm_num : (196 : ℤ) = 14 * 14)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hD : ∑ h, d h = 4 ∨ ∑ h, d h = -4 := by
    rcases mul_self_eq_mul_self_iff.1 (hds.trans (by norm_num : (16 : ℤ) = 4 * 4)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hz0 : z0 % 4 = 2 := by rcases hZ with h | h <;> rw [h] at hz1 <;> omega
  have hd0 : d0 % 4 = 0 := by rcases hD with h | h <;> rw [h] at hd1 <;> omega
  have hzh (h : K) : 4 ≤ |z h + d h| + |z h - d h| := by
    have h1 := (hz h).symm.dvd
    have h2 : z h ≤ -2 ∨ 2 ≤ z h := by omega
    have := two_abs_le_abs_add_abs_sub (z h) (d h)
    rcases h2 with h2 | h2 <;> linarith [le_abs_self (z h), neg_le_abs (z h)]
  obtain ⟨h0, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := d)
    (by rcases hD with h | h <;> rw [h] <;> norm_num)
  have hdh : 8 ≤ |z h0 + d h0| + |z h0 - d h0| := by
    have h1 := (hd h0).symm.dvd
    have h2 : d h0 ≤ -4 ∨ 4 ≤ d h0 := by omega
    have := two_abs_le_abs_add_abs_sub (d h0) (z h0)
    rw [add_comm (d h0), abs_sub_comm (d h0)] at this
    rcases h2 with h2 | h2 <;> linarith [le_abs_self (d h0), neg_le_abs (d h0)]
  have hrest : 4 * 8 ≤ ∑ h ∈ Finset.univ.erase h0, (|z h + d h| + |z h - d h|) := by
    have hc : (Finset.univ.erase h0).card = 8 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hK]
    calc (4 : ℤ) * 8 = ∑ h ∈ Finset.univ.erase h0, (4 : ℤ) := by
          rw [Finset.sum_const, hc]; norm_num
      _ ≤ _ := Finset.sum_le_sum fun h _ => hzh h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h0)] at habs
  linarith

/-- `(72, 8)` on `|K| = 9`: `z ≡ 4`, `d ≡ 0 (mod 8)` and `Σ d ≠ 0` leave some `|z ± d| ≥ 12`. -/
theorem kill_mod_eight (hK : Fintype.card K = 9) (z d : K → ℤ) (z0 d0 : ℤ)
    (hz : ∀ h, z h ≡ z0 [ZMOD 8]) (hd : ∀ h, d h ≡ d0 [ZMOD 8])
    (hzs : (∑ h, z h) * (∑ h, z h) = 784) (hds : (∑ h, d h) * (∑ h, d h) = 64)
    (hbox : ∀ h, |z h + d h| ≤ 10 ∧ |z h - d h| ≤ 10) : False := by
  classical
  have hz1 := dvd_sum_sub z z0 hz
  have hd1 := dvd_sum_sub d d0 hd
  rw [hK] at hz1 hd1
  push_cast at hz1 hd1
  have hZ : ∑ h, z h = 28 ∨ ∑ h, z h = -28 := by
    rcases mul_self_eq_mul_self_iff.1 (hzs.trans (by norm_num : (784 : ℤ) = 28 * 28)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hD : ∑ h, d h = 8 ∨ ∑ h, d h = -8 := by
    rcases mul_self_eq_mul_self_iff.1 (hds.trans (by norm_num : (64 : ℤ) = 8 * 8)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hz0 : z0 % 8 = 4 := by rcases hZ with h | h <;> rw [h] at hz1 <;> omega
  have hd0 : d0 % 8 = 0 := by rcases hD with h | h <;> rw [h] at hd1 <;> omega
  obtain ⟨h0, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := d)
    (by rcases hD with h | h <;> rw [h] <;> norm_num)
  have h1 := (hz h0).symm.dvd
  have h2 := (hd h0).symm.dvd
  have hz2 : z h0 ≤ -4 ∨ 4 ≤ z h0 := by omega
  have hd2 : d h0 ≤ -8 ∨ 8 ≤ d h0 := by omega
  obtain ⟨hp, hm⟩ := hbox h0
  rw [abs_le] at hp hm
  rcases hz2 with hz2 | hz2 <;> rcases hd2 with hd2 | hd2 <;> linarith

end Kills

section Rows

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem two_smul_eq_neg (h : ZMod 3 × ZMod 3) : 2 ^ 1 • h = -h := by
  revert h; decide

theorem card_three_three : Fintype.card (ZMod 3 × ZMod 3) = 9 := by
  rw [Fintype.card_prod, ZMod.card]

/-- No SDS `(90, 18, 2)` on a group onto `ZMod 2 × ZMod 3 × ZMod 3`. -/
theorem not_hasSDS_90_18_2 (φ : G →+ ZMod 2 × (ZMod 3 × ZMod 3)) (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = 90) : ¬ HasSDS G 18 2 := by
  rintro ⟨D, hD⟩
  obtain ⟨hz, hd, hzs, hds, -, habs⟩ := twist_facts (s := 14) (c := 5) (i := 1) (j := 2) hD φ hφ
    (by rw [hcard, card_three_three]) (by rw [hcard]; norm_num) one_pos two_smul_eq_neg
    (by rw [card_three_three]; decide) ⟨(1, 0), by decide⟩ (by norm_num)
  exact kill_mod_four card_three_three (contract (baseOf φ) D) (twist (epsOf φ) (baseOf φ) D)
    (contract (baseOf φ) D 0)
    (twist (epsOf φ) (baseOf φ) D 0) (fun h => by simpa using hz h)
    (fun h => by simpa using hd h) (by rw [hzs]; norm_num) (by rw [hds]; norm_num)
    (by push_cast at habs; linarith)

/-- No SDS `(90, 72, 8)` on a group onto `ZMod 2 × ZMod 3 × ZMod 3`. -/
theorem not_hasSDS_90_72_8 (φ : G →+ ZMod 2 × (ZMod 3 × ZMod 3)) (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = 90) : ¬ HasSDS G 72 8 := by
  rintro ⟨D, hD⟩
  obtain ⟨hz, hd, hzs, hds, hbox, -⟩ := twist_facts (s := 28) (c := 5) (i := 1) (j := 3) hD φ hφ
    (by rw [hcard, card_three_three]) (by rw [hcard]; norm_num) one_pos two_smul_eq_neg
    (by rw [card_three_three]; decide) ⟨(1, 0), by decide⟩ (by norm_num)
  exact kill_mod_eight card_three_three (contract (baseOf φ) D) (twist (epsOf φ) (baseOf φ) D)
    (contract (baseOf φ) D 0)
    (twist (epsOf φ) (baseOf φ) D 0) (fun h => by simpa using hz h)
    (fun h => by simpa using hd h) (by rw [hzs]; norm_num) (by rw [hds]; norm_num)
    (fun h => by have := hbox h; norm_num at this; exact this)

/-- `not_hasSDS_90_18_2` on the table's group `Grp ms`, `φ` given by the forms `A` (onto by the
preimages `P`). -/
theorem not_hasSDS_grp_90_18_2 {ms : List ℕ} {A P : List (List ℕ)}
    (hmap : MapOk ms [2, 3, 3] A) (hsurj : SurjCert ms [2, 3, 3] A P) (hv : ms.prod = 90)
    (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst 18 2 := by
  let φ : Grp ms →+ ZMod 2 × (ZMod 3 × ZMod 3) := linMap ms [2, 3, 3] A hmap
  exact not_hasSDS_90_18_2 φ (linMap_surjective hmap hsurj) (by rw [Grp.card_eq, hv])

/-- `not_hasSDS_90_72_8` on the table's group `Grp ms`. -/
theorem not_hasSDS_grp_90_72_8 {ms : List ℕ} {A P : List (List ℕ)}
    (hmap : MapOk ms [2, 3, 3] A) (hsurj : SurjCert ms [2, 3, 3] A P) (hv : ms.prod = 90)
    (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst 72 8 := by
  let φ : Grp ms →+ ZMod 2 × (ZMod 3 × ZMod 3) := linMap ms [2, 3, 3] A hmap
  exact not_hasSDS_90_72_8 φ (linMap_surjective hmap hsurj) (by rw [Grp.card_eq, hv])

end Rows

end SignedDifferenceSets.TwistBox
