module

public import SignedDifferenceSets.KleinTomography
public import SignedDifferenceSets.EvenContraction

/-!
# The twist on a quotient `ZMod 2 × K` (I23)

Let `φ : G →+ ZMod 2 × K` be onto, `W` the coset sums of an SDS `D` along `φ`, `z` those along
`G → K` and `d` their twist by the character of `ZMod 2` (`KleinTomography.twist`). Then
`z + d = 2 W(0, ·)` and `z − d = 2 W(1, ·)` (`contract_add_twist`), so the box `|W| ≤ c` and
`Σ |W| ≤ k` bound `z ± d`. `z` meets C3's demands with fibres `2c` (`vecDemands_contract`,
`sum_sq_contract`); `d` has square sum `n = k − λ`, autocorrelation `0`, `|d| ≤ 2c`, `Σ |d| ≤ k`
and `≡ k (mod 2)` (`vecDemands_twist`). Groundwork for the box kills N1575 and N1593 (see
`scratch/tomo4/lean3-progress.md`).
-/

@[expose] public section

namespace SignedDifferenceSets.TwistBox

open KleinTomography

/-! ### The quotient `ZMod 2 × K` -/

section Quotient

variable {G K : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- `φ`'s `K` part. -/
def baseOf (φ : G →+ ZMod 2 × K) : G →+ K := (AddMonoidHom.snd _ _).comp φ

/-- `φ`'s `ZMod 2` part, a character of order 2. -/
def epsOf (φ : G →+ ZMod 2 × K) : G →+ ZMod 2 := (AddMonoidHom.fst _ _).comp φ

theorem bitSign_zero : bitSign 0 = 1 := by decide

theorem bitSign_one : bitSign 1 = -1 := by decide

theorem abs_bitSign (e : ZMod 2) : |bitSign e| = 1 := by
  revert e; decide

omit [AddCommGroup K] [Fintype K] in
theorem add_twist_pt (q : ZMod 2 × K) (e : ZMod 2) (h : K) (v : ℤ) :
    (if q.2 = h then v else 0) + bitSign e * (if q.2 = h then bitSign q.1 * v else 0) =
      2 * (if q = (e, h) then v else 0) := by
  have key : ∀ a b : ZMod 2, 1 + bitSign b * bitSign a = if a = b then 2 else 0 := by decide
  obtain ⟨a, b⟩ := q
  simp only [Prod.mk.injEq]
  split_ifs with h1 h2 h2
  · obtain ⟨hae, -⟩ := h2
    subst hae
    linear_combination v * bitSign_mul_self a
  · have hae : a ≠ e := fun hae => h2 ⟨hae, h1⟩
    have := key a e
    simp only [hae, ↓reduceIte] at this
    linear_combination v * this
  · exact absurd h2.2 h1
  · ring

omit [Fintype K] in
/-- The contraction to `K` plus or minus its twist is twice a coset sum along `φ`. -/
theorem contract_add_twist (φ : G →+ ZMod 2 × K) (D : G → SignType) (e : ZMod 2) (h : K) :
    contract (baseOf φ) D h + bitSign e * twist (epsOf φ) (baseOf φ) D h =
      2 * contract φ D (e, h) := by
  simp only [contract, twist, fibre, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => add_twist_pt (φ x) e h (D x)

omit [AddCommGroup K] [DecidableEq K] in
theorem sum_prod_two (f : ZMod 2 × K → ℤ) :
    ∑ q, f q = ∑ h, f (0, h) + ∑ h, f (1, h) := by
  rw [Fintype.sum_prod_type]
  exact Fin.sum_univ_two _

omit [Fintype K] in
theorem abs_twist_le (ε : G →+ ZMod 2) (ψ : G →+ K) (D : G → SignType) (h : K) :
    |twist ε ψ D h| ≤ (fibre ψ h).card := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [abs_mul, abs_bitSign, one_mul]
  rcases D x with _ | _ | _ <;> simp

theorem sum_abs_twist_le {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (ε : G →+ ZMod 2) (ψ : G →+ K) : ∑ h, |twist ε ψ D h| ≤ k := by
  calc ∑ h, |twist ε ψ D h| ≤ ∑ h, ∑ x ∈ fibre ψ h, |(D x : ℤ)| :=
        Finset.sum_le_sum fun h _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun x _ => le_of_eq (by rw [abs_mul, abs_bitSign, one_mul]))
    _ = k := by rw [sum_fibre, hD.sum_abs]

/-- The contraction to `K` (fibres `c`) meets C3's demands. -/
theorem vecDemands_contract {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (ψ : G →+ K) (hψ : Function.Surjective ψ) {c : ℕ} (hc : Fintype.card G = c * Fintype.card K) :
    VecDemands c (k + lam * ((c : ℤ) - 1)) (lam * c) k (contract ψ D) := by
  have hfib := card_fibre_eq hψ hc
  have hc1 : 1 ≤ c := by
    have := (Fintype.card_pos : 0 < Fintype.card G)
    rw [hc] at this
    exact Nat.pos_of_mul_pos_right this
  exact
    { bound := fun h => by
        have := abs_contract_le ψ D h
        rwa [hfib] at this
      sq := by rw [hD.contract_sq ψ, hfib 0, Nat.cast_sub hc1, Nat.cast_one]
      corr := fun g hg => by rw [hD.contract_autocorr ψ g hg, hfib]
      abs := hD.sum_abs_contract_le ψ
      parity := hD.sum_abs_contract_parity ψ }

/-- The contraction's sum is `±s`. -/
theorem sum_sq_contract {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (ψ : G →+ K) (hψ : Function.Surjective ψ) {c : ℕ} (hc : Fintype.card G = c * Fintype.card K)
    {s : ℤ} (hs : s * s = k + lam * ((Fintype.card G : ℤ) - 1)) :
    (∑ h, contract ψ D h) * (∑ h, contract ψ D h) = s * s := by
  have hdem := vecDemands_contract hD ψ hψ hc
  have hH1 : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  simp only [add_zero]
  rw [hdem.sq, Finset.sum_congr rfl fun g hg => hdem.corr g (Finset.ne_of_mem_erase hg),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hs, hc,
    nsmul_eq_mul, Nat.cast_sub hH1]
  push_cast
  ring

/-- The twist (fibres `c`, `ε` nontrivial on `ker ψ`) has square sum `k − λ`, autocorrelation
`0`, `|d| ≤ c`, `Σ |d| ≤ k` and `≡ k (mod 2)`. -/
theorem vecDemands_twist {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (ε : G →+ ZMod 2) (ψ : G →+ K) (hψ : Function.Surjective ψ) {c : ℕ}
    (hc : Fintype.card G = c * Fintype.card K) {u : G} (hu : ψ u = 0) (hεu : ε u = 1) :
    VecDemands c ((k : ℤ) - lam) 0 k (twist ε ψ D) := by
  have hfib := card_fibre_eq hψ hc
  refine
    { bound := fun h => by
        have := abs_twist_le ε ψ D h
        rwa [hfib] at this
      sq := twist_sq_of_isSDS hD ε ψ hu hεu
      corr := fun g hg => by simp [twist_autocorr_of_isSDS hD ε ψ hu hεu g, hg]
      abs := sum_abs_twist_le hD ε ψ
      parity := ?_ }
  have h2 : (2 : ℤ) ∣ ∑ h, (|twist ε ψ D h| - |contract ψ D h|) := Finset.dvd_sum fun h _ => by
    have := two_dvd_twist_sub ε ψ D h
    rcases abs_choice (twist ε ψ D h) with h1 | h1 <;>
      rcases abs_choice (contract ψ D h) with h2 | h2 <;> rw [h1, h2] <;> omega
  rw [Finset.sum_sub_distrib] at h2
  have := hD.sum_abs_contract_parity ψ
  omega

end Quotient

end SignedDifferenceSets.TwistBox
