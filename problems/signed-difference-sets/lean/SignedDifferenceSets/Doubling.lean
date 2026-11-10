module

public import SignedDifferenceSets.MaDescent
public import SignedDifferenceSets.MaRows.Polys

/-!
# The T-side of C26 at `c = 1` (I21's doubling, converse)

On `ZMod 2 × K` with `2` self-conjugate on `K` and `4 ∣ n`, `D(0, y)` and `D(1, y)` have the same
parity (`Ma.dvd_contract_sub` along the identity). So `D(0, ·) = Z + T` and `D(1, ·) = Z − T` for
sign vectors `Z`, `T` on `K` with disjoint supports, `Z` an SDS `((k + λ)/4, λ/2)` and `T` an SDS
`((k − λ)/4, 0)` (`halves_of_isSDS`): `4 Z Z* = n + 2λK` and `4 T T* = n`.
-/

@[expose] public section

namespace SignedDifferenceSets

open Ma


/-- The coset sums along the identity are the values. -/
theorem contract_id {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (D : G → SignType)
    (h : G) : contract (AddMonoidHom.id G) D h = D h := by
  simp [contract, Finset.filter_eq']

/-- A sum over `ZMod 2 × K`, split by the first coordinate. -/
theorem sum_zmod_two_prod {K : Type} [Fintype K] (f : ZMod 2 × K → ℤ) :
    ∑ x, f x = ∑ y, f (0, y) + ∑ y, f (1, y) := by
  rw [Fintype.sum_prod_type]
  exact Fin.sum_univ_two _

/-- A sign vector's support size is its sum of squares. -/
theorem card_ne_zero_eq_sum_sq {G : Type*} [Fintype G] (E : G → SignType) :
    (((Finset.univ.filter fun x => E x ≠ 0).card : ℕ) : ℤ) = ∑ x, (E x : ℤ) * (E x : ℤ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by cases E x <;> simp

/-- The halves of a pair of signs of equal parity: `a = z + t`, `b = z − t`. -/
def halfZ (a b : SignType) : SignType := if a = b then a else 0

/-- See `halfZ`. -/
def halfT (a b : SignType) : SignType := if a = -b then a else 0

theorem halves_spec {a b : SignType} (h : (2 : ℤ) ∣ (b : ℤ) - a) :
    (a : ℤ) = halfZ a b + halfT a b ∧ (b : ℤ) = halfZ a b - halfT a b ∧
      (halfZ a b = 0 ∨ halfT a b = 0) := by
  cases a <;> cases b <;> simp_all [halfZ, halfT]

/-- C26's T-side at `c = 1`: an SDS on `ZMod 2 × K` with `4 ∣ k − λ`, `2` self-conjugate on `K`,
splits into an SDS `Z` with parameters `(k', λ')`, `4k' = k + λ`, `2λ' = λ`, and an SDS `T` with
parameters `(k'', 0)`, `4k'' = k − λ`, with disjoint supports, `D(0, y) = Z y + T y`,
`D(1, y) = Z y − T y`. -/
theorem halves_of_isSDS {K : Type} [AddCommGroup K] [Fintype K] {i k k' k'' : ℕ} {lam lam' : ℤ}
    (hi : 0 < i)
    (hc : ∀ x : K, 2 ^ i • x = -x) (hn : (2 : ℤ) ^ 2 ∣ (k : ℤ) - lam)
    (hk' : 4 * (k' : ℤ) = k + lam) (hl' : 2 * lam' = lam) (hk'' : 4 * (k'' : ℤ) = k - lam)
    {D : ZMod 2 × K → SignType} (hD : IsSDS k lam D) :
    ∃ Z T : K → SignType, IsSDS k' lam' Z ∧ IsSDS k'' 0 T ∧ (∀ y, Z y = 0 ∨ T y = 0) ∧
      ∀ y, (D (0, y) : ℤ) = Z y + T y ∧ (D (1, y) : ℤ) = Z y - T y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpar : ∀ y : K, (2 : ℤ) ∣ (D (1, y) : ℤ) - D (0, y) := by
    intro y
    have h := Ma.dvd_contract_sub (G := ZMod 2 × K) (K := K) (p := 2) (r := 1) (b := 1) (e := 2)
      (c := 1) (φ := AddMonoidHom.id (ZMod 2 × K)) (fun x => ⟨x, rfl⟩) (by simp) one_pos hi hc hn
      (by norm_num) (MaRows.cycloFacts_of_mem_maPairs (pr := (2, 1)) (by decide)) hD 0 y
    simpa [contract_id] using h
  set Z : K → SignType := fun y => halfZ (D (0, y)) (D (1, y)) with hZdef
  set T : K → SignType := fun y => halfT (D (0, y)) (D (1, y)) with hTdef
  have hs : ∀ y, (D (0, y) : ℤ) = Z y + T y ∧ (D (1, y) : ℤ) = Z y - T y ∧ (Z y = 0 ∨ T y = 0) :=
    fun y => halves_spec (hpar y)
  -- the autocorrelations of `D` at `(0, g)` and `(1, g)` in terms of `Z` and `T`
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have hcorr0 : ∀ g : K, ∑ x, (D x : ℤ) * D (x + ((0 : ZMod 2), g)) =
      2 * ∑ y, ((Z y : ℤ) * Z (y + g) + (T y : ℤ) * T (y + g)) := by
    intro g
    rw [sum_zmod_two_prod, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Prod.mk_add_mk, add_zero]
    rw [(hs y).1, (hs (y + g)).1, (hs y).2.1, (hs (y + g)).2.1]
    ring
  have hcorr1 : ∀ g : K, ∑ x, (D x : ℤ) * D (x + ((1 : ZMod 2), g)) =
      2 * ∑ y, ((Z y : ℤ) * Z (y + g) - (T y : ℤ) * T (y + g)) := by
    intro g
    rw [sum_zmod_two_prod, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Prod.mk_add_mk, zero_add, h11]
    rw [(hs y).1, (hs (y + g)).1, (hs y).2.1, (hs (y + g)).2.1]
    ring
  have hD0 : ∑ x, (D x : ℤ) * D (x + ((0 : ZMod 2), (0 : K))) = k := by
    rw [← hD.sum_abs]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Prod.mk_zero_zero, add_zero]
    cases D x <;> simp
  have hD1 : ∀ g : K, ∑ x, (D x : ℤ) * D (x + ((1 : ZMod 2), g)) = lam :=
    fun g => hD.2 _ fun h => one_ne_zero (congrArg Prod.fst h : (1 : ZMod 2) = 0)
  have hDg : ∀ g : K, g ≠ 0 → ∑ x, (D x : ℤ) * D (x + ((0 : ZMod 2), g)) = lam :=
    fun g hg => hD.2 _ fun h => hg (congrArg Prod.snd h)
  have hZ : ∀ g : K, 4 * ∑ y, (Z y : ℤ) * Z (y + g) =
      ∑ x, (D x : ℤ) * D (x + ((0 : ZMod 2), g)) + ∑ x, (D x : ℤ) * D (x + ((1 : ZMod 2), g)) := by
    intro g
    rw [hcorr0, hcorr1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hT : ∀ g : K, 4 * ∑ y, (T y : ℤ) * T (y + g) =
      ∑ x, (D x : ℤ) * D (x + ((0 : ZMod 2), g)) - ∑ x, (D x : ℤ) * D (x + ((1 : ZMod 2), g)) := by
    intro g
    rw [hcorr0, hcorr1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  refine ⟨Z, T, ⟨?_, fun g hg => ?_⟩, ⟨?_, fun g hg => ?_⟩, fun y => (hs y).2.2,
    fun y => ⟨(hs y).1, (hs y).2.1⟩⟩
  · have h4 := hZ 0
    simp only [add_zero] at h4
    rw [hD0, hD1] at h4
    have := card_ne_zero_eq_sum_sq Z
    have : (((Finset.univ.filter fun x => Z x ≠ 0).card : ℕ) : ℤ) = k' := by linarith
    exact_mod_cast this
  · have h4 := hZ g
    rw [hDg g hg, hD1] at h4
    linarith
  · have h4 := hT 0
    simp only [add_zero] at h4
    rw [hD0, hD1] at h4
    have := card_ne_zero_eq_sum_sq T
    have : (((Finset.univ.filter fun x => T x ≠ 0).card : ℕ) : ℤ) = k'' := by linarith
    exact_mod_cast this
  · have h4 := hT g
    rw [hDg g hg, hD1] at h4
    linarith

end SignedDifferenceSets
