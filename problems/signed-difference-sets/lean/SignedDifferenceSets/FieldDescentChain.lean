module

public import SignedDifferenceSets.FieldDescent

/-!
# Schmidt's field descent as a chain of steps (P18, milestone M2)

In `K = ℚ(ζ_m)` the coset sums `f` of an SDS give `X = ∑ f(h) ζ^h` with `X X̄ = n` (M1).
`FixedMod m d Y` says `Y` is fixed by `U_d`, the `σ_t` with `t ≡ 1 (mod d)`, i.e. `Y ∈ ℚ(ζ_d)`.
A step `d → d' = d / p` (`DescentStep`: `p² ∣ d`, `p` odd or `p = 2` with `8 ∣ d`, every prime
of `m` divides `d'`) takes some `ζ^j X` fixed by `U_d` to some `ζ^j' X` fixed by `U_{d'}`. For
each prime `q ∣ n` a unit `t ≡ 1 + d' (mod d)` that is a power of `q` modulo `m / q^a` puts `σ_t`
in the decomposition group of the primes over `q` (`smul_eq_self_of_pow`) and acts on `ζ^j X` as
`σ = σ_{1 + d'}`; so `σ (ζ^j X) = η ζ^j X`, `η = ± ζ^k` (S2–S4). Then `η ∈ ℚ(ζ_d)`, `σ^p ∈ U_d`
gives `η^p = 1` (for `p = 2` through `8 ∣ d`), and `ζ^(-g s) ζ^j X` is fixed by `σ` and by `U_d`,
which generate `U_{d'}` (`exists_fixedMod_step`, S5). A chain `m = d₀ → … → d_r = F`
(`DescentChain`) ends with some `ζ^j X ∈ ℚ(ζ_F)` (`exists_fixedMod_chain`, S6), and M1's
averaging and Parseval give `φ(m) n ≤ m F c²` (`IsSDS.totient_mul_le_of_chain`).
`FieldDescentChainCert` checks it on a row.
-/

@[expose] public section

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat Ideal
open scoped Pointwise

namespace SignedDifferenceSets

/-! ## Descent chains -/

/-- One step `d → d / p` of a descent chain in `ℚ(ζ_m)` for `n`: `p² ∣ d`, `p` odd or `p = 2`
with `8 ∣ d`, every prime of `m` divides `d / p`, and for each prime `q ∣ n` a unit `t` modulo `m`
with `t ≡ 1 + d / p (mod d)` and `t ≡ q^e (mod m / q^a)`, `q^a ∣ m`. -/
def DescentStep (m n d p : ℕ) : Prop :=
  p * (d / p) = d ∧ p ∣ d / p ∧ (Odd p ∨ (p = 2 ∧ 8 ∣ d)) ∧
    (∀ r : ℕ, r.Prime → r ∣ m → r ∣ d / p) ∧
    ∀ q : ℕ, q.Prime → q ∣ n → ∃ t a e : ℕ, t.Coprime m ∧ t ≡ 1 + d / p [MOD d] ∧
      q ^ a ∣ m ∧ t ≡ q ^ e [MOD m / q ^ a]

/-- A descent chain of valid steps `d → d / p₀ → d / p₀ / p₁ → …`; it ends at
`ps.foldl (· / ·) d`. -/
def DescentChain (m n : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | d, p :: ps => DescentStep m n d p ∧ DescentChain m n (d / p) ps

namespace FieldDescent

theorem pow_smul_eq_self {G α : Type*} [Monoid G] [MulAction G α] {σ : G} {W : α}
    (h : σ • W = W) (l : ℕ) : (σ ^ l) • W = W := by
  induction l with
  | zero => rw [pow_zero, one_smul]
  | succ l ih => rw [pow_succ, mul_smul, h, ih]

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
/-- If every prime of `m` divides `x`, every `1 + x z` is a unit modulo `m`. -/
theorem isUnit_one_add_mul {x : ℕ} (hx : ∀ r : ℕ, r.Prime → r ∣ m → r ∣ x) (z : ℕ) :
    IsUnit (1 + (x : ZMod m) * z) := by
  have hc : Nat.Coprime (1 + x * z) m := Nat.coprime_of_dvd fun r hr h1 h2 => by
    have h3 : r ∣ x * z + 1 := by rwa [add_comm] at h1
    exact hr.one_lt.ne' (Nat.dvd_one.1
      ((Nat.dvd_add_right (dvd_mul_of_dvd_left (hx r hr h2) z)).1 h3))
  exact_mod_cast (ZMod.isUnit_iff_coprime _ m).2 hc

omit [NeZero m] in
/-- `(1 + d')^l = 1 + l d' + d S` when `d ∣ d'²`. -/
theorem exists_one_add_pow {d d' e : ℕ} (h : d' * d' = d * e) (l : ℕ) :
    ∃ S : ZMod m, (1 + (d' : ZMod m)) ^ l = 1 + l * d' + d * S := by
  induction l with
  | zero => exact ⟨0, by simp⟩
  | succ l ih =>
    obtain ⟨S, hS⟩ := ih
    refine ⟨l * e + S + S * d', ?_⟩
    have h' : (d' : ZMod m) * d' = d * e := by rw [← Nat.cast_mul, ← Nat.cast_mul, h]
    rw [pow_succ, hS]
    push_cast
    linear_combination (l : ZMod m) * h'

section Field

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]

variable (m) in
/-- `Y` is fixed by `U_d`, the automorphisms `σ ↦ 1 + d z`; for `d ∣ m`, `Y ∈ ℚ(ζ_d)`. -/
def FixedMod (d : ℕ) (Y : 𝓞 K) : Prop :=
  ∀ τ : Gal(K/ℚ), ∀ z : ZMod m, (galEquivZMod m K τ : ZMod m) = 1 + d * z → τ • Y = Y

/-- `U_m` is trivial. -/
theorem fixedMod_self (Y : 𝓞 K) : FixedMod m m Y := by
  intro τ z hτ
  have h1 : τ = 1 := by
    apply (galEquivZMod m K).injective
    rw [map_one, Units.ext_iff, hτ, ZMod.natCast_self, zero_mul, add_zero, Units.val_one]
  rw [h1, one_smul]

theorem zetaChar_eq_one_iff {x : ZMod m} : zetaChar m K x = 1 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, AddChar.map_zero_eq_one]⟩
  have h1 : zetaChar m K x = (zeta_spec m ℚ K).toInteger ^ x.val := rfl
  rw [h1, (zeta_spec m ℚ K).toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd] at h
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt x)

theorem zetaChar_injective : Function.Injective (zetaChar m K) := fun x y h => by
  have h1 : zetaChar m K (x - y) = 1 := by
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, h, ← AddChar.map_add_eq_mul, add_neg_cancel,
      AddChar.map_zero_eq_one]
  exact sub_eq_zero.1 (zetaChar_eq_one_iff.1 h1)

theorem zetaChar_neg_mul (j : ZMod m) : zetaChar m K (-j) * zetaChar m K j = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem norm_zetaChar (φ : K →+* ℂ) (j : ZMod m) : ‖φ ((zetaChar m K j : 𝓞 K) : K)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := m) ?_ (NeZero.ne m)
  rw [RingOfIntegers.coe_eq_algebraMap, ← map_pow, ← map_pow, ← AddChar.map_nsmul_eq_pow,
    nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one, map_one, map_one]

/-- `U_{d'}` is generated by `σ ↦ 1 + d'` and `U_d` when `d ∣ d'²`. -/
theorem fixedMod_of_smul_eq {d d' e : ℕ} (h : d' * d' = d * e) (σ : Gal(K/ℚ))
    (hσ : (galEquivZMod m K σ : ZMod m) = 1 + d') {W : 𝓞 K} (hW : FixedMod m d W)
    (hσW : σ • W = W) : FixedMod m d' W := by
  intro τ z hτ
  obtain ⟨S, hS⟩ := exists_one_add_pow (m := m) h z.val
  have hu : (galEquivZMod m K (σ ^ z.val) : ZMod m) = 1 + z.val * d' + d * S := by
    rw [map_pow, Units.val_pow_eq_pow_val, hσ, hS]
  have hτ' : (galEquivZMod m K ((σ ^ z.val)⁻¹ * τ) : ZMod m) =
      1 + d * (-((((galEquivZMod m K (σ ^ z.val))⁻¹ : (ZMod m)ˣ) : ZMod m) * S)) := by
    have h1 := Units.inv_mul (galEquivZMod m K (σ ^ z.val))
    rw [hu] at h1
    have hz : z = (z.val : ZMod m) := (ZMod.natCast_zmod_val z).symm
    rw [map_mul, map_inv, Units.val_mul, hτ]
    linear_combination h1 + ((((galEquivZMod m K (σ ^ z.val))⁻¹ : (ZMod m)ˣ) : ZMod m) * d') * hz
  calc τ • W = (σ ^ z.val) • (((σ ^ z.val)⁻¹ * τ) • W) := by rw [← mul_smul, mul_inv_cancel_left]
    _ = W := by rw [hW _ _ hτ', pow_smul_eq_self hσW]

/-- S5, the descent step: `d = p d'`, `d' = p e`, `g d = m`, `p` odd or `p = 2` with `e` even,
every prime of `m` divides `d`, and `σ ↦ 1 + d'`. If `Y ≠ 0` is fixed by `U_d` and
`σ Y = ± ζ^k Y`, then some `ζ^(-g s) Y` is fixed by `U_{d'}`. -/
theorem exists_fixedMod_step {d d' p e g : ℕ} (hd : d = p * d') (he : d' = p * e)
    (hgd : g * d = m) (hp : Odd p ∨ (p = 2 ∧ Even e))
    (hrad : ∀ r : ℕ, r.Prime → r ∣ m → r ∣ d) (σ : Gal(K/ℚ))
    (hσ : (galEquivZMod m K σ : ZMod m) = 1 + d') {Y η : 𝓞 K} (hY : Y ≠ 0)
    (hYd : FixedMod m d Y)
    (hη : ∃ k : ℕ, η = (zeta_spec m ℚ K).toInteger ^ k ∨ η = -(zeta_spec m ℚ K).toInteger ^ k)
    (h : σ • Y = η * Y) :
    ∃ s : ℕ, FixedMod m d' (zetaChar m K (-((g * s : ℕ) : ZMod m)) * Y) := by
  have hdd : d' * d' = d * e := by rw [hd, he]; ring
  have hdc : (d : ZMod m) = p * d' := by rw [hd, Nat.cast_mul]
  have hgdc : (g : ZMod m) * d = 0 := by rw [← Nat.cast_mul, hgd, ZMod.natCast_self]
  have hp0 : 0 < p := by
    rcases hp with hp | ⟨rfl, -⟩
    · exact hp.pos
    · exact two_pos
  obtain ⟨k, hk⟩ := hη
  obtain ⟨ε, hε, hηε⟩ : ∃ ε : 𝓞 K, (ε = 1 ∨ ε = -1) ∧ η = ε * zetaChar m K k := by
    rcases hk with hk | hk
    · exact ⟨1, Or.inl rfl, by rw [hk, one_mul, zetaChar_natCast]⟩
    · exact ⟨-1, Or.inr rfl, by rw [hk, zetaChar_natCast, neg_one_mul]⟩
  have hεσ : ∀ τ : Gal(K/ℚ), τ • ε = ε := fun τ => by
    rcases hε with rfl | rfl
    · exact smul_one _
    · rw [smul_neg, smul_one]
  have hε0 : ε ≠ 0 := by
    rcases hε with rfl | rfl
    · exact one_ne_zero
    · exact neg_ne_zero.2 one_ne_zero
  have hε2 : ε ^ 2 = 1 := by
    rcases hε with rfl | rfl <;> ring
  -- `η ∈ ℚ(ζ_d)`: `σ_{1 + d}` fixes `Y` and `σ Y`, so `d k = 0`
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : Gal(K/ℚ),
      (galEquivZMod m K τ₁ : ZMod m) = 1 + d * ((1 : ℕ) : ZMod m) :=
    ⟨(galEquivZMod m K).symm (isUnit_one_add_mul hrad 1).unit, by
      rw [MulEquiv.apply_symm_apply, IsUnit.unit_spec]⟩
  have hY1 := hYd τ₁ _ hτ₁
  have hdk : (d : ZMod m) * k = 0 := by
    have hcomm : τ₁ * σ = σ * τ₁ :=
      (galEquivZMod m K).injective (by rw [map_mul, map_mul, mul_comm])
    have h1 : τ₁ • (σ • Y) = σ • Y := by rw [← mul_smul, hcomm, mul_smul, hY1]
    rw [h, smul_mul', hY1] at h1
    have h2 : τ₁ • η = η := mul_right_cancel₀ hY h1
    rw [hηε, smul_mul', hεσ, smul_zetaChar, hτ₁, Nat.cast_one, mul_one] at h2
    linear_combination zetaChar_injective (mul_left_cancel₀ hε0 h2)
  -- `σ^l η = ε ζ^(k + l d' k)` and the product over `l < i`
  have hl : ∀ l : ℕ, (σ ^ l) • η = ε * zetaChar m K (k + l * (d' * k)) := by
    intro l
    obtain ⟨T, hT⟩ := exists_one_add_pow (m := m) hdd l
    rw [hηε, smul_mul', hεσ, smul_zetaChar, map_pow, Units.val_pow_eq_pow_val, hσ, hT]
    refine congrArg (fun x => ε * zetaChar m K x) ?_
    linear_combination T * hdk
  have hprod : ∀ i : ℕ, ∏ l ∈ Finset.range i, (σ ^ l) • η =
      ε ^ i * zetaChar m K (i * k + ((∑ l ∈ Finset.range i, l : ℕ) : ZMod m) * (d' * k)) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Finset.prod_range_succ, ih, hl i, Finset.sum_range_succ, pow_succ, mul_mul_mul_comm,
        ← AddChar.map_add_eq_mul]
      refine congrArg (fun x => ε ^ i * ε * zetaChar m K x) ?_
      push_cast
      ring
  -- `σ^p ∈ U_d`, so the product over `l < p` is `1`
  obtain ⟨S, hS⟩ := exists_one_add_pow (m := m) hdd p
  have hσp : (σ ^ p) • Y = Y := hYd _ (1 + S) (by
    rw [map_pow, Units.val_pow_eq_pow_val, hσ, hS]
    linear_combination -hdc)
  have hone : ∏ l ∈ Finset.range p, (σ ^ l) • η = 1 := by
    have h1 := pow_smul_eq_prod σ h p
    rw [hσp] at h1
    exact mul_right_cancel₀ hY (by rw [one_mul]; exact h1.symm)
  rw [hprod p] at hone
  -- `η^p = 1`
  have hηp : η ^ p = 1 := by
    rcases hp with ⟨r, hr⟩ | ⟨rfl, e', he'⟩
    · have hs : ∑ l ∈ Finset.range p, l = p * r := by
        apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
        rw [Finset.sum_range_id_mul_two, hr, Nat.add_sub_cancel]
        ring
      rw [hs] at hone
      calc η ^ p = ε ^ p * zetaChar m K (p * k + ((p * r : ℕ) : ZMod m) * (d' * k)) := by
            rw [hηε, mul_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
            refine congrArg (fun x => ε ^ p * zetaChar m K x) ?_
            push_cast
            linear_combination ((r : ZMod m) * k) * hdc - (r : ZMod m) * hdk
        _ = 1 := hone
    · have hs : ∑ l ∈ Finset.range 2, l = 1 := by decide
      rw [hs, hε2, one_mul, zetaChar_eq_one_iff] at hone
      have hec : (d' : ZMod m) = 2 * e := by rw [he, Nat.cast_mul, Nat.cast_ofNat]
      have he'c : (e : ZMod m) = 2 * e' := by rw [he', Nat.cast_add]; ring
      have hd'k : (d' : ZMod m) * k = 0 := by
        push_cast at hone hdc
        linear_combination (e : ZMod m) * hone - (e' : ZMod m) * hdk +
          ((e' : ZMod m) * k) * hdc + (k : ZMod m) * hec - ((d' : ZMod m) * k) * he'c
      rw [hηε, mul_pow, hε2, one_mul, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
        zetaChar_eq_one_iff]
      push_cast at hone ⊢
      linear_combination hone - hd'k
  -- `η = ζ^(g d' s)`, and `W = ζ^(-g s) Y` is fixed by `σ` and by `U_d`
  obtain ⟨s, hs⟩ := exists_eq_zetaChar_mul (m := m) (K := K) (p := p) (F := g * d')
    (by rw [← hgd, hd]; ring) hp0 hηp
  refine ⟨s, fixedMod_of_smul_eq hdd σ hσ ?_ ?_⟩
  · intro τ z hτ
    rw [smul_mul', smul_zetaChar, hτ, hYd τ z hτ]
    refine congrArg (fun x => zetaChar m K x * Y) ?_
    push_cast
    linear_combination (-(z * s) : ZMod m) * hgdc
  · rw [smul_mul', smul_zetaChar, h, hs, hσ, ← mul_assoc, ← AddChar.map_add_eq_mul]
    refine congrArg (fun x => zetaChar m K x * Y) ?_
    push_cast
    ring

/-- S6, one step on `X ∣ n` with `|φ X|² = n` at every embedding: a valid step `d → d / p` takes
some `ζ^j X` fixed by `U_d` to some `ζ^j' X` fixed by `U_{d / p}`. -/
theorem exists_fixedMod_next {X : 𝓞 K} {n : ℕ} (hn : n ≠ 0) (hXn : X ∣ (n : 𝓞 K)) (hX0 : X ≠ 0)
    (hXnorm : ∀ φ : K →+* ℂ, ‖φ (X : K)‖ ^ 2 = n) {d p : ℕ} (hdm : d ∣ m)
    (hrad : ∀ r : ℕ, r.Prime → r ∣ m → r ∣ d) (hstep : DescentStep m n d p) {j : ZMod m}
    (hj : FixedMod m d (zetaChar m K j * X)) :
    ∃ j' : ZMod m, FixedMod m (d / p) (zetaChar m K j' * X) := by
  obtain ⟨hpd, ⟨e, he⟩, hp, hrad', hq⟩ := hstep
  generalize d / p = d' at hpd he hrad' hq ⊢
  have hp' : Odd p ∨ (p = 2 ∧ Even e) := by
    rcases hp with hp | ⟨rfl, c, hc⟩
    · exact Or.inl hp
    · exact Or.inr ⟨rfl, c, by omega⟩
  have hu : IsUnit (zetaChar m K j) := IsUnit.of_mul_eq_one_right _ (zetaChar_neg_mul j)
  have hY0 : zetaChar m K j * X ≠ 0 := mul_ne_zero hu.ne_zero hX0
  have hYn : zetaChar m K j * X ∣ (n : 𝓞 K) := hu.mul_left_dvd.2 hXn
  have hYnorm : ∀ φ : K →+* ℂ, ‖φ ((zetaChar m K j * X : 𝓞 K) : K)‖ ^ 2 = n := fun φ => by
    rw [show ((zetaChar m K j * X : 𝓞 K) : K) = (zetaChar m K j : K) * (X : K) from rfl,
      map_mul, norm_mul, norm_zetaChar, one_mul, hXnorm]
  -- `σ ↦ 1 + d'`
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(K/ℚ), (galEquivZMod m K σ : ZMod m) = 1 + d' :=
    ⟨(galEquivZMod m K).symm (isUnit_one_add_mul hrad' 1).unit, by
      rw [MulEquiv.apply_symm_apply, IsUnit.unit_spec, Nat.cast_one, mul_one]⟩
  have hσY : σ • (zetaChar m K j * X) ∣ (n : 𝓞 K) := by
    obtain ⟨Z, hZ⟩ := hYn
    refine ⟨σ • Z, ?_⟩
    rw [← smul_mul', ← hZ]
    exact (map_natCast (MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) σ) n).symm
  -- every prime over `n` has a `σ_t` in its decomposition group acting as `σ`
  have hassoc : Associated (zetaChar m K j * X) (σ • (zetaChar m K j * X)) := by
    refine associated_of_forall_smul hn hYn hσY fun P hP hnP => ?_
    have := hP.isPrime
    obtain ⟨q, hq', hqn, hqP⟩ := exists_prime_mem P hn hnP
    obtain ⟨t, a, e₁, htm, ht, ha, hte⟩ := hq q hq' hqn
    have : Fact q.Prime := ⟨hq'⟩
    obtain ⟨τ, hτ⟩ : ∃ τ : Gal(K/ℚ), (galEquivZMod m K τ : ZMod m) = t :=
      ⟨(galEquivZMod m K).symm (ZMod.unitOfCoprime t htm), by
        rw [MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime]⟩
    refine ⟨τ, smul_eq_self_of_pow (q := q) (a := a) (m'' := m / q ^ a) (e := e₁)
      (Nat.mul_div_cancel' ha).symm P hqP τ ?_, ?_⟩
    · rw [hτ, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff',
        Nat.mod_mod_of_dvd _ (Nat.div_dvd_of_dvd ha)]
      exact hte
    · obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.1 ht
      have htc : (t : ZMod m) = 1 + d' + d * (-(c : ZMod m)) := by
        have h1 := congrArg (Int.cast : ℤ → ZMod m) hc
        push_cast at h1
        linear_combination -h1
      have hτ' : (galEquivZMod m K (σ⁻¹ * τ) : ZMod m) =
          1 + d * ((((galEquivZMod m K σ)⁻¹ : (ZMod m)ˣ) : ZMod m) * -(c : ZMod m)) := by
        have h1 := Units.inv_mul (galEquivZMod m K σ)
        rw [hσ] at h1
        rw [map_mul, map_inv, Units.val_mul, hτ, htc]
        linear_combination h1
      calc τ • (zetaChar m K j * X) = σ • ((σ⁻¹ * τ) • (zetaChar m K j * X)) := by
            rw [← mul_smul, mul_inv_cancel_left]
        _ = σ • (zetaChar m K j * X) := by rw [hj _ _ hτ']
  have hnorm : ∀ φ : K →+* ℂ, ‖φ ((zetaChar m K j * X : 𝓞 K) : K)‖ =
      ‖φ ((σ • (zetaChar m K j * X) : 𝓞 K) : K)‖ := by
    intro φ
    have h1 := hYnorm φ
    have h2 := hYnorm (φ.comp (σ : K →+* K))
    rw [coe_smul]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h1.trans h2.symm)
  obtain ⟨η, hη, hση⟩ := exists_root_of_associated (m := m) hassoc hnorm hY0
  obtain ⟨s, hs⟩ := exists_fixedMod_step hpd.symm he (Nat.div_mul_cancel hdm) hp' hrad σ hσ hY0
    hj (eq_pow_or_eq_neg_pow hη) hση
  refine ⟨-((m / d * s : ℕ) : ZMod m) + j, ?_⟩
  rwa [AddChar.map_add_eq_mul, mul_assoc]

/-- S6, the chain: along a valid chain from `d`, some `ζ^j X` fixed by `U_d` gives some `ζ^j' X`
fixed by `U_F`, `F` the chain's end, with `F ∣ m` and every prime of `m` dividing `F`. -/
theorem exists_fixedMod_chain {X : 𝓞 K} {n : ℕ} (hn : n ≠ 0) (hXn : X ∣ (n : 𝓞 K))
    (hX0 : X ≠ 0) (hXnorm : ∀ φ : K →+* ℂ, ‖φ (X : K)‖ ^ 2 = n) :
    ∀ (ps : List ℕ) (d : ℕ) (j : ZMod m), d ∣ m → (∀ r : ℕ, r.Prime → r ∣ m → r ∣ d) →
      FixedMod m d (zetaChar m K j * X) → DescentChain m n d ps →
      ∃ j' : ZMod m, FixedMod m (ps.foldl (· / ·) d) (zetaChar m K j' * X) ∧
        ps.foldl (· / ·) d ∣ m ∧ ∀ r : ℕ, r.Prime → r ∣ m → r ∣ ps.foldl (· / ·) d
  | [], _, j, hdm, hrad, hj, _ => ⟨j, hj, hdm, hrad⟩
  | p :: ps, d, _, hdm, hrad, hj, ⟨hstep, hrest⟩ => by
    obtain ⟨j', hj'⟩ := exists_fixedMod_next hn hXn hX0 hXnorm hdm hrad hstep hj
    exact exists_fixedMod_chain hn hXn hX0 hXnorm ps (d / p) j'
      ((Nat.div_dvd_of_dvd ⟨d / p, hstep.1.symm⟩).trans hdm) hstep.2.2.2.1 hj' hrest

end Field

/-- M2 on the coset sums `f`, computed in `K`: a valid descent chain `m → … → F` gives
`φ(m) n ≤ m F c²`. -/
theorem totient_mul_le_of_chain_aux (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] {f : ZMod m → ℤ} {n : ℕ} {μ : ℤ} {c : ℕ} (hm : 1 < m)
    (hn : n ≠ 0) (hf : ∀ g, ∑ h, f h * f (h + g) = (if g = 0 then (n : ℤ) else 0) + μ)
    (hc : ∀ h, |f h| ≤ c) (ps : List ℕ) (hps : DescentChain m n m ps) :
    (Nat.totient m : ℤ) * n ≤ m * ps.foldl (· / ·) m * c ^ 2 := by
  classical
  have hXX := mul_elt_neg_eq (K := K) hm hf
  have hXn : elt K f ∣ (n : 𝓞 K) := ⟨elt K (fun h => f (-h)), by rw [hXX, Int.cast_natCast]⟩
  have hX0 : elt K f ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hXX
    exact hn (by exact_mod_cast hXX.symm)
  have hXnorm : ∀ φ : K →+* ℂ, ‖φ ((elt K f : 𝓞 K) : K)‖ ^ 2 = n := fun φ => by
    exact_mod_cast norm_sq_elt (K := K) hm hf φ
  have h0 : FixedMod m m (zetaChar m K 0 * elt K f) := by
    rw [AddChar.map_zero_eq_one, one_mul]
    exact fixedMod_self _
  obtain ⟨j, hj, hFm, hFrad⟩ :=
    exists_fixedMod_chain hn hXn hX0 hXnorm ps m 0 dvd_rfl (fun _ _ h => h) h0 hps
  generalize ps.foldl (· / ·) m = F at hj hFm hFrad ⊢
  obtain ⟨D, hD⟩ := hFm
  have hfix : ∀ a : (ZMod m)ˣ, ∀ u < D,
      Descent.chi ((a : ZMod m) * ((1 + F * u : ℕ) : ZMod m)) (fun h => f (h + -j)) =
        Descent.chi a (fun h => f (h + -j)) := by
    intro a u _
    obtain ⟨ρ, hρ⟩ := exists_ringHom (K := K) a
    obtain ⟨τ, hτ⟩ : ∃ τ : Gal(K/ℚ), (galEquivZMod m K τ : ZMod m) = 1 + F * (u : ZMod m) :=
      ⟨(galEquivZMod m K).symm (isUnit_one_add_mul hFrad u).unit, by
        rw [MulEquiv.apply_symm_apply, IsUnit.unit_spec]⟩
    have hρu := ringHom_comp_smul ρ hρ τ
    rw [hτ] at hρu
    have hcast : ((1 + F * u : ℕ) : ZMod m) = 1 + F * (u : ZMod m) := by norm_cast
    rw [hcast, ← ringHom_translate _ hρu f (-j), ← ringHom_translate _ hρ f (-j), neg_neg,
      RingHom.comp_apply, MulSemiringAction.toRingHom_apply, hj τ u hτ]
  exact totient_mul_le_of_chi (f := fun h => f (h + -j)) hm (autocorr_translate hf _)
    (fun h => hc _) hD.symm hfix

end FieldDescent

/-! ## M2 for an SDS -/

/-- P18 M2: an SDS with a cyclic quotient `ZMod m` (fibres of size `c`), `n = k − λ > 0`, and a
valid descent chain `m → … → F` for `n` (`DescentChain`) has `φ(m) n ≤ m F c²`. -/
theorem IsSDS.totient_mul_le_of_chain {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ}
    {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D) {m c : ℕ} [NeZero m] (hm : 1 < m)
    (φ : G →+ ZMod m) (hφ : Function.Surjective φ) (hcard : Fintype.card G = c * m)
    (hn : 0 < (k : ℤ) - lam) (ps : List ℕ) (hps : DescentChain m ((k : ℤ) - lam).toNat m ps) :
    (Nat.totient m : ℤ) * ((k : ℤ) - lam) ≤ m * ps.foldl (· / ·) m * c ^ 2 := by
  have hcardH : Fintype.card G = c * Fintype.card (ZMod m) := by rw [ZMod.card]; exact hcard
  have hnZ : (((k : ℤ) - lam).toNat : ℤ) = (k : ℤ) - lam := Int.toNat_of_nonneg hn.le
  have hA : ∀ g, ∑ h, contract φ D h * contract φ D (h + g) =
      (if g = 0 then ((((k : ℤ) - lam).toNat : ℕ) : ℤ) else 0) + lam * c := by
    intro g
    rw [hnZ]
    by_cases hg : g = 0
    · subst hg
      simp only [add_zero, ite_true]
      rw [hD.contract_sq φ, card_fibre_eq hφ hcardH, Nat.cast_sub (one_le_of_card hcardH),
        Nat.cast_one]
      ring
    · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcardH, ite_eq_right hg, zero_add]
  rw [← hnZ]
  have : NeZero ((m : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne m)⟩
  have : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  exact FieldDescent.totient_mul_le_of_chain_aux (CyclotomicField m ℚ) hm (by omega) hA
    (fun h => by have := abs_contract_le φ D h; rwa [card_fibre_eq hφ hcardH] at this) ps hps

/-! ## Row certificates -/

/-- A witness for a prime `q ∣ n` at one step: the unit `t`, with `q^a ∣ m` and `t ≡ q^e`. -/
structure DescentWitness where
  q : ℕ
  t : ℕ
  a : ℕ
  e : ℕ
  deriving DecidableEq

/-- One step of a chain certificate: the prime `p` and the witnesses for the primes of `n`. -/
structure DescentStepCert where
  p : ℕ
  ws : List DescentWitness
  deriving DecidableEq

/-- The step `d → d / p` in `ℚ(ζ_m)` for `n`, as arithmetic: `p` prime, `p² ∣ d`, `p` odd or
`8 ∣ d`, `m ∣ (d / p)^m` (every prime of `m` divides `d / p`), and for each prime `q ∣ n` (no
divisor in `[2, q)`) a witness with `gcd(t, m) = 1`, `t ≡ 1 + d / p (mod d)`, `q^a ∣ m` and
`t ≡ q^e (mod m / q^a)`. -/
def DescentStepCert.Ok (m n d : ℕ) (s : DescentStepCert) : Prop :=
  IsPrimeTD s.p ∧ d % (s.p * s.p) = 0 ∧ (s.p % 2 = 1 ∨ (s.p = 2 ∧ d % 8 = 0)) ∧
    (d / s.p) ^ m % m = 0 ∧
    ∀ q ∈ List.range (n + 1), 2 ≤ q → n % q = 0 → (∀ r ∈ List.range q, 2 ≤ r → q % r ≠ 0) →
      ∃ w ∈ s.ws, w.q = q ∧ Nat.gcd w.t m = 1 ∧ w.t % d = (1 + d / s.p) % d ∧
        m % q ^ w.a = 0 ∧ w.t % (m / q ^ w.a) = q ^ w.e % (m / q ^ w.a)

instance DescentStepCert.instDecidableOk (m n d : ℕ) (s : DescentStepCert) :
    Decidable (s.Ok m n d) := by
  unfold DescentStepCert.Ok; infer_instance

/-- Every step of a chain certificate, from `d`. -/
def StepsOk (m n : ℕ) : ℕ → List DescentStepCert → Prop
  | _, [] => True
  | d, s :: ss => s.Ok m n d ∧ StepsOk m n (d / s.p) ss

instance StepsOk.instDecidable (m n : ℕ) :
    (d : ℕ) → (ss : List DescentStepCert) → Decidable (StepsOk m n d ss)
  | _, [] => isTrue trivial
  | d, s :: ss =>
    letI := StepsOk.instDecidable m n (d / s.p) ss
    inferInstanceAs (Decidable (s.Ok m n d ∧ StepsOk m n (d / s.p) ss))

theorem DescentStepCert.Ok.descentStep {m n d : ℕ} (hn : 0 < n) {s : DescentStepCert}
    (h : s.Ok m n d) : DescentStep m n d s.p := by
  obtain ⟨hp, hpp, h2, hrad, hq⟩ := h
  have hpp' : s.p * s.p ∣ d := Nat.dvd_of_mod_eq_zero hpp
  have hpd : s.p ∣ d := (dvd_mul_right s.p s.p).trans hpp'
  refine ⟨Nat.mul_div_cancel' hpd, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hpp'
    exact ⟨r, by rw [hr, mul_assoc, Nat.mul_div_cancel_left _ hp.prime.pos]⟩
  · rcases h2 with h2 | ⟨h2, h8⟩
    · exact Or.inl (Nat.odd_iff.2 h2)
    · exact Or.inr ⟨h2, Nat.dvd_of_mod_eq_zero h8⟩
  · intro r hr hrm
    exact hr.dvd_of_dvd_pow (hrm.trans (Nat.dvd_of_mod_eq_zero hrad))
  · intro q hq' hqn
    obtain ⟨w, -, rfl, hgcd, ht, ha, he⟩ := hq q
      (List.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hn hqn))) hq'.two_le
      (Nat.mod_eq_zero_of_dvd hqn)
      (fun r hr hr2 hqr => by
        rcases hq'.eq_one_or_self_of_dvd r (Nat.dvd_of_mod_eq_zero hqr) with h1 | h1
        · omega
        · exact absurd (List.mem_range.1 hr) (by omega))
    exact ⟨w.t, w.a, w.e, hgcd, ht, Nat.dvd_of_mod_eq_zero ha, he⟩

theorem StepsOk.descentChain {m n : ℕ} (hn : 0 < n) :
    ∀ (d : ℕ) (ss : List DescentStepCert), StepsOk m n d ss →
      DescentChain m n d (ss.map (·.p))
  | _, [], _ => trivial
  | d, s :: ss, ⟨hs, hss⟩ => ⟨hs.descentStep hn, StepsOk.descentChain hn (d / s.p) ss hss⟩

/-- An M2 certificate: the quotient `ZMod m` as the form `A` with a preimage `P` of `1`, and the
chain's steps. -/
structure FieldDescentChainCert where
  m : ℕ
  A : List ℕ
  P : List ℕ
  steps : List DescentStepCert
  deriving DecidableEq

/-- M2's hypotheses on the row (`n = k − λ`, `c = v / m`) and the kill `m F c² < φ(m) n`, `F` the
chain's end. -/
def FieldDescentChainCert.Kills (w : Row) (c : FieldDescentChainCert) : Prop :=
  (∀ x ∈ w.ms, 0 < x) ∧ 1 < c.m ∧ c.m ∣ w.ms.prod ∧ MapOk w.ms [c.m] [c.A] ∧
    SurjCert w.ms [c.m] [c.A] [c.P] ∧ 0 < (w.k : ℤ) - w.lam ∧
    StepsOk c.m (w.k - w.lam).toNat c.m c.steps ∧
    c.m * (c.steps.map (·.p)).foldl (· / ·) c.m * (w.ms.prod / c.m) ^ 2 <
      Nat.totient c.m * (w.k - w.lam).toNat

instance FieldDescentChainCert.instDecidableKills (w : Row) (c : FieldDescentChainCert) :
    Decidable (c.Kills w) := by
  unfold FieldDescentChainCert.Kills; infer_instance

/-- A killed row has no SDS. -/
theorem FieldDescentChainCert.not_hasSDS {w : Row} {c : FieldDescentChainCert} (h : c.Kills w)
    (inst : Fintype (Grp w.ms)) : ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨-, hm, hmv, hmap, hsurj, hn, hsteps, hkill⟩ := h
  rintro ⟨D, hD⟩
  have : NeZero c.m := ⟨by omega⟩
  have hnZ : (w.k : ℤ) - w.lam = ((w.k - w.lam).toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm
  let φ : Grp w.ms →+ ZMod c.m := linMap w.ms [c.m] [c.A] hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp w.ms) = w.ms.prod / c.m * c.m := by
    rw [Grp.card_eq, Nat.div_mul_cancel hmv]
  have key := hD.totient_mul_le_of_chain hm φ hφ hcard hn (c.steps.map (·.p))
    (hsteps.descentChain (by omega) c.m c.steps)
  rw [hnZ] at key
  have hle : Nat.totient c.m * (w.k - w.lam).toNat ≤
      c.m * (c.steps.map (·.p)).foldl (· / ·) c.m * (w.ms.prod / c.m) ^ 2 := by
    exact_mod_cast key
  exact absurd hle (not_le.2 hkill)

end SignedDifferenceSets
