module

public import SignedDifferenceSets.UnramifiedDescent

/-!
# Schmidt's field descent, one step at an odd prime (P18, milestone M1)

The coset sums `f` of an SDS on a cyclic quotient `ZMod m` give `X = ∑ f(h) ζ^h` in `𝓞 K`,
`K = ℚ(ζ_m)`, with `X X̄ = n` (`mul_elt_neg_eq`) and `|φ X|² = n` at every embedding. Let `p` be an
odd prime, `p² ∣ m`, `F = m / p` and `t = 1 + F`. If `t` is a power of each prime `q ∣ n` modulo
the `q`-free part of `m`, `σ_t` fixes every prime ideal over `n` (`smul_eq_self_of_pow`, the
decomposition group, ramified or not), so `σ_t X` and `X` are associated
(`associated_of_forall_smul`) and differ by a root of unity `± ζ^k` (Kronecker:
`exists_root_of_associated`, `eq_pow_or_eq_neg_pow`). As `σ_t` has odd order `p`, that root is a
`p`-th root of unity and some `ζ^j X` is fixed by `σ_t` (`exists_smul_fixed`). Every character
`χ_a`, `a` a unit, of the matching translate of `f` is then invariant under `a ↦ a (1 + F u)`, sees
only the points `F h = 0` (`chi_eq_chi_restrict_of_chi`), and Parseval gives `φ(m) n ≤ m F c²`
(`IsSDS.totient_mul_le_of_descent`). `FieldDescentCert` checks it on a row.
-/

@[expose] public section

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat Ideal ComplexConjugate
open scoped Pointwise

namespace SignedDifferenceSets

namespace FieldDescent

/-! ## S1–S4: decomposition groups, the ideal step, Kronecker, roots of unity -/

/-- In a domain of characteristic `q`, a `q^a`-th root of unity is `1`. -/
theorem eq_one_of_pow_char_pow {R : Type*} [CommRing R] [IsDomain R] {q : ℕ} [hq : Fact q.Prime]
    [CharP R q] {y : R} {a : ℕ} (hy : y ^ q ^ a = 1) : y = 1 := by
  have : ExpChar R q := ExpChar.prime hq.out
  have h : (y - 1) ^ q ^ a = 0 := by rw [sub_pow_char_pow, hy, one_pow, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hq.out.ne_zero)).1 h)

variable {m : ℕ} [NeZero m]

section Field

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]

/-- S1, the decomposition group, ramified or not: if `m = q^a m''` and `σ ζ = ζ^t` with
`t ≡ q^e (mod m'')`, then `σ` fixes every maximal ideal `P ∋ q` of `𝓞 K`. On `𝓞 K ⧸ P`
(characteristic `q`) `σ` acts as `x ↦ x^(q^e)`: both are ring maps agreeing on `ζ` (`𝓞 K = ℤ[ζ]`),
and `ζ^(m'')` is a `q^a`-th root of unity, so `1` mod `P`. -/
theorem smul_eq_self_of_pow {q a m'' e : ℕ} [hq : Fact q.Prime] (hm : m = q ^ a * m'')
    (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (hqP : (q : 𝓞 K) ∈ P) (σ : Gal(K/ℚ))
    (hσ : ((galEquivZMod m K σ).val.val : ZMod m'') = ((q ^ e : ℕ) : ZMod m'')) :
    σ • P = P := by
  have hζ : IsPrimitiveRoot (zeta m ℚ K) m := zeta_spec m ℚ K
  have : CharP (𝓞 K ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq.out).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hqP)
  have : ExpChar (𝓞 K ⧸ P) q := ExpChar.prime hq.out
  set y : 𝓞 K ⧸ P := Ideal.Quotient.mk P hζ.toInteger with hy
  have hy1 : y ^ m'' = 1 := by
    refine eq_one_of_pow_char_pow (q := q) (a := a) ?_
    rw [← pow_mul, mul_comm, ← hm, hy, ← map_pow, hζ.toInteger_isPrimitiveRoot.pow_eq_one, map_one]
  let f₁ : 𝓞 K →+* 𝓞 K ⧸ P := (Ideal.Quotient.mk P).comp (MulSemiringAction.toRingHom _ _ σ)
  let f₂ : 𝓞 K →+* 𝓞 K ⧸ P := (iterateFrobenius (𝓞 K ⧸ P) q e).comp (Ideal.Quotient.mk P)
  have hgen : f₁ hζ.toInteger = f₂ hζ.toInteger := by
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hσ
    simp only [f₁, f₂, RingHom.comp_apply, MulSemiringAction.toRingHom_apply, iterateFrobenius_def]
    rw [galEquivZMod_smul_of_pow_eq m K σ hζ.toInteger_isPrimitiveRoot.pow_eq_one, map_pow, ← hy,
      pow_eq_pow_mod _ hy1, hmod, ← pow_eq_pow_mod _ hy1]
  have hf : f₁ = f₂ := by
    have h := AlgHom.ext_of_adjoin_eq_top (adjoin_singleton_eq_top hζ)
      (φ₁ := f₁.toIntAlgHom) (φ₂ := f₂.toIntAlgHom) (by
        rintro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hgen)
    exact RingHom.ext fun x => DFunLike.congr_fun h x
  have hle : σ • P ≤ P := by
    rw [pointwise_smul_def, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    have h := DFunLike.congr_fun hf x
    simp only [f₁, f₂, RingHom.comp_apply] at h
    rw [h, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  have hmax : (σ • P).IsMaximal := by
    rw [pointwise_smul_eq_comap]
    infer_instance
  exact hmax.eq_of_le hP.ne_top hle

/-- Kronecker, then the torsion of `ℚ(ζ_m)` (order `m` if `m` is even, else `2m`): a unit of
`𝓞 K` of absolute value `1` at every complex embedding is a root of unity of that order. -/
theorem pow_torsion_eq_one {u : (𝓞 K)ˣ} (hu : ∀ φ : K →+* ℂ, ‖φ (u : K)‖ = 1) :
    u ^ (if Even m then m else 2 * m) = 1 := by
  have hmem : u ∈ Units.torsion K := (Units.mem_torsion (K := K)).2 fun w => by
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.apply]
    exact hu _
  generalize hN : (if Even m then m else 2 * m) = N
  have hdvd : Units.torsionOrder K ∣ N := by
    rw [← hN, torsionOrder_eq (n := m) (K := K)]
  have h : (⟨u, hmem⟩ : Units.torsion K) ^ N = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard _).trans hdvd)
  exact congr_arg Subtype.val h

/-- S2, the ideal step: `Y, Z ∣ n ≠ 0`, and every maximal `P ∋ n` has some `τ` with `τ • P = P`
and `τ • Y = Z`; then `Y` and `Z` are associated (equal multiplicity at every prime ideal). -/
theorem associated_of_forall_smul {n : ℕ} (hn : n ≠ 0) {Y Z : 𝓞 K} (hY : Y ∣ (n : 𝓞 K))
    (hZ : Z ∣ (n : 𝓞 K))
    (hτ : ∀ P : Ideal (𝓞 K), P.IsMaximal → (n : 𝓞 K) ∈ P →
      ∃ τ : Gal(K/ℚ), τ • P = P ∧ τ • Y = Z) :
    Associated Y Z := by
  classical
  have hn' : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hY0 : Y ≠ 0 := fun h => hn' (zero_dvd_iff.1 (h ▸ hY))
  have hZ0 : Z ≠ 0 := fun h => hn' (zero_dvd_iff.1 (h ▸ hZ))
  rw [← Ideal.span_singleton_eq_span_singleton]
  have hI : Ideal.span {Y} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hJ : Ideal.span {Z} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hmult : ∀ P : Ideal (𝓞 K), Irreducible P →
      emultiplicity P (Ideal.span {Y}) = emultiplicity P (Ideal.span {Z}) := by
    intro P hP
    have hPp : P.IsPrime :=
      Ideal.isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1 hP)
    have hPm : P.IsMaximal := hPp.isMaximal (by rw [← Ideal.zero_eq_bot]; exact hP.ne_zero)
    by_cases hnP : (n : 𝓞 K) ∈ P
    · obtain ⟨τ, hτP, hτY⟩ := hτ P hPm hnP
      have hJ' : Ideal.span {Z} = τ • Ideal.span {Y} := by
        rw [Ideal.smul_closure, Set.smul_set_singleton, hτY]
      have h := emultiplicity_map_eq (MulSemiringAction.toRingEquiv Gal(K/ℚ) (Ideal (𝓞 K)) τ)
        (a := P) (b := Ideal.span {Y})
      simp only [MulSemiringAction.toRingEquiv_apply_apply, hτP] at h
      rw [hJ', h]
    · have h1 : ¬ P ∣ Ideal.span {Y} := by
        rw [Ideal.dvd_span_singleton]
        exact fun h => hnP (P.mem_of_dvd hY h)
      have h2 : ¬ P ∣ Ideal.span {Z} := by
        rw [Ideal.dvd_span_singleton]
        exact fun h => hnP (P.mem_of_dvd hZ h)
      rw [emultiplicity_eq_zero.2 h1, emultiplicity_eq_zero.2 h2]
  have hfac : UniqueFactorizationMonoid.normalizedFactors (Ideal.span {Y}) =
      UniqueFactorizationMonoid.normalizedFactors (Ideal.span {Z}) := by
    refine Multiset.ext.2 fun P => ?_
    by_cases hP : Irreducible P
    · have h := hmult P hP
      rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hP hI,
        UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hP hJ,
        normalize_eq] at h
      exact_mod_cast h
    · rw [Multiset.count_eq_zero.2 fun h =>
          hP (UniqueFactorizationMonoid.irreducible_of_normalized_factor _ h),
        Multiset.count_eq_zero.2 fun h =>
          hP (UniqueFactorizationMonoid.irreducible_of_normalized_factor _ h)]
  rw [← Ideal.prod_normalizedFactors_eq_self hI, hfac, Ideal.prod_normalizedFactors_eq_self hJ]

/-- S3: `Y, Z` associated with `‖φ Y‖ = ‖φ Z‖` at every `φ` and `Y ≠ 0` give `Z = η Y` with `η`
a root of unity. -/
theorem exists_root_of_associated {Y Z : 𝓞 K} (h : Associated Y Z)
    (hnorm : ∀ φ : K →+* ℂ, ‖φ (Y : K)‖ = ‖φ (Z : K)‖) (hY : Y ≠ 0) :
    ∃ η : 𝓞 K, η ^ (if Even m then m else 2 * m) = 1 ∧ Z = η * Y := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_, by rw [← hu, mul_comm]⟩
  have hu1 : ∀ φ : K →+* ℂ, ‖φ ((u : 𝓞 K) : K)‖ = 1 := by
    intro φ
    have hYK : (Y : K) ≠ 0 := by exact_mod_cast hY
    have hpos : 0 < ‖φ (Y : K)‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hYK)
    have h1 : ‖φ (Y : K)‖ * ‖φ ((u : 𝓞 K) : K)‖ = ‖φ (Y : K)‖ * 1 := by
      have hc : ((Y * u : 𝓞 K) : K) = (Y : K) * ((u : 𝓞 K) : K) := rfl
      rw [← norm_mul, ← map_mul, ← hc, hu, ← hnorm φ, mul_one]
    exact mul_left_cancel₀ hpos.ne' h1
  have h := congr_arg Units.val (pow_torsion_eq_one (m := m) hu1)
  generalize (if Even m then m else 2 * m) = N at h ⊢
  simpa using h

/-- S4: the roots of unity of `ℚ(ζ_m)` are `± ζ^k`. -/
theorem eq_pow_or_eq_neg_pow {η : 𝓞 K} (hη : η ^ (if Even m then m else 2 * m) = 1) :
    ∃ k : ℕ, η = (zeta_spec m ℚ K).toInteger ^ k ∨ η = -(zeta_spec m ℚ K).toInteger ^ k := by
  have hz := (zeta_spec m ℚ K).toInteger_isPrimitiveRoot
  split_ifs at hη with hm
  · obtain ⟨k, -, hk⟩ := hz.eq_pow_of_pow_eq_one hη
    exact ⟨k, Or.inl hk.symm⟩
  · have h2 : (η ^ 2) ^ m = 1 := by rw [← pow_mul]; exact hη
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one h2
    obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.1 hm
    refine ⟨a * (r + 1), sq_eq_sq_iff_eq_or_eq_neg.1 ?_⟩
    rw [← ha, ← pow_mul, show a * (r + 1) * 2 = a + m * a by rw [hr]; ring, pow_add, pow_mul,
      hz.pow_eq_one, one_pow, mul_one]

omit [NumberField K] in
/-- A prime ideal containing `n ≠ 0` contains a prime `q ∣ n`. -/
theorem exists_prime_mem (P : Ideal (𝓞 K)) [hP : P.IsPrime] {n : ℕ} (hn : n ≠ 0)
    (h : (n : 𝓞 K) ∈ P) : ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ (q : 𝓞 K) ∈ P := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => exact absurd ((P.eq_top_iff_one).2 (by simpa using h)) hP.ne_top
  | prime_mul q a hq ih =>
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h' | h'
    · exact ⟨q, hq, dvd_mul_right q a, h'⟩
    · obtain ⟨r, hr, hra, hrP⟩ := ih (right_ne_zero_of_mul hn) h'
      exact ⟨r, hr, dvd_mul_of_dvd_right hra q, hrP⟩

/-! ## `ζ^x` for `x : ZMod m`, and the element `X = ∑ f(h) ζ^h` -/

variable (m K) in
/-- `x ↦ ζ^x` on `ZMod m`, `ζ = zeta m ℚ K` in `𝓞 K`. -/
noncomputable def zetaChar : AddChar (ZMod m) (𝓞 K) :=
  AddChar.zmodChar m (zeta_spec m ℚ K).toInteger_isPrimitiveRoot.pow_eq_one

theorem zetaChar_natCast (a : ℕ) :
    zetaChar m K (a : ZMod m) = (zeta_spec m ℚ K).toInteger ^ a :=
  AddChar.zmodChar_apply' _ a

theorem zetaChar_one : zetaChar m K 1 = (zeta_spec m ℚ K).toInteger := by
  simpa using zetaChar_natCast (m := m) (K := K) 1

theorem zetaChar_sum_range (g : ℕ → ZMod m) (p : ℕ) :
    zetaChar m K (∑ l ∈ Finset.range p, g l) = ∏ l ∈ Finset.range p, zetaChar m K (g l) := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ, Finset.prod_range_succ, AddChar.map_add_eq_mul, ih]

/-- `σ ζ^x = ζ^(a x)` for `σ ↦ a` under `galEquivZMod`. -/
theorem smul_zetaChar (σ : Gal(K/ℚ)) (x : ZMod m) :
    σ • zetaChar m K x = zetaChar m K ((galEquivZMod m K σ : ZMod m) * x) := by
  have hζ := (zeta_spec m ℚ K).toInteger_isPrimitiveRoot
  have h1 : zetaChar m K x = (zeta_spec m ℚ K).toInteger ^ x.val := rfl
  rw [h1, smul_pow', galEquivZMod_smul_of_pow_eq m K σ hζ.pow_eq_one, ← pow_mul,
    ← zetaChar_natCast]
  congr 1
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val]

/-- A ring map to `ℂ` sending `ζ` to `ψ(b)` sends `ζ^x` to `ψ(b x)`, `ψ = ZMod.stdAddChar`. -/
theorem ringHom_zetaChar (ρ : 𝓞 K →+* ℂ) {b : ZMod m}
    (hb : ρ (zetaChar m K 1) = ZMod.stdAddChar b) (x : ZMod m) :
    ρ (zetaChar m K x) = ZMod.stdAddChar (b * x) := by
  conv_lhs =>
    rw [show x = x.val • (1 : ZMod m) by rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]]
  rw [AddChar.map_nsmul_eq_pow, map_pow, hb, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
    ZMod.natCast_zmod_val, mul_comm]

/-- The same map after `σ`: `ζ ↦ ψ(b a)`, `σ ↦ a`. -/
theorem ringHom_comp_smul (ρ : 𝓞 K →+* ℂ) {b : ZMod m}
    (hb : ρ (zetaChar m K 1) = ZMod.stdAddChar b) (σ : Gal(K/ℚ)) :
    (ρ.comp (MulSemiringAction.toRingHom _ _ σ)) (zetaChar m K 1) =
      ZMod.stdAddChar (b * (galEquivZMod m K σ : ZMod m)) := by
  rw [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, smul_zetaChar, mul_one,
    ringHom_zetaChar ρ hb]

theorem isPrimitiveRoot_stdAddChar_one : IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod m)) m := by
  refine ⟨?_, fun l hl => ?_⟩
  · rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self,
      AddChar.map_zero_eq_one]
  · rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := m)),
      ZMod.injective_stdAddChar.eq_iff, nsmul_eq_mul, mul_one] at hl
    exact (ZMod.natCast_eq_zero_iff l m).1 hl

/-- An injective ring map `𝓞 K → ℂ` sends `ζ` to `ψ(b)` for a unit `b`. -/
theorem exists_eq_stdAddChar (ρ : 𝓞 K →+* ℂ) (hρ : Function.Injective ρ) :
    ∃ b : (ZMod m)ˣ, ρ (zetaChar m K 1) = ZMod.stdAddChar (b : ZMod m) := by
  have hζ := ((zeta_spec m ℚ K).toInteger_isPrimitiveRoot).map_of_injective hρ
  have h1 := isPrimitiveRoot_stdAddChar_one (m := m)
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hcop : i.Coprime m := (h1.pow_iff_coprime (NeZero.pos m) i).1 (by rw [hi]; exact hζ)
  refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, zetaChar_one, ← hi, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
    mul_one]

theorem exists_ringHom_injective : ∃ ρ : 𝓞 K →+* ℂ, Function.Injective ρ := by
  obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  exact ⟨φ.comp (algebraMap (𝓞 K) K),
    φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)⟩

/-- For every unit `b` some ring map `𝓞 K → ℂ` sends `ζ` to `ψ(b)`. -/
theorem exists_ringHom (b : (ZMod m)ˣ) :
    ∃ ρ : 𝓞 K →+* ℂ, ρ (zetaChar m K 1) = ZMod.stdAddChar (b : ZMod m) := by
  obtain ⟨ρ₀, hinj⟩ := exists_ringHom_injective (K := K)
  obtain ⟨a, ha⟩ := exists_eq_stdAddChar (m := m) ρ₀ hinj
  refine ⟨ρ₀.comp (MulSemiringAction.toRingHom _ _ ((galEquivZMod m K).symm (a⁻¹ * b))), ?_⟩
  rw [ringHom_comp_smul ρ₀ ha, MulEquiv.apply_symm_apply, Units.val_mul,
    Units.mul_inv_cancel_left]

theorem coe_smul (σ : Gal(K/ℚ)) (x : 𝓞 K) : ((σ • x : 𝓞 K) : K) = σ (x : K) := rfl

variable (K) in
/-- `X = ∑ f(h) ζ^h ∈ 𝓞 K`. -/
noncomputable def elt (f : ZMod m → ℤ) : 𝓞 K := ∑ h, (f h : 𝓞 K) * zetaChar m K h

/-- A ring map with `ζ ↦ ψ(b)` sends `X` to the character sum `χ_b(f)`. -/
theorem ringHom_elt (ρ : 𝓞 K →+* ℂ) {b : ZMod m} (hb : ρ (zetaChar m K 1) = ZMod.stdAddChar b)
    (f : ZMod m → ℤ) : ρ (elt K f) = Descent.chi b f := by
  simp only [elt, Descent.chi, map_sum, map_mul, map_intCast, ringHom_zetaChar ρ hb]

theorem chi_neg (b : ZMod m) (f : ZMod m → ℤ) :
    Descent.chi b (fun h => f (-h)) = conj (Descent.chi b f) := by
  simp only [Descent.chi, map_sum, map_mul, map_intCast, ← AddChar.map_neg_eq_conj]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ fun h => by simp [mul_neg]

theorem chi_translate (b s : ZMod m) (f : ZMod m → ℤ) :
    Descent.chi b (fun h => f (h + s)) = ZMod.stdAddChar (b * -s) * Descent.chi b f := by
  rw [Descent.chi, Descent.chi, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun h => ?_
  simp only [Equiv.coe_addRight]
  rw [mul_left_comm, ← AddChar.map_add_eq_mul, show b * -s + b * (h + s) = b * h by ring]

/-- `ζ^(-s) X` goes to the character sum of the translate `f(· + s)`. -/
theorem ringHom_translate (ρ : 𝓞 K →+* ℂ) {b : ZMod m}
    (hb : ρ (zetaChar m K 1) = ZMod.stdAddChar b) (f : ZMod m → ℤ) (s : ZMod m) :
    ρ (zetaChar m K (-s) * elt K f) = Descent.chi b (fun h => f (h + s)) := by
  rw [map_mul, ringHom_zetaChar ρ hb, ringHom_elt ρ hb, chi_translate]

/-- S7: `|φ X|² = n` at every embedding `φ` when `f` has autocorrelation `n [g = 0] + μ`. -/
theorem norm_sq_elt {f : ZMod m → ℤ} {n μ : ℤ} (hm : 1 < m)
    (hf : ∀ g, ∑ h, f h * f (h + g) = (if g = 0 then n else 0) + μ) (φ : K →+* ℂ) :
    ‖φ ((elt K f : 𝓞 K) : K)‖ ^ 2 = n := by
  have hinj : Function.Injective (φ.comp (algebraMap (𝓞 K) K)) :=
    φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  obtain ⟨b, hb⟩ := exists_eq_stdAddChar (m := m) _ hinj
  have h : φ ((elt K f : 𝓞 K) : K) = Descent.chi b f := ringHom_elt _ hb f
  have : Fact (1 < m) := ⟨hm⟩
  have h2 := Descent.chi_mul_conj_eq hf b.ne_zero
  rw [← h, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  exact_mod_cast h2

/-- S7: `X X̄ = n` in `𝓞 K`, `X̄ = ∑ f(-h) ζ^h`. -/
theorem mul_elt_neg_eq {f : ZMod m → ℤ} {n μ : ℤ} (hm : 1 < m)
    (hf : ∀ g, ∑ h, f h * f (h + g) = (if g = 0 then n else 0) + μ) :
    elt K f * elt K (fun h => f (-h)) = n := by
  obtain ⟨ρ, hinj⟩ := exists_ringHom_injective (K := K)
  obtain ⟨b, hb⟩ := exists_eq_stdAddChar (m := m) ρ hinj
  apply hinj
  rw [map_mul, ringHom_elt ρ hb, ringHom_elt ρ hb, chi_neg, map_intCast]
  have : Fact (1 < m) := ⟨hm⟩
  exact Descent.chi_mul_conj_eq hf b.ne_zero

/-! ## S5: the descent step for `σ ζ = ζ^(1 + F)`, `p F = m`, `p` odd, `m ∣ F²` -/

omit [NeZero m] in
theorem one_add_pow {F : ℕ} (hF : ((F * F : ℕ) : ZMod m) = 0) (u : ℕ) :
    (1 + (F : ZMod m)) ^ u = 1 + u * F := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [pow_succ, ih]
    have h : (F : ZMod m) * F = 0 := by exact_mod_cast hF
    push_cast
    linear_combination (u : ZMod m) * h

omit [NeZero m] in
theorem sum_one_add_pow {p F : ℕ} (hpF : p * F = m) (hF : ((F * F : ℕ) : ZMod m) = 0)
    (hp : Odd p) : ∑ l ∈ Finset.range p, (1 + (F : ZMod m)) ^ l = p := by
  simp only [one_add_pow hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, ← Finset.sum_mul]
  obtain ⟨r, rfl⟩ := hp
  have h2 := Finset.sum_range_id_mul_two (2 * r + 1)
  rw [Nat.add_sub_cancel] at h2
  have hs : ∑ i ∈ Finset.range (2 * r + 1), i = (2 * r + 1) * r := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
    rw [h2]
    ring
  have hm0 : (((2 * r + 1) * F : ℕ) : ZMod m) = 0 := by rw [hpF, ZMod.natCast_self]
  rw [← Nat.cast_sum, hs]
  push_cast at hm0 ⊢
  linear_combination (r : ZMod m) * hm0

/-- `σ^i X = (∏_{l < i} σ^l η) X` from `σ X = η X`. -/
theorem pow_smul_eq_prod (σ : Gal(K/ℚ)) {X η : 𝓞 K} (h : σ • X = η * X) (i : ℕ) :
    (σ ^ i) • X = (∏ l ∈ Finset.range i, (σ ^ l) • η) * X := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, mul_smul, h, smul_mul', ih, Finset.prod_range_succ]
    ring

theorem prod_smul_eq_pow (σ : Gal(K/ℚ)) {p F : ℕ}
    (hσ : (galEquivZMod m K σ : ZMod m) = 1 + F) (hpF : p * F = m)
    (hF : ((F * F : ℕ) : ZMod m) = 0) (hp : Odd p) {ε : 𝓞 K} (hε : ε = 1 ∨ ε = -1)
    (κ : ZMod m) :
    ∏ l ∈ Finset.range p, (σ ^ l) • (ε * zetaChar m K κ) = (ε * zetaChar m K κ) ^ p := by
  have hεl : ∀ l : ℕ, (σ ^ l) • ε = ε := fun l => by
    rcases hε with rfl | rfl
    · exact smul_one _
    · rw [smul_neg, smul_one]
  have hl : ∀ l : ℕ, (σ ^ l) • (ε * zetaChar m K κ) =
      ε * zetaChar m K ((1 + (F : ZMod m)) ^ l * κ) := fun l => by
    rw [smul_mul', hεl, smul_zetaChar, map_pow, Units.val_pow_eq_pow_val, hσ]
  rw [Finset.prod_congr rfl fun l _ => hl l, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, ← zetaChar_sum_range, ← Finset.sum_mul, sum_one_add_pow hpF hF hp, mul_pow,
    ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

theorem pow_eq_one_of_galEquivZMod (σ : Gal(K/ℚ)) {p F : ℕ}
    (hσ : (galEquivZMod m K σ : ZMod m) = 1 + F) (hpF : p * F = m)
    (hF : ((F * F : ℕ) : ZMod m) = 0) : σ ^ p = 1 := by
  apply (galEquivZMod m K).injective
  rw [map_pow, map_one, Units.ext_iff, Units.val_pow_eq_pow_val, hσ, one_add_pow hF,
    Units.val_one]
  have h : (p : ZMod m) * F = 0 := by
    exact_mod_cast (show ((p * F : ℕ) : ZMod m) = 0 by rw [hpF, ZMod.natCast_self])
  rw [h, add_zero]

theorem exists_eq_zetaChar_mul {p F : ℕ} (hpF : p * F = m) (hp : 0 < p) {η : 𝓞 K}
    (hη : η ^ p = 1) : ∃ s : ℕ, η = zetaChar m K (F * s) := by
  have hζ := (zeta_spec m ℚ K).toInteger_isPrimitiveRoot
  have hζF : IsPrimitiveRoot ((zeta_spec m ℚ K).toInteger ^ F) p :=
    hζ.pow (NeZero.pos m) (by rw [← hpF, mul_comm])
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨s, -, hs⟩ := hζF.eq_pow_of_pow_eq_one hη
  refine ⟨s, ?_⟩
  rw [← hs, ← pow_mul, ← zetaChar_natCast, Nat.cast_mul]

theorem smul_zetaChar_mul_eq (σ : Gal(K/ℚ)) {F : ℕ}
    (hσ : (galEquivZMod m K σ : ZMod m) = 1 + F) {X : 𝓞 K} {s : ℕ}
    (h : σ • X = zetaChar m K (F * s) * X) :
    σ • (zetaChar m K (-(s : ZMod m)) * X) = zetaChar m K (-(s : ZMod m)) * X := by
  rw [smul_mul', smul_zetaChar, h, hσ, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- S5 (one step): `σ ζ = ζ^(1 + F)` with `p F = m`, `m ∣ F²`, `p` odd, and `σ X = ± ζ^k X`,
`X ≠ 0`; then some `ζ^(-s) X` is fixed by `σ`. -/
theorem exists_smul_fixed (σ : Gal(K/ℚ)) {p F : ℕ}
    (hσ : (galEquivZMod m K σ : ZMod m) = 1 + F) (hpF : p * F = m)
    (hF : ((F * F : ℕ) : ZMod m) = 0) (hp : Odd p) {X η : 𝓞 K} (hX : X ≠ 0)
    (hη : ∃ k : ℕ, η = (zeta_spec m ℚ K).toInteger ^ k ∨ η = -(zeta_spec m ℚ K).toInteger ^ k)
    (h : σ • X = η * X) :
    ∃ s : ℕ, σ • (zetaChar m K (-(s : ZMod m)) * X) = zetaChar m K (-(s : ZMod m)) * X := by
  obtain ⟨k, hk⟩ := hη
  obtain ⟨ε, hε, hηε⟩ : ∃ ε : 𝓞 K, (ε = 1 ∨ ε = -1) ∧ η = ε * zetaChar m K k := by
    rcases hk with hk | hk
    · exact ⟨1, Or.inl rfl, by rw [hk, one_mul, zetaChar_natCast]⟩
    · exact ⟨-1, Or.inr rfl, by rw [hk, zetaChar_natCast, neg_one_mul]⟩
  have hηp : η ^ p = 1 := by
    have h1 := pow_smul_eq_prod σ h p
    rw [pow_eq_one_of_galEquivZMod σ hσ hpF hF, one_smul, hηε,
      prod_smul_eq_pow σ hσ hpF hF hp hε, ← hηε] at h1
    have h2 : (η ^ p - 1) * X = 0 := by linear_combination -h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hX)
  obtain ⟨s, hs⟩ := exists_eq_zetaChar_mul hpF hp.pos hηp
  exact ⟨s, smul_zetaChar_mul_eq σ hσ (by rw [h, hs])⟩

end Field

/-! ## S8: averaging and Parseval -/

open Descent in
/-- If `χ_a(f)` is invariant under `a ↦ a (1 + F u)` for `u < d` (`F d = m`, `a` a unit), it
sees only the points `F h = 0`. -/
theorem chi_eq_chi_restrict_of_chi {f : ZMod m → ℤ} {F d : ℕ} (hFd : F * d = m) (hd : 0 < d)
    {a : ZMod m} (ha : IsUnit a)
    (hfix : ∀ u < d, chi (a * ((1 + F * u : ℕ) : ZMod m)) f = chi a f) :
    chi a f = chi a (restrict F f) := by
  have hstep (u : ℕ) (hu : u < d) : chi a f = ∑ h, (f h : ℂ) * ZMod.stdAddChar (a * h) *
      ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u := by
    rw [← hfix u hu, chi]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hψ : (ZMod.stdAddChar (a * ((1 + F * u : ℕ) : ZMod m) * h) : ℂ) =
        ZMod.stdAddChar (a * h) * ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u := by
      rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul, nsmul_eq_mul]
      congr 1
      push_cast
      ring
    rw [hψ]
    ring
  have hsum : (d : ℂ) * chi a f = ∑ h, (f h : ℂ) * ZMod.stdAddChar (a * h) *
      ∑ u ∈ Finset.range d, ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u := by
    calc (d : ℂ) * chi a f = ∑ _u ∈ Finset.range d, chi a f := by simp
      _ = ∑ u ∈ Finset.range d, ∑ h, (f h : ℂ) * ZMod.stdAddChar (a * h) *
            ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u :=
          Finset.sum_congr rfl fun u hu => hstep u (Finset.mem_range.1 hu)
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  have hm0 : ((F * d : ℕ) : ZMod m) = 0 := by rw [hFd, ZMod.natCast_self]
  have hgeom (h : ZMod m) : ∑ u ∈ Finset.range d, ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u =
      if F • h = 0 then (d : ℂ) else 0 := by
    rw [nsmul_eq_mul]
    split_ifs with hF
    · simp [mul_assoc, hF]
    · have hw : ZMod.stdAddChar (a * (F : ZMod m) * h) ≠ (1 : ℂ) := by
        rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := m)), Ne,
          ZMod.injective_stdAddChar.eq_iff, mul_assoc]
        exact fun h0 => hF ((ha.mul_right_eq_zero).1 h0)
      have hw1 : ZMod.stdAddChar (a * (F : ZMod m) * h) ^ d = (1 : ℂ) := by
        have hx : (d : ZMod m) * (a * F * h) = ((F * d : ℕ) : ZMod m) * (a * h) := by
          push_cast
          ring
        rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hx, hm0, zero_mul,
          AddChar.map_zero_eq_one]
      rw [geom_sum_eq hw, hw1, sub_self, zero_div]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  apply mul_left_cancel₀ hd0
  rw [hsum, chi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [hgeom h, restrict]
  split_ifs
  · ring
  · simp

open Descent in
/-- S8, the bound: `f` with autocorrelation `n [g = 0] + μ`, `|f| ≤ c`, and every `χ_a(f)`
(`a` a unit) invariant under `a ↦ a (1 + F u)`, `u < d`, `F d = m`, has `φ(m) n ≤ m F c²`. -/
theorem totient_mul_le_of_chi {f : ZMod m → ℤ} {n μ : ℤ} {c F d : ℕ} (hm : 1 < m)
    (hf : ∀ g, ∑ h, f h * f (h + g) = (if g = 0 then n else 0) + μ) (hc : ∀ h, |f h| ≤ c)
    (hFd : F * d = m)
    (hfix : ∀ a : (ZMod m)ˣ, ∀ u < d,
      chi ((a : ZMod m) * ((1 + F * u : ℕ) : ZMod m)) f = chi a f) :
    (Nat.totient m : ℤ) * n ≤ m * F * c ^ 2 := by
  classical
  have : Fact (1 < m) := ⟨hm⟩
  have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by subst h0; omega
  have hF : 0 < F := Nat.pos_of_ne_zero fun h0 => by subst h0; omega
  set g := restrict F f with hg
  have hunits (a : (ZMod m)ˣ) : Complex.normSq (chi (a : ZMod m) g) = n := by
    have h1 := chi_mul_conj_eq hf (a.ne_zero)
    rw [chi_eq_chi_restrict_of_chi hFd hd a.isUnit (hfix a), Complex.mul_conj] at h1
    exact_mod_cast h1
  have hpars : ∑ a, Complex.normSq (chi a g) = (m : ℝ) * ((∑ h, g h * g h : ℤ) : ℝ) := by
    have h1 := sum_chi_mul_conj (m := m) g
    simp only [Complex.mul_conj] at h1
    exact_mod_cast h1
  have hcard : (Finset.univ.filter fun h : ZMod m => F • h = 0).card ≤ F := by
    convert IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod m) hF
  have hgsq : ∑ h, g h * g h ≤ F * c ^ 2 := by
    calc ∑ h, g h * g h = ∑ h ∈ Finset.univ.filter fun h : ZMod m => F • h = 0, f h * f h := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [hg, restrict]
          split_ifs <;> simp
      _ ≤ ∑ _h ∈ Finset.univ.filter fun h : ZMod m => F • h = 0, (c : ℤ) ^ 2 := by
          refine Finset.sum_le_sum fun h _ => ?_
          rw [← sq, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hc h) 2
      _ ≤ F * c ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
  have hle : ∑ a : (ZMod m)ˣ, Complex.normSq (chi (a : ZMod m) g) ≤
      ∑ a, Complex.normSq (chi a g) := by
    rw [← Finset.sum_image (s := Finset.univ) (g := ((↑) : (ZMod m)ˣ → ZMod m))
      (f := fun x => Complex.normSq (chi x g)) (fun a _ b _ h => Units.ext h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => Complex.normSq_nonneg _
  simp only [hunits, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient,
    nsmul_eq_mul] at hle
  rw [hpars] at hle
  have hgsq' : ((∑ h, g h * g h : ℤ) : ℝ) ≤ F * c ^ 2 := by exact_mod_cast hgsq
  have hfin : (Nat.totient m : ℝ) * n ≤ m * F * c ^ 2 := by
    calc (Nat.totient m : ℝ) * n ≤ m * ((∑ h, g h * g h : ℤ) : ℝ) := hle
      _ ≤ m * (F * c ^ 2) := by gcongr
      _ = m * F * c ^ 2 := by ring
  exact_mod_cast hfin

/-! ## The step on `f`, in any `K = ℚ(ζ_m)` -/

/-- M1 on the coset sums `f`, computed in `K`: `p F = m`, `p ∣ F`, `p` odd, and for each prime
`q ∣ n` some `q^a ∣ m` with `1 + F ≡ q^e (mod m / q^a)`; then `φ(m) n ≤ m F c²`. -/
theorem totient_mul_le_of_descent_aux (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] {f : ZMod m → ℤ} {n : ℕ} {μ : ℤ} {c p F : ℕ} (hm : 1 < m)
    (hn : n ≠ 0) (hf : ∀ g, ∑ h, f h * f (h + g) = (if g = 0 then (n : ℤ) else 0) + μ)
    (hc : ∀ h, |f h| ≤ c) (hpF : p * F = m) (hpF' : p ∣ F) (hp : Odd p)
    (hq : ∀ q : ℕ, q.Prime → q ∣ n → ∃ a e : ℕ, q ^ a ∣ m ∧ 1 + F ≡ q ^ e [MOD m / q ^ a]) :
    (Nat.totient m : ℤ) * n ≤ m * F * c ^ 2 := by
  classical
  have hF2 : ((F * F : ℕ) : ZMod m) = 0 := by
    obtain ⟨r, rfl⟩ := hpF'
    rw [ZMod.natCast_eq_zero_iff]
    exact ⟨r, by rw [← hpF]; ring⟩
  -- `σ = σ_t`, `t = 1 + F`
  have ht : (1 + (F : ZMod m)) ^ p = 1 := by
    rw [one_add_pow hF2]
    have h : (p : ZMod m) * F = 0 := by
      exact_mod_cast (show ((p * F : ℕ) : ZMod m) = 0 by rw [hpF, ZMod.natCast_self])
    rw [h, add_zero]
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(K/ℚ), (galEquivZMod m K σ : ZMod m) = 1 + F :=
    ⟨(galEquivZMod m K).symm (Units.ofPowEqOne _ p ht hp.pos.ne'), by
      rw [MulEquiv.apply_symm_apply]; simp⟩
  -- `X X̄ = n`, `X = elt K f`
  have hXX := mul_elt_neg_eq (K := K) hm hf
  have hXn : elt K f ∣ (n : 𝓞 K) := ⟨elt K (fun h => f (-h)), by rw [hXX, Int.cast_natCast]⟩
  have hX0 : elt K f ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hXX
    exact hn (by exact_mod_cast hXX.symm)
  -- `σ` fixes every prime over `n`
  have hfixP : ∀ P : Ideal (𝓞 K), P.IsMaximal → (n : 𝓞 K) ∈ P → σ • P = P := by
    intro P hP hnP
    have := hP.isPrime
    obtain ⟨q, hq', hqn, hqP⟩ := exists_prime_mem P hn hnP
    obtain ⟨a, e, ha, he⟩ := hq q hq' hqn
    have : Fact q.Prime := ⟨hq'⟩
    refine smul_eq_self_of_pow (q := q) (a := a) (m'' := m / q ^ a) (e := e)
      (Nat.mul_div_cancel' ha).symm P hqP σ ?_
    have hval : (galEquivZMod m K σ).val.val = (1 + F) % m := by
      rw [hσ, show (1 + (F : ZMod m)) = ((1 + F : ℕ) : ZMod m) by simp, ZMod.val_natCast]
    rw [hval, ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ (Nat.div_dvd_of_dvd ha)]
    exact he
  -- `σ X = η X`, `η = ± ζ^k`
  have hσX : σ • elt K f ∣ (n : 𝓞 K) := by
    obtain ⟨Y, hY⟩ := hXn
    refine ⟨σ • Y, ?_⟩
    rw [← smul_mul', ← hY]
    exact (map_natCast (MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) σ) n).symm
  have hassoc : Associated (elt K f) (σ • elt K f) :=
    associated_of_forall_smul hn hXn hσX fun P hP hnP => ⟨σ, hfixP P hP hnP, rfl⟩
  have hnorm : ∀ φ : K →+* ℂ, ‖φ ((elt K f : 𝓞 K) : K)‖ = ‖φ ((σ • elt K f : 𝓞 K) : K)‖ := by
    intro φ
    have h1 := norm_sq_elt (K := K) hm hf φ
    have h2 := norm_sq_elt (K := K) hm hf (φ.comp (σ : K →+* K))
    rw [coe_smul]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h1.trans h2.symm)
  obtain ⟨η, hη, hση⟩ := exists_root_of_associated (m := m) hassoc hnorm hX0
  -- descent: `W = ζ^(-s) X` is fixed by `σ`, hence by every `σ^u`
  obtain ⟨s, hs⟩ := exists_smul_fixed σ hσ hpF hF2 hp hX0 (eq_pow_or_eq_neg_pow hη) hση
  have hWu : ∀ u : ℕ, (σ ^ u) • (zetaChar m K (-(s : ZMod m)) * elt K f) =
      zetaChar m K (-(s : ZMod m)) * elt K f := fun u => by
    induction u with
    | zero => rw [pow_zero, one_smul]
    | succ u ih => rw [pow_succ, mul_smul, hs, ih]
  -- every unit character of the translate is invariant under `a ↦ a (1 + F u)`
  have hfix : ∀ a : (ZMod m)ˣ, ∀ u < p,
      Descent.chi ((a : ZMod m) * ((1 + F * u : ℕ) : ZMod m)) (fun h => f (h + (s : ZMod m))) =
        Descent.chi a (fun h => f (h + (s : ZMod m))) := by
    intro a u _
    obtain ⟨ρ, hρ⟩ := exists_ringHom (K := K) a
    have hρu := ringHom_comp_smul ρ hρ (σ ^ u)
    have hgu : (galEquivZMod m K (σ ^ u) : ZMod m) = ((1 + F * u : ℕ) : ZMod m) := by
      rw [map_pow, Units.val_pow_eq_pow_val, hσ, one_add_pow hF2]
      push_cast
      ring
    rw [hgu] at hρu
    rw [← ringHom_translate _ hρu f (s : ZMod m), ← ringHom_translate _ hρ f (s : ZMod m),
      RingHom.comp_apply, MulSemiringAction.toRingHom_apply, hWu u]
  exact totient_mul_le_of_chi (f := fun h => f (h + (s : ZMod m))) hm
    (autocorr_translate hf _) (fun h => hc _) (by rw [mul_comm]; exact hpF) hfix

end FieldDescent

/-! ## M1 for an SDS -/

/-- M1 with explicit `F`: an SDS with a cyclic quotient `ZMod m` (fibres of size `c`),
`n = k − λ > 0`, `p F = m` with `p ∣ F` and `p` odd, and for each prime `q ∣ n` some `q^a ∣ m` with
`1 + F ≡ q^e (mod m / q^a)`, has `φ(m) n ≤ m F c²`. -/
theorem IsSDS.totient_mul_le_of_descent' {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ}
    {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D) {m c p F : ℕ} [NeZero m] (hm : 1 < m)
    (φ : G →+ ZMod m) (hφ : Function.Surjective φ) (hcard : Fintype.card G = c * m)
    (hn : 0 < (k : ℤ) - lam) (hpF : p * F = m) (hpF' : p ∣ F) (hp : Odd p)
    (hq : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (k : ℤ) - lam →
      ∃ a e : ℕ, q ^ a ∣ m ∧ 1 + F ≡ q ^ e [MOD m / q ^ a]) :
    (Nat.totient m : ℤ) * ((k : ℤ) - lam) ≤ m * F * c ^ 2 := by
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
  exact FieldDescent.totient_mul_le_of_descent_aux (CyclotomicField m ℚ) hm (by omega) hA
    (fun h => by have := abs_contract_le φ D h; rwa [card_fibre_eq hφ hcardH] at this) hpF hpF' hp
    fun q hq' hqn => hq q hq' (by rw [← hnZ]; exact_mod_cast hqn)

/-- P18 M1: an SDS with a cyclic quotient `ZMod m` (fibres of size `c`), `n = k − λ > 0`, an odd
prime `p` with `p² ∣ m` (so `rad m ∣ m / p`), and for every prime `q ∣ n` some `e` with
`1 + m/p ≡ q^e` modulo the `q`-free part of `m`, has `φ(m) n ≤ m (m/p) c²`. -/
theorem IsSDS.totient_mul_le_of_descent {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ}
    {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D) {m c p : ℕ} [NeZero m] (hm : 1 < m)
    (φ : G →+ ZMod m) (hφ : Function.Surjective φ) (hcard : Fintype.card G = c * m)
    (hn : 0 < (k : ℤ) - lam) (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ^ 2 ∣ m)
    (hq : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (k : ℤ) - lam →
      ∃ e : ℕ, 1 + m / p ≡ q ^ e [MOD ordCompl[q] m]) :
    (Nat.totient m : ℤ) * ((k : ℤ) - lam) ≤ m * (m / p) * c ^ 2 := by
  have hpm' : p ∣ m := (dvd_pow_self p two_ne_zero).trans hpm
  refine hD.totient_mul_le_of_descent' hm φ hφ hcard hn (Nat.mul_div_cancel' hpm') ?_
    (hp.odd_of_ne_two hp2) fun q hq' hqn => ?_
  · obtain ⟨r, hr⟩ := hpm
    exact ⟨r, by rw [hr, pow_two, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
  · obtain ⟨e, he⟩ := hq q hq' hqn
    exact ⟨m.factorization q, e, Nat.ordProj_dvd m q, he⟩

/-! ## Row certificates -/

/-- An M1 certificate: the quotient `ZMod m` as the form `A` with a preimage `P` of `1`, and `p`. -/
structure FieldDescentCert where
  m : ℕ
  p : ℕ
  A : List ℕ
  P : List ℕ
  deriving DecidableEq

/-- M1's hypotheses on the row (`n = k − λ`, `c = v / m`; a prime `q ∣ n` is one with no divisor
in `[2, q)`), with `a`, `e` searched below `m`, and the kill `m (m/p) c² < φ(m) n`. -/
def FieldDescentCert.Kills (w : Row) (c : FieldDescentCert) : Prop :=
  (∀ x ∈ w.ms, 0 < x) ∧ 1 < c.m ∧ c.m ∣ w.ms.prod ∧ MapOk w.ms [c.m] [c.A] ∧
    SurjCert w.ms [c.m] [c.A] [c.P] ∧ IsPrimeTD c.p ∧ c.p ≠ 2 ∧ c.m % (c.p * c.p) = 0 ∧
    0 < (w.k : ℤ) - w.lam ∧
    (∀ q ∈ List.range ((w.k - w.lam).toNat + 1), 2 ≤ q → q ∣ (w.k - w.lam).toNat →
        (∀ r ∈ List.range q, 2 ≤ r → q % r ≠ 0) →
          ∃ a ∈ List.range c.m, ∃ e ∈ List.range c.m, c.m % q ^ a = 0 ∧
            (1 + c.m / c.p) % (c.m / q ^ a) = q ^ e % (c.m / q ^ a)) ∧
    c.m * (c.m / c.p) * (w.ms.prod / c.m) ^ 2 < Nat.totient c.m * (w.k - w.lam).toNat

instance FieldDescentCert.instDecidableKills (w : Row) (c : FieldDescentCert) :
    Decidable (c.Kills w) := by
  unfold FieldDescentCert.Kills; infer_instance

/-- A killed row has no SDS. -/
theorem FieldDescentCert.not_hasSDS {w : Row} {c : FieldDescentCert} (h : c.Kills w)
    (inst : Fintype (Grp w.ms)) : ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨-, hm, hmv, hmap, hsurj, hp, hp2, hpm, hn, hq, hkill⟩ := h
  rintro ⟨D, hD⟩
  have : NeZero c.m := ⟨by omega⟩
  have hpp := hp.prime
  have hnZ : (w.k : ℤ) - w.lam = ((w.k - w.lam).toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm
  let φ : Grp w.ms →+ ZMod c.m := linMap w.ms [c.m] [c.A] hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp w.ms) = w.ms.prod / c.m * c.m := by
    rw [Grp.card_eq, Nat.div_mul_cancel hmv]
  have hpm2 : c.p ^ 2 ∣ c.m := by rw [pow_two]; exact Nat.dvd_of_mod_eq_zero hpm
  have hpm' : c.p ∣ c.m := (dvd_pow_self c.p two_ne_zero).trans hpm2
  have hpF' : c.p ∣ c.m / c.p := by
    obtain ⟨r, hr⟩ := hpm2
    exact ⟨r, by rw [hr, pow_two, mul_assoc, Nat.mul_div_cancel_left _ hpp.pos]⟩
  have key := hD.totient_mul_le_of_descent' hm φ hφ hcard hn (Nat.mul_div_cancel' hpm') hpF'
    (hpp.odd_of_ne_two hp2) fun q hq' hqn => by
      rw [hnZ] at hqn
      have hqn' : q ∣ (w.k - w.lam).toNat := Int.natCast_dvd_natCast.1 hqn
      have hpos : 0 < (w.k - w.lam).toNat := by omega
      obtain ⟨a, -, e, -, ha, he⟩ := hq q
        (List.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hpos hqn'))) hq'.two_le hqn'
        (fun r hr hr2 hqr => by
          rcases hq'.eq_one_or_self_of_dvd r (Nat.dvd_of_mod_eq_zero hqr) with h1 | h1
          · omega
          · exact absurd (List.mem_range.1 hr) (by omega))
      exact ⟨a, e, Nat.dvd_of_mod_eq_zero ha, he⟩
  rw [hnZ] at key
  have hle : Nat.totient c.m * (w.k - w.lam).toNat ≤ c.m * (c.m / c.p) * (w.ms.prod / c.m) ^ 2 := by
    exact_mod_cast key
  exact absurd hle (not_le.2 hkill)

end SignedDifferenceSets
