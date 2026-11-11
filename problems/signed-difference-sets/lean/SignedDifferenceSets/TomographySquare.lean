module

public import SignedDifferenceSets.TomographyQuotNC

/-!
# Line tomography when `k − λ = p²` (I23)

An integer vector `Y` on `ZMod p` with autocorrelation `p² [g = 0] + μ` is constant mod `p`
(`congr_of_autocorr_sq`): in `𝓞 ℚ(ζ)` the element `a = Σ Y(t) ζ^t` has `a σ(a) = p²` (`σ ζ = ζ⁻¹`),
`π = ζ − 1` is prime with `π^(p−1) ~ p` and `σ π ~ π`, so `a ~ π^j ~ σ(a)` with `2j = 2(p − 1)`,
`p ∣ a`, and the coordinates in the basis `1, ζ, …, ζ^(p−2)` give `p ∣ Y(t) − Y(p − 1)`.
With sum `p q` and square sum `p q² + p (p − 1)` such a vector is `≡ q ± 1`, and `≡ q + 1` when its
entries stay below `q + p − 1` (`modEq_succ_of_const`). So on `φ : G → ZMod p × ZMod p` (fibres
`c`) with `k − λ = p²`, `s = p q` and `q + p − 1 > c p` every line contraction is `≡ q + 1`, and
the line identity at `0` gives `p ∣ q + 1` (`not_hasSDS_sq`, `not_hasSDS_grp_sq`).
-/

@[expose] public section

open NumberField Polynomial

namespace SignedDifferenceSets.Tomography

section Cyclotomic

variable {p : ℕ} [hp : Fact p.Prime]

theorem pow_zmod_val_add {R : Type*} [CommMonoid R] {z : R} (hz : z ^ p = 1) (s t : ZMod p) :
    z ^ (s + t).val = z ^ s.val * z ^ t.val := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (s.val + t.val) p, pow_add, pow_mul, hz, one_pow, mul_one]

theorem sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (F : ZMod p → M) :
    ∑ t, F t = ∑ i ∈ Finset.range p, F (i : ZMod p) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.sum_bij' (fun t _ => t.val) (fun i _ => (i : ZMod p)) (fun t _ => ?_)
    (fun i _ => Finset.mem_univ _) (fun t _ => ZMod.natCast_zmod_val t)
    (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.1 hi)) (fun t _ => ?_)
  · exact Finset.mem_range.2 (ZMod.val_lt t)
  · rw [ZMod.natCast_zmod_val]

/-- `congr_of_autocorr_sq` in a `p`-th cyclotomic field `K`. -/
theorem congr_of_autocorr_sq_aux (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (Y : ZMod p → ℤ) (μ : ℤ)
    (hY : ∀ g, ∑ t, Y t * Y (t + g) = (if g = 0 then (p : ℤ) ^ 2 else 0) + μ) (t : ZMod p) :
    Y t ≡ Y 0 [ZMOD p] := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_lt.le
  set ζ := IsCyclotomicExtension.zeta p ℚ K
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ K
  set z : 𝓞 K := hζ.toInteger with hzdef
  have hz : IsPrimitiveRoot z p := hζ.toInteger_isPrimitiveRoot
  set e : ZMod p → 𝓞 K := fun t => z ^ t.val with hedef
  have he (s t : ZMod p) : e (s + t) = e s * e t := pow_zmod_val_add hz.pow_eq_one s t
  have he0 : e 0 = 1 := by simp [hedef]
  have hgeom : ∑ i ∈ Finset.range p, z ^ i = 0 := hz.geom_sum_eq_zero hp.out.one_lt
  have hsum : ∑ t, e t = 0 := by
    rw [sum_zmod_eq_sum_range, ← hgeom]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hedef, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)]
  set a : 𝓞 K := ∑ t, (Y t : 𝓞 K) * e t with hadef
  set a' : 𝓞 K := ∑ t, (Y t : 𝓞 K) * e (-t) with ha'def
  -- `a a' = p²`
  have haa : a * a' = (p : 𝓞 K) ^ 2 := by
    have h1 : a * a' = ∑ g, ((∑ t, Y t * Y (t + g) : ℤ) : 𝓞 K) * e g := by
      rw [hadef, ha'def, Finset.sum_mul_sum, Finset.sum_comm]
      have h2 (t : ZMod p) : ∑ s, (Y s : 𝓞 K) * e s * ((Y t : 𝓞 K) * e (-t)) =
          ∑ g, (Y t : 𝓞 K) * Y (t + g) * e g := by
        refine Fintype.sum_equiv (Equiv.subRight t) _ _ fun s => ?_
        have e1 : t + (s - t) = s := by abel
        have e2 : e s * e (-t) = e (s - t) := by rw [← he, sub_eq_add_neg]
        simp only [Equiv.subRight_apply, e1, ← e2]
        ring
      simp only [h2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      push_cast
      rw [Finset.sum_mul]
    rw [h1]
    simp only [hY]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, he0, mul_one]
  -- the conjugation `ζ ↦ ζ^(p-1)`
  have hcop : (p - 1).Coprime p := Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp.out).2
    (Nat.not_dvd_of_pos_of_lt (by have := hp.out.two_le; omega) (by omega))
  have hμ : IsPrimitiveRoot (ζ ^ (p - 1)) p := hζ.pow_of_coprime (p - 1) hcop
  set σ : K ≃ₐ[ℚ] K :=
    IsCyclotomicExtension.fromZetaAut hμ (cyclotomic.irreducible_rat hp.out.pos) with hσdef
  have hσ : σ ζ = ζ ^ (p - 1) := IsCyclotomicExtension.fromZetaAut_spec hμ _
  set τ : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom σ.toAlgHom.toRingHom with hτdef
  have hτz : τ z = z ^ (p - 1) := by
    apply RingOfIntegers.ext
    simp only [hτdef, RingOfIntegers.mapRingHom_apply, hzdef]
    push_cast
    exact hσ
  have hτe (t : ZMod p) : τ (e t) = e (-t) := by
    have h1 : e t * τ (e t) = 1 := by
      simp only [hedef, map_pow, hτz]
      rw [← mul_pow, ← pow_succ', hp1, hz.pow_eq_one, one_pow]
    have h2 : e (-t) * e t = 1 := by rw [← he, neg_add_cancel, he0]
    calc τ (e t) = (e (-t) * e t) * τ (e t) := by rw [h2, one_mul]
      _ = e (-t) * (e t * τ (e t)) := by ring
      _ = e (-t) := by rw [h1, mul_one]
  have hτa : τ a = a' := by
    simp only [hadef, ha'def, map_sum, map_mul, map_intCast, hτe]
  -- `π = ζ - 1`
  set π : 𝓞 K := z - 1 with hπdef
  have hπ : Prime π := hζ.zeta_sub_one_prime'
  have hpπ : Associated (π ^ (p - 1)) (p : 𝓞 K) :=
    IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ
  have hτπ : Associated π (τ π) := by
    rw [hπdef, map_sub, map_one, hτz]
    exact hz.associated_sub_one_pow_sub_one_of_coprime hcop
  have hadvd : a ∣ π ^ (2 * (p - 1)) := by
    have h1 : a ∣ (p : 𝓞 K) ^ 2 := ⟨a', haa.symm⟩
    have h2 : Associated (π ^ (2 * (p - 1))) ((p : 𝓞 K) ^ 2) := by
      rw [mul_comm, pow_mul]; exact hpπ.pow_pow
    exact h1.trans h2.symm.dvd
  obtain ⟨j, -, haj⟩ := (dvd_prime_pow hπ _).1 hadvd
  have ha'j : Associated a' (π ^ j) := by
    rw [← hτa]
    have h1 : Associated (τ a) (τ (π ^ j)) := haj.map τ
    rw [map_pow] at h1
    exact h1.trans hτπ.symm.pow_pow
  have hjle : p - 1 ≤ j := by
    have h1 : Associated ((p : 𝓞 K) ^ 2) (π ^ (2 * j)) := by
      rw [← haa, two_mul, pow_add]; exact haj.mul_mul ha'j
    have h2 : Associated (π ^ (2 * (p - 1))) (π ^ (2 * j)) := by
      rw [mul_comm 2 (p - 1), pow_mul]; exact hpπ.pow_pow.trans h1
    have h3 := (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 h2.dvd
    omega
  have hpa : (p : 𝓞 K) ∣ a :=
    hpπ.symm.dvd.trans ((pow_dvd_pow π hjle).trans haj.symm.dvd)
  -- coordinates in the power basis `1, ζ, …, ζ^(p-2)`
  set last : ZMod p := ((p - 1 : ℕ) : ZMod p) with hlast
  have hrange : Finset.range p = Finset.range (p - 1 + 1) := by rw [hp1]
  have ha2 : a = ∑ i ∈ Finset.range (p - 1), ((Y i - Y last : ℤ) : 𝓞 K) * z ^ i := by
    have h1 : a = ∑ i ∈ Finset.range p, (Y (i : ZMod p) : 𝓞 K) * z ^ i := by
      rw [hadef, sum_zmod_eq_sum_range]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hedef, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)]
    have h2 := hgeom
    rw [hrange, Finset.sum_range_succ] at h1 h2
    rw [h1, show z ^ (p - 1) = -∑ i ∈ Finset.range (p - 1), z ^ i by linear_combination h2]
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  obtain ⟨w, hw⟩ := hpa
  set pb := hζ.integralPowerBasis with hpbdef
  have hdim : pb.dim = p - 1 := by rw [hζ.integralPowerBasis_dim, Nat.totient_prime hp.out]
  have hgen : pb.gen = z := hζ.integralPowerBasis_gen
  set c : Fin pb.dim → ℤ := pb.basis.equivFun w with hcdef
  have hwsum : w = ∑ i, c i • pb.basis i := (pb.basis.sum_equivFun w).symm
  set g : Fin pb.dim → ℤ := fun i => (Y (i : ℕ) - Y last) - p * c i with hgdef
  have hg : ∑ i, g i • pb.basis i = 0 := by
    have e0 (i : Fin pb.dim) : g i • pb.basis i =
        (Y ((i : ℕ) : ZMod p) - Y last) • pb.basis i - ((p : ℤ) * c i) • pb.basis i := by
      simp only [hgdef, sub_smul]
    rw [Finset.sum_congr rfl fun i _ => e0 i, Finset.sum_sub_distrib]
    have e1 : ∑ i : Fin pb.dim, (Y ((i : ℕ) : ZMod p) - Y last) • pb.basis i = a := by
      rw [ha2]
      simp only [PowerBasis.coe_basis, hgen, zsmul_eq_mul]
      rw [Fin.sum_univ_eq_sum_range (fun i => ((Y (i : ZMod p) - Y last : ℤ) : 𝓞 K) * z ^ i),
        hdim]
    have e2 : ∑ i, ((p : ℤ) * c i) • pb.basis i = (p : 𝓞 K) * w := by
      rw [hwsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [mul_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [e1, e2, hw, sub_self]
  have hli := Fintype.linearIndependent_iff.1 pb.basis.linearIndependent g hg
  have hlastc : ∀ i < p - 1, Y (i : ZMod p) ≡ Y last [ZMOD p] := by
    intro i hi
    have := hli ⟨i, by rw [hdim]; exact hi⟩
    simp only [hgdef] at this
    exact (Int.modEq_iff_dvd.2 ⟨c _, by linear_combination this⟩).symm
  have hall : ∀ t : ZMod p, Y t ≡ Y last [ZMOD p] := by
    intro t
    rcases Nat.lt_or_ge t.val (p - 1) with h | h
    · have := hlastc t.val h
      rwa [ZMod.natCast_zmod_val] at this
    · have : t = last := by
        rw [hlast, ← ZMod.natCast_zmod_val t]
        congr 1
        have := ZMod.val_lt t
        omega
      rw [this]
  exact (hall t).trans (hall 0).symm

/-- An integer vector on `ZMod p` with autocorrelation `p² [g = 0] + μ` is constant mod `p`. -/
theorem congr_of_autocorr_sq (Y : ZMod p → ℤ) (μ : ℤ)
    (hY : ∀ g, ∑ t, Y t * Y (t + g) = (if g = 0 then (p : ℤ) ^ 2 else 0) + μ) (t : ZMod p) :
    Y t ≡ Y 0 [ZMOD p] := by
  have : NeZero ((p : ℕ) : ℚ) := ⟨by exact_mod_cast hp.out.ne_zero⟩
  exact @congr_of_autocorr_sq_aux p hp (CyclotomicField p ℚ) _ _
    (CyclotomicField.isCyclotomicExtension p ℚ) Y μ hY t

/-- A vector on `ZMod p`, constant mod `p`, with sum `p q`, square sum `p q² + p (p − 1)` and
entries at most `f < q + p − 1` is `≡ q + 1 (mod p)`. -/
theorem modEq_succ_of_const (Y : ZMod p → ℤ) {q f : ℤ} (hc : ∀ t, Y t ≡ Y 0 [ZMOD p])
    (hs : ∑ t, Y t = p * q) (hq : ∑ t, Y t * Y t = p * q ^ 2 + p * (p - 1))
    (hb : ∀ t, Y t ≤ f) (hf : f < q + p - 1) : Y 0 ≡ q + 1 [ZMOD p] := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by
    have : NeZero p := ⟨hp.out.ne_zero⟩
    rw [Finset.card_univ, ZMod.card]
  choose r hr using fun t => (hc t).symm.dvd
  have e (t : ZMod p) : Y t = Y 0 + p * r t := by linear_combination hr t
  obtain ⟨R, hR⟩ : ∃ R, ∑ t, r t = R := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, ∑ t, r t * r t = S := ⟨_, rfl⟩
  have h1 : Y 0 + R = q := by
    have : ∑ t, Y t = p * Y 0 + p * R := by
      rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_add_distrib, Finset.sum_const, hcard,
        nsmul_eq_mul, ← Finset.mul_sum, hR]
    apply mul_left_cancel₀ hp0
    linear_combination this.symm.trans hs
  have hsq : ∑ t, Y t * Y t = p * (Y 0 * Y 0) + 2 * p * Y 0 * R + p * p * S := by
    rw [Finset.sum_congr rfl fun t _ => (by linear_combination (Y t + Y 0 + p * r t) * e t :
        Y t * Y t = Y 0 * Y 0 + 2 * p * Y 0 * r t + p * p * (r t * r t)),
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.mul_sum, hR, hS]
  have h2 : (R - 1) * (R + 1) = p * (S - 1) := by
    apply mul_left_cancel₀ hp0
    linear_combination -(hsq.symm.trans hq) + p * (Y 0 + R + q) * h1
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  rcases hpr.dvd_or_dvd ⟨S - 1, h2⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- `Y ≡ q - 1`: some entry reaches `q + p - 1`
    exfalso
    have hsum0 : ∑ t, (Y t - q) = 0 := by
      rw [Finset.sum_sub_distrib, hs, Finset.sum_const, hcard, nsmul_eq_mul]; ring
    obtain ⟨t, ht⟩ : ∃ t, 0 ≤ Y t - q := by
      by_contra hneg
      simp only [not_exists, not_le] at hneg
      have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun t _ => hneg t
      simp only [Finset.sum_const_zero] at this
      linarith
    have hdvd : (p : ℤ) ∣ Y t - q + 1 := ⟨r t - m, by linear_combination e t + h1 - hm⟩
    have := Int.le_of_dvd (by linarith) hdvd
    have := hb t
    linarith
  · exact Int.modEq_iff_dvd.2 ⟨m, by linear_combination hm - h1⟩

end Cyclotomic

section Quot

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- No SDS on `G` when `φ : G → ZMod p × ZMod p` is onto with fibres of `c`, `k − λ = p²`,
`s = p q` (`s² = k + λ (v − 1)`), `c p < q + p − 1` and `p ∤ q + 1`. -/
theorem not_hasSDS_sq (p : ℕ) [hp : Fact p.Prime] {c k : ℕ} {lam s q : ℤ}
    (φ : G →+ ZMod p × ZMod p) (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * (p * p)) (hs : s * s = k + lam * ((c : ℤ) * p * p - 1))
    (hn : (k : ℤ) - lam = p ^ 2) (hq : s = p * q) (hbox : (c : ℤ) * p < q + p - 1)
    (hq1 : ¬ (p : ℤ) ∣ q + 1) : ¬ HasSDS G k lam := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hqq : q ^ 2 = 1 + lam * c := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hp0)
    linear_combination hs + hn - (s + p * q) * hq
  have key : ∀ D : G → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s → False := by
    intro D hD hsum
    have hline (j : ℕ) : contract (lineQ p j φ) D 0 ≡ q + 1 [ZMOD p] := by
      have hdem := demands_lineQ hφ hcard hD j
      have hY (g : ZMod p) : ∑ t, contract (lineQ p j φ) D t * contract (lineQ p j φ) D (t + g) =
          (if g = 0 then (p : ℤ) ^ 2 else 0) + lam * ((c * p : ℕ) : ℤ) := by
        by_cases hg : g = 0
        · subst hg
          simp only [add_zero, ↓reduceIte]
          rw [hdem.sq]
          push_cast
          linear_combination hn
        · rw [hdem.corr g hg]
          simp [hg]
      refine modEq_succ_of_const _ (congr_of_autocorr_sq _ _ hY) (f := ((c * p : ℕ) : ℤ)) ?_ ?_
        (fun t => (le_abs_self _).trans (hdem.bound t)) (by push_cast; linarith)
      · rw [sum_contractQ, hsum, hq]
      · rw [hdem.sq]
        push_cast
        linear_combination hn - p * hqq
    have e := sum_contract_linesQ φ D 0
    simp only [map_zero] at e
    have h1 : ((∑ j ∈ Finset.range (p + 1), contract (lineQ p j φ) D 0 : ℤ) : ZMod p) =
        ((q + 1 : ℤ) : ZMod p) := by
      push_cast
      rw [Finset.sum_congr rfl fun j _ => (ZMod.intCast_eq_intCast_iff _ _ _).2 (hline j)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
        ZMod.natCast_self, zero_add, one_mul]
      push_cast
      ring
    rw [e, hsum, hq] at h1
    push_cast at h1
    simp only [ZMod.natCast_self, zero_mul, add_zero] at h1
    exact hq1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by push_cast; exact h1.symm))
  rintro ⟨D, hD⟩
  have hdem := demands_lineQ hφ hcard hD 0
  set a := contract (lineQ p 0 φ) D
  have hp1 : 0 < p := hp.out.pos
  have hsq : (∑ h, a h) * (∑ h, a h) = s * s := by
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hdem.sq, Finset.sum_congr rfl fun g hg => hdem.corr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card, hs, nsmul_eq_mul, Nat.cast_sub hp1]
    push_cast
    ring
  rw [sum_contractQ] at hsq
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key D hD h1
  · refine key _ hD.neg ?_
    simp only [SignType.coe_neg, Finset.sum_neg_distrib, h1, neg_neg]

/-- `not_hasSDS_sq` on the table's group `Grp ms`, with `φ` given by the forms `A` (onto by the
preimages `P`). -/
theorem not_hasSDS_grp_sq {ms : List ℕ} (p : ℕ) [Fact p.Prime] {A P : List (List ℕ)}
    (hmap : MapOk ms [p, p] A) (hsurj : SurjCert ms [p, p] A P) (inst : Fintype (Grp ms))
    {c k : ℕ} {lam s q : ℤ} (hcard : ms.prod = c * (p * p))
    (hs : s * s = k + lam * ((c : ℤ) * p * p - 1)) (hn : (k : ℤ) - lam = p ^ 2)
    (hq : s = p * q) (hbox : (c : ℤ) * p < q + p - 1) (hq1 : ¬ (p : ℤ) ∣ q + 1) :
    ¬ @HasSDS (Grp ms) _ inst k lam := by
  let φ : Grp ms →+ ZMod p × ZMod p := linMap ms [p, p] A hmap
  have hcardG : Fintype.card (Grp ms) = c * (p * p) := by rw [Grp.card_eq, hcard]
  exact not_hasSDS_sq p φ (linMap_surjective hmap hsurj) hcardG hs hn hq hbox hq1

end Quot

end SignedDifferenceSets.Tomography
