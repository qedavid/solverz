module

public import SignedDifferenceSets.MaDivided

/-!
# C36: the divided contraction two levels below a Ma quotient

On a C21 quotient `ZMod (r p p) × K` with `b ≥ 2` (any prime `p`), Ma's step holds at both levels
`ZMod (r p p) × K` and `ZMod (r p) × K`: one level down the coset sums agree with `p` times the
coset sums above them mod `p^b` (`Ma.dvd_contract_quot_sub`), so two levels down, on
`ZMod r × K` (fibres `p² c`), they are divisible by `p²`. `Z = W / p²` has entries in `[−c, c]`,
square sum `Q` with `p⁴ Q = k + λ (p² c − 1)`, autocorrelation `t` with `p² t = λ c`, sum `±s'`
with `p² s' = s`, and an absolute sum `A` with `p² A ≤ k`, `k − p² A` even; a list of bounds
`k'` covers every such `A` (`k'` itself for odd `p`; two bounds for `p = 2`, where the parity is
lost), and `noVector` with each bound rules the SDS out (`IsSDS.false_of_maDivided2`).
`MaDiv2Cert` checks a row's hypotheses by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets

open Ma

/-- C21's step one level down: on a C21 quotient, the coset sum below `h` is `p` times the coset
sum at `h`, mod `p^b`. -/
theorem Ma.dvd_contract_quot_sub {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K]
    [Fintype K] [DecidableEq K] {p r i e b c k : ℕ} {lam : ℤ} [hp : Fact p.Prime]
    [NeZero (r * p)] [NeZero r] {φ : G →+ ZMod (r * p) × K} (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * Fintype.card (ZMod (r * p) × K)) (hr : 0 < r) (hi : 0 < i)
    (hc : ∀ x : K, p ^ i • x = -x) (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam) (hb : 2 * b ≤ e)
    (hcert : CycloFacts p r) {D : G → SignType} (hD : IsSDS k lam D) (h : ZMod (r * p) × K) :
    (p : ℤ) ^ b ∣ contract ((maQuot K r p).comp φ) D (maQuot K r p h) - p * contract φ D h := by
  set ψ := maQuot K r p with hψdef
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, b⟩
    obtain ⟨a', ha'⟩ := ZMod.ringHom_surjective (ZMod.castHom (dvd_mul_right r p) (ZMod r)) a
    exact ⟨(a', b), by simp [hψdef, maQuot, ha']⟩
  set u : ZMod (r * p) × K := ((r : ZMod (r * p)), 0) with hu
  have hcardH : Fintype.card (ZMod (r * p) × K) = p * Fintype.card (ZMod r × K) := by
    rw [Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  set Y := contract φ D with hYdef
  have hstep : ∀ h, (p : ℤ) ^ b ∣ Y (h + u) - Y h := by
    rintro ⟨x, kk⟩
    simpa [hu] using Ma.dvd_contract_sub hφ hcard hr hi hc hn hb hcert hD x kk
  have hiter : ∀ (m : ℕ) h, (p : ℤ) ^ b ∣ Y (h + m • u) - Y h := by
    intro m
    induction m with
    | zero => intro h; simp
    | succ m ih =>
      intro h
      have := dvd_add (hstep (h + m • u)) (ih h)
      rw [succ_nsmul, ← add_assoc]
      convert this using 1
      ring
  have hker : ∀ d, ψ d = 0 → ∃ m : ℕ, d = m • u := by
    rintro ⟨d1, d2⟩ hd
    have h1 : ZMod.castHom (dvd_mul_right r p) (ZMod r) d1 = 0 := congrArg Prod.fst hd
    have h2 : d2 = 0 := congrArg Prod.snd hd
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h1
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h1
    refine ⟨m, Prod.ext ?_ (by simp [hu, h2])⟩
    simp only [hu, Prod.smul_fst, nsmul_eq_mul]
    rw [← ZMod.natCast_zmod_val d1, hm, Nat.cast_mul]
    ring
  rw [contract_comp]
  have hfib := card_fibre_eq hψ hcardH (ψ h)
  rw [fibre] at hfib
  have hsplit : ∑ h' ∈ Finset.univ.filter (fun h' => ψ h' = ψ h), Y h' =
      ∑ h' ∈ Finset.univ.filter (fun h' => ψ h' = ψ h), (Y h' - Y h) + (p : ℤ) * Y h := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hfib, nsmul_eq_mul]
    ring
  rw [hsplit, add_sub_cancel_right]
  refine Finset.dvd_sum fun h' hh' => ?_
  have hh' : ψ (h' - h) = 0 := by
    rw [map_sub, (Finset.mem_filter.1 hh').2, sub_self]
  obtain ⟨m, hm⟩ := hker _ hh'
  have : h' = h + m • u := by rw [← hm]; abel
  rw [this]
  exact hiter m h

/-- C36: two levels below a C21 quotient `ZMod (r p p) × K` with `b ≥ 2`, `Z = W / p²` meets
`DemandsQ c Q t k'` for some bound `k'` of `bounds`, with `(Σ Z)² = s'²`; a `noVector` check with
each bound leaves no SDS. -/
theorem IsSDS.false_of_maDivided2 {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K]
    [Fintype K] {p r i e b c k : ℕ} {lam Q t s' : ℤ} {bounds : List ℕ} [Indexed (ZMod r × K)]
    [hp : Fact p.Prime] [NeZero (r * p * p)] [NeZero (r * p)] [NeZero r]
    {φ : G →+ ZMod (r * p * p) × K} (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * Fintype.card (ZMod (r * p * p) × K)) (hr : 0 < r) (hi : 0 < i)
    (hc : ∀ x : K, p ^ i • x = -x) (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam) (hb : 2 * b ≤ e)
    (hb2 : 2 ≤ b) (hcert1 : CycloFacts p (r * p)) (hcert2 : CycloFacts p r)
    (hQ : (p : ℤ) ^ 4 * Q = k + lam * ((p * p * c : ℕ) - 1)) (ht : (p : ℤ) ^ 2 * t = lam * c)
    (hs : ((p : ℤ) ^ 2 * s') * ((p : ℤ) ^ 2 * s') = k + lam * ((Fintype.card G : ℤ) - 1))
    (hbounds : ∀ A ∈ List.range (k + 1), p * p * A ≤ k → (k - p * p * A) % 2 = 0 →
      ∃ k' ∈ bounds, A ≤ k' ∧ (k' - A) % 2 = 0)
    (hnv : ∀ k' ∈ bounds,
      noVector (Indexed.size (ZMod r × K)) (Indexed.addIdx (ZMod r × K)) c Q t k' s' = true)
    {D : G → SignType} (hD : IsSDS k lam D) : False := by
  classical
  have hrp : 0 < r * p := Nat.mul_pos hr hp.out.pos
  set ψ1 := maQuot K (r * p) p with hψ1def
  set ψ2 := maQuot K r p with hψ2def
  have hsurj (r' : ℕ) [NeZero (r' * p)] [NeZero r'] : Function.Surjective (maQuot K r' p) := by
    rintro ⟨a, b⟩
    obtain ⟨a', ha'⟩ := ZMod.ringHom_surjective (ZMod.castHom (dvd_mul_right r' p) (ZMod r')) a
    exact ⟨(a', b), by simp [maQuot, ha']⟩
  set χ1 := ψ1.comp φ with hχ1def
  set χ2 := ψ2.comp χ1 with hχ2def
  have hχ1 : Function.Surjective χ1 := (hsurj (r * p)).comp hφ
  have hχ2 : Function.Surjective χ2 := (hsurj r).comp hχ1
  have hcard1 : Fintype.card G = p * c * Fintype.card (ZMod (r * p) × K) := by
    rw [hcard, Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hcard2 : Fintype.card G = p * p * c * Fintype.card (ZMod r × K) := by
    rw [hcard, Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hfib := card_fibre_eq hχ2 hcard2
  set W := contract χ2 D with hWdef
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hb1 : 0 < b := by omega
  -- one level down: `p ∣ W₁`; two levels down: `p² ∣ W`
  have hW1 : ∀ y, (p : ℤ) ∣ contract χ1 D y := by
    intro y
    obtain ⟨h, rfl⟩ := hsurj (r * p) y
    have h1 := Ma.dvd_contract_quot_sub hφ hcard hrp hi hc hn hb hcert1 hD h
    have h2 := dvd_add ((dvd_pow_self (p : ℤ) hb1.ne').trans h1)
      (dvd_mul_right (p : ℤ) (contract φ D h))
    simpa [hχ1def, hψ1def] using h2
  have hdiv : ∀ y, (p : ℤ) ^ 2 ∣ W y := by
    intro y
    obtain ⟨h1, rfl⟩ := hsurj r y
    have h2 := Ma.dvd_contract_quot_sub (φ := χ1) hχ1 hcard1 hr hi hc hn hb hcert2 hD h1
    have h3 : (p : ℤ) ^ 2 ∣ (p : ℤ) ^ b := pow_dvd_pow _ hb2
    have h4 : (p : ℤ) ^ 2 ∣ (p : ℤ) * contract χ1 D h1 := by
      rw [pow_two]; exact mul_dvd_mul_left _ (hW1 h1)
    have := dvd_add (h3.trans h2) h4
    simpa [hWdef, hχ2def, hψ2def] using this
  set Z : ZMod r × K → ℤ := fun y => W y / p ^ 2 with hZdef
  have hWZ : ∀ y, W y = p ^ 2 * Z y := fun y => (Int.mul_ediv_cancel' (hdiv y)).symm
  have hpc1 : 1 ≤ p * p * c := by
    rcases Nat.eq_zero_or_pos (p * p * c) with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card G)
      rw [hcard2, h0, zero_mul] at this
      omega
    · exact h0
  have hsqW := hD.contract_sq χ2
  rw [← hWdef, hfib 0, Nat.cast_sub hpc1, Nat.cast_one] at hsqW
  have hcorrW : ∀ g, g ≠ 0 → ∑ y, W y * W (y + g) = lam * ((p * p * c : ℕ) : ℤ) := fun g hg => by
    rw [hD.contract_autocorr χ2 g hg, hfib]
  have hp2 : (0 : ℤ) < p ^ 2 := by positivity
  have habsW : ∑ y, |W y| = p ^ 2 * ∑ y, |Z y| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hWZ y, abs_mul, abs_of_pos hp2]
  -- the bound `k'` that covers the absolute sum
  set A := ∑ y, |Z y| with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun y _ => abs_nonneg _
  have habs := hD.sum_abs_contract_le χ2
  have hpar := hD.sum_abs_contract_parity χ2
  rw [← hWdef, habsW] at habs hpar
  obtain ⟨n, hnA⟩ : ∃ n : ℕ, A = n := ⟨A.toNat, (Int.toNat_of_nonneg hA0).symm⟩
  rw [hnA] at habs hpar
  have hm : ((p * p * n : ℕ) : ℤ) = (p : ℤ) ^ 2 * n := by push_cast; ring
  have hle : p * p * n ≤ k := by
    have : ((p * p * n : ℕ) : ℤ) ≤ k := by rw [hm]; exact habs
    exact_mod_cast this
  have hpar' : (k - p * p * n) % 2 = 0 := by
    rw [← hm] at hpar
    have hn' : n ≤ p * p * n := Nat.le_mul_of_pos_left n (Nat.mul_pos hp.out.pos hp.out.pos)
    generalize p * p * n = m at *
    omega
  have hmem : n ∈ List.range (k + 1) := by
    have hn' : n ≤ p * p * n := Nat.le_mul_of_pos_left n (Nat.mul_pos hp.out.pos hp.out.pos)
    exact List.mem_range.2 (by omega)
  obtain ⟨k', hk', hAk, hpk⟩ := hbounds n hmem hle hpar'
  have hdem : DemandsQ c Q t k' Z := by
    refine ⟨fun y => ?_, ?_, fun g hg => ?_, ?_, ?_⟩
    · have h1 := abs_contract_le χ2 D y
      rw [hfib y, ← hWdef, hWZ y, abs_mul, abs_of_pos hp2] at h1
      push_cast at h1
      have : (p : ℤ) ^ 2 * |Z y| ≤ (p : ℤ) ^ 2 * c := by linarith
      exact le_of_mul_le_mul_left this hp2
    · have h2 : (p : ℤ) ^ 4 * ∑ y, Z y * Z y = (p : ℤ) ^ 4 * Q := by
        rw [hQ, Finset.mul_sum, ← hsqW]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hWZ y]
        ring
      exact mul_left_cancel₀ (by positivity) h2
    · have h2 : (p : ℤ) ^ 4 * ∑ y, Z y * Z (y + g) = (p : ℤ) ^ 4 * t := by
        rw [Finset.mul_sum]
        have : ∑ y, (p : ℤ) ^ 4 * (Z y * Z (y + g)) = ∑ y, W y * W (y + g) :=
          Finset.sum_congr rfl fun y _ => by rw [hWZ y, hWZ (y + g)]; ring
        rw [this, hcorrW g hg]
        push_cast
        linear_combination -(p : ℤ) ^ 2 * ht
      exact mul_left_cancel₀ (by positivity) h2
    · rw [← hAdef, hnA]
      exact_mod_cast hAk
    · rw [← hAdef, hnA]
      have := hpk
      zify [hAk] at this
      exact this
  have hsqZ : (∑ y, Z y) * (∑ y, Z y) = s' * s' := by
    have hH1 : 1 ≤ Fintype.card (ZMod r × K) := Fintype.card_pos
    have hW2 : (∑ y, W y) * (∑ y, W y) = ((p : ℤ) ^ 2 * s') * ((p : ℤ) ^ 2 * s') := by
      rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
      simp only [add_zero]
      rw [hsqW, Finset.sum_congr rfl fun g hg => hcorrW g (Finset.ne_of_mem_erase hg),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hs,
        hcard2, nsmul_eq_mul, Nat.cast_sub hH1]
      push_cast
      ring
    have hsumW : ∑ y, W y = p ^ 2 * ∑ y, Z y := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => hWZ y
    rw [hsumW] at hW2
    have : (p : ℤ) ^ 4 * ((∑ y, Z y) * (∑ y, Z y)) = (p : ℤ) ^ 4 * (s' * s') := by
      linear_combination hW2
    exact mul_left_cancel₀ (by positivity) this
  exact false_of_noVectorQ' (hnv k' hk') hdem hsqZ

/-! ### Rows -/

/-- A C36 certificate: C21's fields at the top (`p`, `r`, `i`, `e`, `b ≥ 2`, `ks ≠ []`, forms `A`
onto `ZMod (r p p) × Grp ks` with preimages `P`), the bounds and the divided demands. -/
structure MaDiv2Cert where
  p : ℕ
  r : ℕ
  i : ℕ
  e : ℕ
  b : ℕ
  ks : List ℕ
  A : List (List ℕ)
  P : List (List ℕ)
  bounds : List ℕ
  Q : ℤ
  t : ℤ
  s' : ℤ
  deriving DecidableEq

/-- C36's hypotheses on the row, `c = |G| / (r p p |K|)`, `(p, r p)` and `(p, r)` among
`MaRows.maPairs`. -/
def MaDiv2Cert.Valid (w : Row) (c : MaDiv2Cert) : Prop :=
  IsPrimeTD c.p ∧ 0 < c.r ∧ 0 < c.i ∧ c.ks ≠ [] ∧ (∀ d ∈ c.ks, d ∣ c.p ^ c.i + 1) ∧
    MapOk w.ms (c.r * c.p * c.p :: c.ks) c.A ∧ SurjCert w.ms (c.r * c.p * c.p :: c.ks) c.A c.P ∧
    c.r * c.p * c.p * c.ks.prod ∣ w.ms.prod ∧ (c.p : ℤ) ^ c.e ∣ w.k - w.lam ∧ 2 * c.b ≤ c.e ∧
    2 ≤ c.b ∧
    (c.p : ℤ) ^ 4 * c.Q =
      w.k + w.lam * ((c.p * c.p * (w.ms.prod / (c.r * c.p * c.p * c.ks.prod)) : ℕ) - 1) ∧
    (c.p : ℤ) ^ 2 * c.t = w.lam * (w.ms.prod / (c.r * c.p * c.p * c.ks.prod) : ℕ) ∧
    ((c.p : ℤ) ^ 2 * c.s') * ((c.p : ℤ) ^ 2 * c.s') = w.k + w.lam * ((w.ms.prod : ℤ) - 1) ∧
    (∀ A ∈ List.range (w.k + 1), c.p * c.p * A ≤ w.k → (w.k - c.p * c.p * A) % 2 = 0 →
      ∃ k' ∈ c.bounds, A ≤ k' ∧ (k' - A) % 2 = 0) ∧
    (c.p, c.r * c.p) ∈ MaRows.maPairs ∧ (c.p, c.r) ∈ MaRows.maPairs

instance MaDiv2Cert.instDecidableValid (w : Row) (c : MaDiv2Cert) : Decidable (c.Valid w) := by
  unfold MaDiv2Cert.Valid; infer_instance

/-- A row meeting C36's hypotheses whose divided search on `Grp (r :: ks)` finds no vector for any
bound has no SDS, whatever `Fintype` instance its group carries. -/
theorem MaDiv2Cert.not_hasSDS {w : Row} {c : MaDiv2Cert} (h : c.Valid w)
    (hpos : ∀ m ∈ c.r :: c.ks, 0 < m) (inst : Fintype (Grp w.ms))
    (hn : ∀ k' ∈ c.bounds, noVector (@Indexed.size (Grp (c.r :: c.ks)) _ (Grp.indexed _ hpos))
      (@Indexed.addIdx (Grp (c.r :: c.ks)) _ (Grp.indexed _ hpos))
      ((w.ms.prod / (c.r * c.p * c.p * c.ks.prod) : ℕ) : ℤ) c.Q c.t k' c.s' = true) :
    ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨p, r, i, e, b, ks, A, P, bounds, Q, t, s'⟩ := c
  obtain ⟨hp, hr, hi, hne, hks, hmap, hsurj, hprod, hn', hbe, hb2, hQ, ht, hs, hbounds, hpair1,
    hpair2⟩ := h
  dsimp only at *
  rintro ⟨D, hD⟩
  obtain ⟨k₀, ks, rfl⟩ := List.exists_cons_of_ne_nil hne
  have : Fact p.Prime := ⟨hp.prime⟩
  have : NeZero (r * p * p) := ⟨(Nat.mul_pos (Nat.mul_pos hr hp.prime.pos) hp.prime.pos).ne'⟩
  have : NeZero (r * p) := ⟨(Nat.mul_pos hr hp.prime.pos).ne'⟩
  have : NeZero r := ⟨hr.ne'⟩
  let _ : Fintype (Grp (k₀ :: ks)) :=
    Grp.fintype _ fun d hd => Nat.pos_of_dvd_of_pos (hks d hd) (by positivity)
  let φ : Grp w.ms →+ ZMod (r * p * p) × Grp (k₀ :: ks) :=
    linMap w.ms (r * p * p :: k₀ :: ks) A hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp w.ms) = w.ms.prod / (r * p * p * (k₀ :: ks).prod) *
      Fintype.card (ZMod (r * p * p) × Grp (k₀ :: ks)) := by
    rw [Fintype.card_prod, ZMod.card, Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hconj (x : Grp (k₀ :: ks)) : p ^ i • x = -x := by
    have := Grp.nsmul_eq_zero (N := p ^ i + 1) (k₀ :: ks) hks x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  let _ : Indexed (ZMod r × Grp (k₀ :: ks)) := Grp.indexed (r :: k₀ :: ks) hpos
  exact hD.false_of_maDivided2 hφ hcard hr hi hconj hn' hbe hb2
    (MaRows.cycloFacts_of_mem_maPairs hpair1) (MaRows.cycloFacts_of_mem_maPairs hpair2) hQ ht
    (by rw [Grp.card_eq]; exact hs) hbounds hn

end SignedDifferenceSets
