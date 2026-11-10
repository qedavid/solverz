module

public import SignedDifferenceSets.MaEdge
public import SignedDifferenceSets.ContractionCheck
public import SignedDifferenceSets.OrbitSearch

/-!
# C34: the divided contraction below a Ma quotient

On a C21 quotient `H = ZMod (r p) × K` with `b ≥ 1`, the coset sums `W` along `G → ZMod r × K`
(fibres `p c`) are all divisible by `p` (C33's step, `Ma.dvd_contract_quot`). For odd `p`,
`Z = W / p` has entries in `[−c, c]`, square sum `Q` with `p² Q = k + λ (p c − 1)`,
autocorrelation `t` with `p t = λ c` at every shift `≠ 0`, sum `±s'` with `p s' = s`, and
absolute sum at most `k'` (`k < p (k' + 2)`, `k' ≡ k mod 2`); `noVector` with these demands
(`false_of_noVectorQ'`) rules the SDS out (`IsSDS.false_of_maDivided`). `MaDivCert` checks a
row's hypotheses by `decide +kernel`; the search itself is a separate `noVector` check.
-/

@[expose] public section

namespace SignedDifferenceSets

open Ma

section Demands

variable {H : Type*} [AddCommGroup H] [Fintype H]

/-- `Demands` with a free square sum `Q` and autocorrelation `t`. -/
structure DemandsQ (c : ℕ) (Q t : ℤ) (k : ℕ) (b : H → ℤ) : Prop where
  bound : ∀ h, |b h| ≤ c
  sq : ∑ h, b h * b h = Q
  corr : ∀ g, g ≠ 0 → ∑ h, b h * b (h + g) = t
  abs : ∑ h, |b h| ≤ k
  parity : ((k : ℤ) - ∑ h, |b h|) % 2 = 0

variable {c k : ℕ} {Q t : ℤ} {b : H → ℤ}

theorem DemandsQ.neg (hb : DemandsQ c Q t k b) : DemandsQ c Q t k (fun h => -b h) where
  bound h := by rw [abs_neg]; exact hb.bound h
  sq := by simpa only [neg_mul_neg] using hb.sq
  corr g hg := by simpa only [neg_mul_neg] using hb.corr g hg
  abs := by simpa only [abs_neg] using hb.abs
  parity := by simpa only [abs_neg] using hb.parity

theorem DemandsQ.translate (hb : DemandsQ c Q t k b) (h₀ : H) :
    DemandsQ c Q t k (fun h => b (h + h₀)) where
  bound h := hb.bound _
  sq := by rw [← hb.sq]; exact Fintype.sum_equiv (Equiv.addRight h₀) _ _ fun _ => rfl
  corr g hg := by
    rw [← hb.corr g hg]
    simp only [add_right_comm _ g h₀]
    exact Fintype.sum_equiv (Equiv.addRight h₀) _ (fun u => b u * b (u + g)) fun _ => rfl
  abs := by
    rw [Fintype.sum_equiv (Equiv.addRight h₀) (fun h => |b (h + h₀)|) (fun u => |b u|)
      fun _ => rfl]; exact hb.abs
  parity := by
    rw [Fintype.sum_equiv (Equiv.addRight h₀) (fun h => |b (h + h₀)|) (fun u => |b u|)
      fun _ => rfl]; exact hb.parity

variable [Indexed H]

/-- A vector meeting `DemandsQ`, `Σ b = s` and `|b 0|` largest, contradicts `noVector`. -/
theorem false_of_noVectorQ {s : ℤ}
    (hn : noVector (Indexed.size H) (Indexed.addIdx H) c Q t k s = true)
    (hb : DemandsQ c Q t k b) (hmax : ∀ h, |b h| ≤ |b 0|) (hs : ∑ h, b h = s) : False := by
  set n := Indexed.size H
  set e : H ≃ Fin n := Indexed.equiv
  have hpos : 0 < n := (e 0).pos
  have he0 : e.symm ⟨0, hpos⟩ = 0 := e.symm_apply_eq.2 (Fin.ext Indexed.equiv_zero.symm)
  set F : Fin n → ℤ := fun i => b (e.symm i)
  have hsum (f : ℤ → ℤ) : ((List.ofFn F).map f).sum = ∑ h, f (b h) := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact e.symm.sum_comp (fun h => f (b h))
  have hmem : ∀ y ∈ List.ofFn F, ∃ h, b h = y := by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨_, rfl⟩
  have hne : List.ofFn F ≠ [] := by
    intro h
    have := List.length_ofFn (f := F)
    rw [h] at this
    simp at this
    omega
  obtain ⟨x, w, hL⟩ := List.exists_cons_of_ne_nil hne
  have hx : x = b 0 := by
    have := getD_ofFn F hpos
    rw [hL] at this
    simpa [F, he0] using this
  have hw : ∀ y ∈ w, ∃ h, b h = y := fun y hy => hmem y (hL ▸ List.mem_cons_of_mem x hy)
  refine noVector_sound hn x w (by rw [← hL, List.length_ofFn]) (hx ▸ hb.bound 0)
    (fun y hy => ?_) (fun y hy => ?_) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hx ▸ hmax h
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hb.bound h
  · rw [← hL, ← hs]
    simpa using hsum id
  · rw [← hL, ← hb.sq]
    exact hsum fun y => y * y
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.abs
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.parity
  · rw [← hL, shiftsOK, allTo_iff]
    intro g hg
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · simp
    set gH := e.symm ⟨g, hg⟩
    have hgH : (e gH : ℕ) = g := by simp [gH]
    have hgH0 : gH ≠ 0 := by
      intro h0
      have := hgH
      rw [h0, Indexed.equiv_zero] at this
      omega
    simp only [Bool.or_eq_true, beq_iff_eq]
    right
    rw [← hb.corr gH hgH0, sumTo_eq, ← sum_equiv (G := H)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hgH, ← Indexed.equiv_add, getD_ofFn F (e u).isLt, getD_ofFn F (e (u + gH)).isLt]
    simp [F]

/-- `DemandsQ` and `(Σ b)² = s²` contradict `noVector` (negate, then translate the largest
entry to `0`). -/
theorem false_of_noVectorQ' {s : ℤ}
    (hn : noVector (Indexed.size H) (Indexed.addIdx H) c Q t k s = true)
    (hb : DemandsQ c Q t k b) (hsq : (∑ h, b h) * (∑ h, b h) = s * s) : False := by
  have key : ∀ b : H → ℤ, DemandsQ c Q t k b → ∑ h, b h = s → False := by
    intro b hb hbs
    obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => |b h|)
      Finset.univ_nonempty
    refine false_of_noVectorQ hn (hb.translate h₀) (fun h => ?_) ?_
    · simpa using hmax (h + h₀) (Finset.mem_univ _)
    · rw [← hbs]
      exact Fintype.sum_equiv (Equiv.addRight h₀) _ b fun _ => rfl
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key b hb h1
  · exact key _ hb.neg (by rw [Finset.sum_neg_distrib, h1, neg_neg])

end Demands

/-- The reduction `ZMod (r p) × K → ZMod r × K`. -/
def maQuot (K : Type) [AddCommGroup K] (r p : ℕ) : ZMod (r * p) × K →+ ZMod r × K :=
  ((ZMod.castHom (dvd_mul_right r p) (ZMod r)).toAddMonoidHom).prodMap (AddMonoidHom.id K)

/-- C33's step: on a C21 quotient with `b ≥ 1`, every coset sum along
`ZMod (r p) × K → ZMod r × K` is divisible by `p`. -/
theorem Ma.dvd_contract_quot {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K]
    [Fintype K] [DecidableEq K] {p r i e b c k : ℕ} {lam : ℤ} [hp : Fact p.Prime]
    [NeZero (r * p)] [NeZero r] {φ : G →+ ZMod (r * p) × K} (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * Fintype.card (ZMod (r * p) × K)) (hr : 0 < r) (hi : 0 < i)
    (hc : ∀ x : K, p ^ i • x = -x) (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam) (hb : 2 * b ≤ e)
    (hb1 : 0 < b) (hcert : CycloFacts p r) {D : G → SignType} (hD : IsSDS k lam D)
    (y : ZMod r × K) : (p : ℤ) ∣ contract ((maQuot K r p).comp φ) D y := by
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
  have hstep : ∀ h, (p : ℤ) ∣ Y (h + u) - Y h := by
    rintro ⟨x, kk⟩
    have := Ma.dvd_contract_sub hφ hcard hr hi hc hn hb hcert hD x kk
    exact (dvd_pow_self (p : ℤ) hb1.ne').trans (by simpa [hu] using this)
  have hiter : ∀ (m : ℕ) h, (p : ℤ) ∣ Y (h + m • u) - Y h := by
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
  obtain ⟨h, rfl⟩ := hψ y
  rw [contract_comp]
  have hfib := card_fibre_eq hψ hcardH (ψ h)
  rw [fibre] at hfib
  have hsplit : ∑ h' ∈ Finset.univ.filter (fun h' => ψ h' = ψ h), Y h' =
      ∑ h' ∈ Finset.univ.filter (fun h' => ψ h' = ψ h), (Y h' - Y h) + (p : ℤ) * Y h := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hfib, nsmul_eq_mul]
    ring
  rw [hsplit]
  refine dvd_add (Finset.dvd_sum fun h' hh' => ?_) (dvd_mul_right _ _)
  have hh' : ψ (h' - h) = 0 := by
    rw [map_sub, (Finset.mem_filter.1 hh').2, sub_self]
  obtain ⟨m, hm⟩ := hker _ hh'
  have : h' = h + m • u := by rw [← hm]; abel
  rw [this]
  exact hiter m h

/-- C34: for odd `p`, `Z = W / p` meets `DemandsQ c Q t k'` with `(Σ Z)² = s'²`, so a
`noVector` check with those demands on `ZMod r × K` leaves no SDS. -/
theorem IsSDS.false_of_maDivided {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K]
    [Fintype K] {p r i e b c k k' : ℕ} {lam Q t s' : ℤ} [Indexed (ZMod r × K)]
    [hp : Fact p.Prime] [NeZero (r * p)] [NeZero r] {φ : G →+ ZMod (r * p) × K}
    (hφ : Function.Surjective φ) (hcard : Fintype.card G = c * Fintype.card (ZMod (r * p) × K))
    (hr : 0 < r) (hi : 0 < i) (hc : ∀ x : K, p ^ i • x = -x) (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam)
    (hb : 2 * b ≤ e) (hb1 : 0 < b) (hcert : CycloFacts p r) (hp2 : p ≠ 2)
    (hQ : (p : ℤ) ^ 2 * Q = k + lam * ((p * c : ℕ) - 1)) (ht : (p : ℤ) * t = lam * c)
    (hs : ((p : ℤ) * s') * ((p : ℤ) * s') = k + lam * ((Fintype.card G : ℤ) - 1))
    (hk : k < p * (k' + 2)) (hkk : ((k : ℤ) - k') % 2 = 0)
    (hnv : noVector (Indexed.size (ZMod r × K)) (Indexed.addIdx (ZMod r × K)) c Q t k' s' = true)
    {D : G → SignType} (hD : IsSDS k lam D) : False := by
  classical
  set ψ := maQuot K r p with hψdef
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, b⟩
    obtain ⟨a', ha'⟩ := ZMod.ringHom_surjective (ZMod.castHom (dvd_mul_right r p) (ZMod r)) a
    exact ⟨(a', b), by simp [hψdef, maQuot, ha']⟩
  set χ := ψ.comp φ with hχdef
  have hχ : Function.Surjective χ := hψ.comp hφ
  have hcardp : Fintype.card G = p * c * Fintype.card (ZMod r × K) := by
    rw [hcard, Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hfib := card_fibre_eq hχ hcardp
  set W := contract χ D with hWdef
  have hdiv : ∀ y, (p : ℤ) ∣ W y := fun y =>
    Ma.dvd_contract_quot hφ hcard hr hi hc hn hb hb1 hcert hD y
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  set Z : ZMod r × K → ℤ := fun y => W y / p with hZdef
  have hWZ : ∀ y, W y = p * Z y := fun y => (Int.mul_ediv_cancel' (hdiv y)).symm
  have hpc1 : 1 ≤ p * c := by
    rcases Nat.eq_zero_or_pos (p * c) with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card G)
      rw [hcardp, h0, zero_mul] at this
      omega
    · exact h0
  have hsqW := hD.contract_sq χ
  rw [← hWdef, hfib 0, Nat.cast_sub hpc1, Nat.cast_one] at hsqW
  have hcorrW : ∀ g, g ≠ 0 → ∑ y, W y * W (y + g) = lam * ((p * c : ℕ) : ℤ) := fun g hg => by
    rw [hD.contract_autocorr χ g hg, hfib]
  have habsW : ∑ y, |W y| = p * ∑ y, |Z y| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hWZ y, abs_mul, abs_of_pos hp0]
  have hdem : DemandsQ c Q t k' Z := by
    refine ⟨fun y => ?_, ?_, fun g hg => ?_, ?_, ?_⟩
    · have h1 := abs_contract_le χ D y
      rw [hfib y, ← hWdef, hWZ y, abs_mul, abs_of_pos hp0] at h1
      push_cast at h1
      exact le_of_mul_le_mul_left h1 hp0
    · have h2 : (p : ℤ) ^ 2 * ∑ y, Z y * Z y = (p : ℤ) ^ 2 * Q := by
        rw [hQ, Finset.mul_sum, ← hsqW]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hWZ y]
        ring
      exact mul_left_cancel₀ (by positivity) h2
    · have h2 : (p : ℤ) ^ 2 * ∑ y, Z y * Z (y + g) = (p : ℤ) ^ 2 * t := by
        rw [Finset.mul_sum]
        have : ∑ y, (p : ℤ) ^ 2 * (Z y * Z (y + g)) = ∑ y, W y * W (y + g) :=
          Finset.sum_congr rfl fun y _ => by rw [hWZ y, hWZ (y + g)]; ring
        rw [this, hcorrW g hg]
        push_cast
        linear_combination -(p : ℤ) * ht
      exact mul_left_cancel₀ (by positivity) h2
    · have h1 := hD.sum_abs_contract_le χ
      have h2 := hD.sum_abs_contract_parity χ
      rw [← hWdef, habsW] at h1 h2
      obtain ⟨m, hm⟩ := (hp.out.eq_two_or_odd').resolve_left hp2
      set A := ∑ y, |Z y|
      have hpA : (p : ℤ) * A = 2 * (m * A) + A := by rw [hm]; push_cast; ring
      have hk' : (k : ℤ) < p * ((k' : ℤ) + 2) := by exact_mod_cast hk
      have hA0 : 0 ≤ A := Finset.sum_nonneg fun y _ => abs_nonneg _
      have hlt : A < (k' : ℤ) + 2 := by
        by_contra hge
        have : (p : ℤ) * ((k' : ℤ) + 2) ≤ p * A :=
          mul_le_mul_of_nonneg_left (not_lt.1 hge) hp0.le
        linarith
      omega
    · have h2 := hD.sum_abs_contract_parity χ
      rw [← hWdef, habsW] at h2
      obtain ⟨m, hm⟩ := (hp.out.eq_two_or_odd').resolve_left hp2
      set A := ∑ y, |Z y|
      have hpA : (p : ℤ) * A = 2 * (m * A) + A := by rw [hm]; push_cast; ring
      omega
  have hsqZ : (∑ y, Z y) * (∑ y, Z y) = s' * s' := by
    have hH1 : 1 ≤ Fintype.card (ZMod r × K) := Fintype.card_pos
    have hW2 : (∑ y, W y) * (∑ y, W y) = ((p : ℤ) * s') * ((p : ℤ) * s') := by
      rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
      simp only [add_zero]
      rw [hsqW, Finset.sum_congr rfl fun g hg => hcorrW g (Finset.ne_of_mem_erase hg),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hs,
        hcardp, nsmul_eq_mul, Nat.cast_sub hH1]
      push_cast
      ring
    have hsumW : ∑ y, W y = p * ∑ y, Z y := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => hWZ y
    rw [hsumW] at hW2
    have : (p : ℤ) ^ 2 * ((∑ y, Z y) * (∑ y, Z y)) = (p : ℤ) ^ 2 * (s' * s') := by
      linear_combination hW2
    exact mul_left_cancel₀ (by positivity) this
  exact false_of_noVectorQ' hnv hdem hsqZ

/-! ### Rows -/

/-- A C34 certificate: C21's fields (`p` odd, `r = p^(j−1)`, `i`, `e`, `b ≥ 1`, `ks ≠ []`, forms `A`
onto `ZMod (r p) × Grp ks` with preimages `P`) and the divided demands `k'`, `Q`, `t`, `s'`. -/
structure MaDivCert where
  p : ℕ
  r : ℕ
  i : ℕ
  e : ℕ
  b : ℕ
  ks : List ℕ
  A : List (List ℕ)
  P : List (List ℕ)
  k' : ℕ
  Q : ℤ
  t : ℤ
  s' : ℤ
  deriving DecidableEq

/-- C34's hypotheses on the row, `c = |G| / (r p |K|)`, `(p, r)` among `MaRows.maPairs`. -/
def MaDivCert.Valid (w : Row) (c : MaDivCert) : Prop :=
  IsPrimeTD c.p ∧ c.p ≠ 2 ∧ 0 < c.r ∧ 0 < c.i ∧ c.ks ≠ [] ∧ (∀ d ∈ c.ks, d ∣ c.p ^ c.i + 1) ∧
    MapOk w.ms (c.r * c.p :: c.ks) c.A ∧ SurjCert w.ms (c.r * c.p :: c.ks) c.A c.P ∧
    c.r * c.p * c.ks.prod ∣ w.ms.prod ∧ (c.p : ℤ) ^ c.e ∣ w.k - w.lam ∧ 2 * c.b ≤ c.e ∧
    0 < c.b ∧
    (c.p : ℤ) ^ 2 * c.Q =
      w.k + w.lam * ((c.p * (w.ms.prod / (c.r * c.p * c.ks.prod)) : ℕ) - 1) ∧
    (c.p : ℤ) * c.t = w.lam * (w.ms.prod / (c.r * c.p * c.ks.prod) : ℕ) ∧
    ((c.p : ℤ) * c.s') * ((c.p : ℤ) * c.s') = w.k + w.lam * ((w.ms.prod : ℤ) - 1) ∧
    w.k < c.p * (c.k' + 2) ∧ ((w.k : ℤ) - c.k') % 2 = 0 ∧ (c.p, c.r) ∈ MaRows.maPairs

instance MaDivCert.instDecidableValid (w : Row) (c : MaDivCert) : Decidable (c.Valid w) := by
  unfold MaDivCert.Valid; infer_instance

/-- A row meeting C34's hypotheses whose divided search on `Grp (r :: ks)` finds no vector has
no SDS, whatever `Fintype` instance its group carries. -/
theorem MaDivCert.not_hasSDS {w : Row} {c : MaDivCert} (h : c.Valid w)
    (hpos : ∀ m ∈ c.r :: c.ks, 0 < m) (inst : Fintype (Grp w.ms))
    (hn : noVector (@Indexed.size (Grp (c.r :: c.ks)) _ (Grp.indexed _ hpos))
      (@Indexed.addIdx (Grp (c.r :: c.ks)) _ (Grp.indexed _ hpos))
      ((w.ms.prod / (c.r * c.p * c.ks.prod) : ℕ) : ℤ) c.Q c.t c.k' c.s' = true) :
    ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨p, r, i, e, b, ks, A, P, k', Q, t, s'⟩ := c
  obtain ⟨hp, hp2, hr, hi, hne, hks, hmap, hsurj, hprod, hn', hbe, hb1, hQ, ht, hs, hk, hkk,
    hpair⟩ := h
  dsimp only at *
  rintro ⟨D, hD⟩
  obtain ⟨k₀, ks, rfl⟩ := List.exists_cons_of_ne_nil hne
  have : Fact p.Prime := ⟨hp.prime⟩
  have : NeZero (r * p) := ⟨(Nat.mul_pos hr hp.prime.pos).ne'⟩
  have : NeZero r := ⟨hr.ne'⟩
  let _ : Fintype (Grp (k₀ :: ks)) :=
    Grp.fintype _ fun d hd => Nat.pos_of_dvd_of_pos (hks d hd) (by positivity)
  let φ : Grp w.ms →+ ZMod (r * p) × Grp (k₀ :: ks) := linMap w.ms (r * p :: k₀ :: ks) A hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp w.ms) = w.ms.prod / (r * p * (k₀ :: ks).prod) *
      Fintype.card (ZMod (r * p) × Grp (k₀ :: ks)) := by
    rw [Fintype.card_prod, ZMod.card, Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hconj (x : Grp (k₀ :: ks)) : p ^ i • x = -x := by
    have := Grp.nsmul_eq_zero (N := p ^ i + 1) (k₀ :: ks) hks x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  let _ : Indexed (ZMod r × Grp (k₀ :: ks)) := Grp.indexed (r :: k₀ :: ks) hpos
  exact hD.false_of_maDivided hφ hcard hr hi hconj hn' hbe hb1
    (MaRows.cycloFacts_of_mem_maPairs hpair) hp2 hQ ht (by rw [Grp.card_eq]; exact hs) hk hkk hn

end SignedDifferenceSets
