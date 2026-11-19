module

public import SignedDifferenceSets.TomographyQuotSearch
public import SignedDifferenceSets.TomographyOrbit
public import SignedDifferenceSets.MultiplierWitt
public import SignedDifferenceSets.LinearMaps
public import SignedDifferenceSets.SelfConjugacyCheck

/-!
# Line tomography on a quotient `G → ZMod p × ZMod p` (I23)

Let `φ : G →+ ZMod p × ZMod p` be onto with fibres of `c` elements, `D` an SDS on `G`, `W` its coset
sums along `φ` (`|W| ≤ c`) and `Yⱼ` its coset sums along line `j` of `φ` (`lineQ`, fibres of
`c p`). Then `Σⱼ Yⱼ(lineⱼ g) = p W(g) + Σ D` (`sum_contract_linesQ`). A translate of `D` has
`Σₓ D(x) φ(x) = 0` when `p ∤ s` (`exists_centeredQ`); then every `Σₜ t Yⱼ(t)` vanishes, each
`Yⱼ` meets C3's demands with fibres `c p` (`demands_lineQ`), and with a multiplier `t` (C10':
`p ∤ k − λ ≠ 0`, `t ≡ q^f` for every prime `q ∣ k − λ`) it is fixed by `h ↦ t h`
(`fixed_lineQ`). `not_hasSDS_quot`: if every such vector lies in `W` and no choice of one per
line has every `lineSum − s` equal to `p z` with `|z| ≤ c`, there is no SDS. The lists come from
`inSearch` (`lists_of_inSearch`) or `orbSearch` (`lists_of_orbSearch`), the choice is ruled out
by one point (`closes_of_ptOK`) or by `tomoGoL` (`closes_of_tomoGoL`); `not_hasSDS_grp` states it
for the table's groups with `φ` given by forms (`linMap`).
-/

@[expose] public section

namespace SignedDifferenceSets.Tomography

section Quot

variable {G : Type*} [AddCommGroup G] [Fintype G] {p : ℕ} [hp : Fact p.Prime]

/-- Line `j` of the quotient `φ`. -/
def lineQ (p j : ℕ) (φ : G →+ ZMod p × ZMod p) : G →+ ZMod p := (lineMap p j).comp φ

/-- The lines' coset sums at `g` add up to `p W(g) + Σ D`. -/
theorem sum_contract_linesQ (φ : G →+ ZMod p × ZMod p) (D : G → SignType)
    (g : ZMod p × ZMod p) :
    ∑ j ∈ Finset.range (p + 1), contract (lineQ p j φ) D (lineMap p j g) =
      p * contract φ D g + ∑ x, (D x : ℤ) := by
  have h1 (j : ℕ) : contract (lineQ p j φ) D (lineMap p j g) =
      ∑ x, if lineMap p j (φ x - g) = 0 then (D x : ℤ) else 0 := by
    rw [contract, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [lineQ, AddMonoidHom.coe_comp, Function.comp_apply, map_sub, sub_eq_zero]
    exact if_congr Iff.rfl rfl rfl
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 (x : G) : ∑ j ∈ Finset.range (p + 1),
      (if lineMap p j (φ x - g) = 0 then (D x : ℤ) else 0) =
      (D x : ℤ) + if φ x = g then p * (D x : ℤ) else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hy : φ x = g
    · subst hy
      simp only [sub_self, map_zero, Finset.filter_true_of_mem (fun _ _ => trivial),
        Finset.card_range, ↓reduceIte]
      push_cast
      ring
    · simp only [card_lines_eq_one (sub_ne_zero.2 hy), hy, ↓reduceIte]
      simp
  simp only [h2, Finset.sum_add_distrib]
  rw [add_comm, contract, Finset.sum_filter, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- The coset sums along `ψ` add up to `Σ D`. -/
theorem sum_contractQ (ψ : G →+ ZMod p) (D : G → SignType) :
    ∑ h, contract ψ D h = ∑ x, (D x : ℤ) :=
  sum_fibre ψ _

/-- `Σₜ t Y(t)` of the coset sums along `ψ` is `Σₓ D(x) ψ(x)` in `ZMod p`. -/
theorem moment_contractQ (ψ : G →+ ZMod p) (D : G → SignType) :
    ∑ h, ((contract ψ D h : ℤ) : ZMod p) * h = ∑ x, ((D x : ℤ) : ZMod p) * ψ x := by
  simp only [contract, Int.cast_sum, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ ψ (fun x => ((D x : ℤ) : ZMod p) * ψ x)]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-- `Σₓ D(x) φ(x) = 0` in `ZMod p × ZMod p`. -/
def CenteredQ (φ : G →+ ZMod p × ZMod p) (D : G → SignType) : Prop :=
  ∑ x, ((D x : ℤ) : ZMod p) * (φ x).1 = 0 ∧ ∑ x, ((D x : ℤ) : ZMod p) * (φ x).2 = 0

theorem CenteredQ.moment_line {φ : G →+ ZMod p × ZMod p} {D : G → SignType}
    (hc : CenteredQ φ D) (j : ℕ) :
    ∑ h, ((contract (lineQ p j φ) D h : ℤ) : ZMod p) * h = 0 := by
  rw [moment_contractQ]
  cases j with
  | zero =>
    simpa only [lineQ, AddMonoidHom.coe_comp, Function.comp_apply, lineMap_zero] using hc.2
  | succ j =>
    have e : ∑ x, ((D x : ℤ) : ZMod p) * lineQ p (j + 1) φ x =
        ∑ x, ((D x : ℤ) : ZMod p) * (φ x).1 +
          (j : ZMod p) * ∑ x, ((D x : ℤ) : ZMod p) * (φ x).2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [lineQ, AddMonoidHom.coe_comp, Function.comp_apply, lineMap_succ]
      ring
    rw [e, hc.1, hc.2, mul_zero, add_zero]

/-- A translate of `D` is centred along `φ` when `p ∤ Σ D`. -/
theorem exists_centeredQ {φ : G →+ ZMod p × ZMod p} (hφ : Function.Surjective φ)
    (D : G → SignType) (hS : ∑ x, ((D x : ℤ) : ZMod p) ≠ 0) :
    ∃ t, CenteredQ φ fun x => D (x + t) := by
  set S := ∑ x, ((D x : ℤ) : ZMod p) with hSdef
  obtain ⟨t, ht⟩ := hφ ((∑ x, ((D x : ℤ) : ZMod p) * (φ x).1) / S,
    (∑ x, ((D x : ℤ) : ZMod p) * (φ x).2) / S)
  have e (f : ZMod p × ZMod p → ZMod p) : ∑ x, ((D (x + t) : ℤ) : ZMod p) * f (φ x) =
      ∑ y, ((D y : ℤ) : ZMod p) * f (φ y - φ t) :=
    Fintype.sum_equiv (Equiv.addRight t) _ _ fun x => by simp
  refine ⟨t, ?_, ?_⟩
  · change ∑ x, ((D (x + t) : ℤ) : ZMod p) * Prod.fst (φ x) = 0
    rw [e Prod.fst]
    simp only [Prod.fst_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hSdef, ht]
    rw [mul_comm, div_mul_cancel₀ _ hS, sub_self]
  · change ∑ x, ((D (x + t) : ℤ) : ZMod p) * Prod.snd (φ x) = 0
    rw [e Prod.snd]
    simp only [Prod.snd_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hSdef, ht]
    rw [mul_comm, div_mul_cancel₀ _ hS, sub_self]

omit [Fintype G] in
theorem lineQ_surjective {φ : G →+ ZMod p × ZMod p} (hφ : Function.Surjective φ) (j : ℕ) :
    Function.Surjective (lineQ p j φ) :=
  (lineMap_surjective p j).comp hφ

/-- The demands on the coset sums along a line of `φ` (C3, fibres of `c p`). -/
theorem demands_lineQ {φ : G →+ ZMod p × ZMod p} (hφ : Function.Surjective φ) {c k : ℕ}
    {lam : ℤ} (hcard : Fintype.card G = c * (p * p)) {D : G → SignType} (hD : IsSDS k lam D)
    (j : ℕ) : Demands (c * p) k lam (contract (lineQ p j φ) D) := by
  have hc : Fintype.card G = (c * p) * Fintype.card (ZMod p) := by rw [hcard, ZMod.card]; ring
  have hfib := card_fibre_eq (lineQ_surjective hφ j) hc
  have hcp : 1 ≤ c * p := by
    rcases Nat.eq_zero_or_pos (c * p) with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card G)
      rw [hc, h0, zero_mul] at this
      omega
    · exact h0
  exact
    { bound := fun h => by
        have := abs_contract_le (lineQ p j φ) D h
        rwa [hfib] at this
      sq := by rw [hD.contract_sq, hfib 0, Nat.cast_sub hcp, Nat.cast_one]
      corr := fun g hg => by rw [hD.contract_autocorr _ g hg, hfib]
      abs := hD.sum_abs_contract_le _
      parity := hD.sum_abs_contract_parity _ }

/-- C10' on a line of `φ`: the coset sums of a centred SDS are fixed by `h ↦ t h` when
`n = k − λ ≠ 0`, `p ∤ n`, `t ≢ 0, 1 (mod p)` and `t ≡ q^f` for every prime `q ∣ n`. -/
theorem fixed_lineQ {φ : G →+ ZMod p × ZMod p} (hφ : Function.Surjective φ) {c k : ℕ}
    {lam s : ℤ} (hcard : Fintype.card G = c * (p * p)) {D : G → SignType} (hD : IsSDS k lam D)
    (hsum : ∑ x, (D x : ℤ) = s) (hsp : (s : ZMod p) ≠ 0) (hcen : CenteredQ φ D) {n t : ℕ}
    (hk : (k : ℤ) - lam = n) (hn0 : n ≠ 0) (hpn : (n : ZMod p) ≠ 0) (ht0 : (t : ZMod p) ≠ 0)
    (ht1 : (t : ZMod p) ≠ 1)
    (hq : ∀ q : ℕ, q.Prime → q ∣ n → ∃ f : ℕ, (t : ZMod p) = (q : ZMod p) ^ f)
    (j : ℕ) (h : ZMod p) :
    contract (lineQ p j φ) D ((t : ZMod p) * h) = contract (lineQ p j φ) D h := by
  set Y := contract (lineQ p j φ) D with hY
  have hc : Fintype.card G = (c * p) * Fintype.card (ZMod p) := by rw [hcard, ZMod.card]; ring
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hd =>
    hpn ((ZMod.natCast_eq_zero_iff n p).2 hd)
  have htc : Nat.Coprime t p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hd =>
    ht0 ((ZMod.natCast_eq_zero_iff t p).2 hd)).symm
  obtain ⟨b, hb⟩ := hD.exists_translate_fixed_contract' (lineQ p j φ) (lineQ_surjective hφ j) hc
    (by rw [hk]; exact_mod_cast hn0)
    (by rw [ZMod.card, hk]; exact Nat.isCoprime_iff_coprime.2 hcop)
  have hfix : ∀ h, Y ((t : ZMod p) * h + b) = Y (h + b) := by
    intro h
    have := hb t (by rw [ZMod.card]; exact htc) (fun q hq' hqn => by
      rw [hk, Int.natCast_dvd_natCast] at hqn
      obtain ⟨f, hf⟩ := hq q hq' hqn
      exact ⟨f, fun x => by rw [nsmul_eq_mul, nsmul_eq_mul, hf, Nat.cast_pow]⟩) h
    rwa [nsmul_eq_mul] at this
  -- the translate's first moment `M` is fixed by `t`, so vanishes
  set M := ∑ h, ((Y (h + b) : ℤ) : ZMod p) * h with hM
  have hM0 : M = 0 := by
    have e1 : ∑ x, ((Y ((t : ZMod p) * x + b) : ℤ) : ZMod p) * ((t : ZMod p) * x) = M :=
      Fintype.sum_equiv (Equiv.mulLeft₀ (t : ZMod p) ht0) _
        (fun y => ((Y (y + b) : ℤ) : ZMod p) * y) fun _ => rfl
    simp only [hfix] at e1
    have e2 : (t : ZMod p) * M = M := by
      calc (t : ZMod p) * M = ∑ x, ((Y (x + b) : ℤ) : ZMod p) * ((t : ZMod p) * x) := by
            rw [hM, Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ = M := e1
    have : ((t : ZMod p) - 1) * M = 0 := by rw [sub_mul, e2, one_mul, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ht1)
  -- and `M = −b s`
  have hMb : M = -(b * (s : ZMod p)) := by
    have e1 : M = ∑ y, ((Y y : ℤ) : ZMod p) * (y - b) :=
      Fintype.sum_equiv (Equiv.addRight b) _ _ fun x => by simp
    have hs' : ∑ y, ((Y y : ℤ) : ZMod p) = s := by
      rw [← Int.cast_sum, hY, sum_contractQ, hsum]
    have hm' : ∑ h, ((Y h : ℤ) : ZMod p) * h = 0 := hcen.moment_line j
    rw [e1]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs', hm']
    ring
  have hb0 : b = 0 := by
    rw [hM0, eq_comm, neg_eq_zero] at hMb
    exact (mul_eq_zero.1 hMb).resolve_right hsp
  simpa [hb0] using hfix h

/-- Line tomography on a quotient (I23): no SDS on `G` when `φ : G → ZMod p × ZMod p` is onto
with fibres of `c`, `p ∤ s`, the centred line contractions are fixed by `h ↦ t h`, every vector
meeting their demands (fibres `c p`), fixed by `t`, with sum `s` and `Σ h b(h) = 0` is in `W`,
and no choice of one per line from `W` passes `leafQ`. -/
theorem not_hasSDS_quot (p : ℕ) [Fact p.Prime] {c k : ℕ} {lam s : ℤ}
    (φ : G →+ ZMod p × ZMod p) (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * (p * p)) (hs : s * s = k + lam * ((c : ℤ) * p * p - 1))
    (hsp : (s : ZMod p) ≠ 0) {t : ℕ}
    (hfix : ∀ D : G → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s → CenteredQ φ D →
      ∀ j h, contract (lineQ p j φ) D ((t : ZMod p) * h) = contract (lineQ p j φ) D h)
    {W : List (List ℤ)}
    (hW : ∀ b : ZMod p → ℤ, Demands (c * p) k lam b → ∑ h, b h = s →
      ∑ x, ((b x : ℤ) : ZMod p) * x = 0 → (∀ h, b ((t : ZMod p) * h) = b h) → vecOf p b ∈ W)
    (hC : ∀ ys : List (List ℤ), ys.length = p + 1 → (∀ y ∈ ys, y ∈ W) →
      leafQ p s c ys = true → False) :
    ¬ HasSDS G k lam := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have key : ∀ D : G → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s → CenteredQ φ D →
      False := by
    intro D hD hsum hcen
    set ys := (List.range (p + 1)).map fun j => vecOf p (contract (lineQ p j φ) D) with hys
    refine hC ys (by simp [ys]) (fun y hy => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
      exact hW _ (demands_lineQ hφ hcard hD j) (by rw [sum_contractQ, hsum])
        (hcen.moment_line j) (hfix D hD hsum hcen j)
    · rw [leafQ, allTo_iff]
      intro x _
      have e : lineSum p ys x = p * contract φ D (gOf p x) + s := by
        rw [lineSum, sumTo_eq, ← hsum, ← sum_contract_linesQ φ D (gOf p x)]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hys, getD_map_range' _ _ (Finset.mem_range.1 hj),
          vecOf_getD _ (lineIdx_lt hp0 j x), lineIdx_cast]
      have hb : |contract φ D (gOf p x)| ≤ c := by
        have := abs_contract_le φ D (gOf p x)
        rwa [card_fibre_eq hφ (by rw [hcard, Fintype.card_prod, ZMod.card])] at this
      rw [e, add_sub_cancel_right]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      refine ⟨Int.mul_emod_right _ _, ?_⟩
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p)]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
  have centre : ∀ D : G → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s → False := by
    intro D hD hsum
    have hS : ∑ x, ((D x : ℤ) : ZMod p) ≠ 0 := by
      rw [← Int.cast_sum, hsum]
      exact hsp
    obtain ⟨t₀, ht⟩ := exists_centeredQ hφ D hS
    refine key _ (hD.translate t₀) ?_ ht
    rw [← hsum]
    exact Fintype.sum_equiv (Equiv.addRight t₀) _ (fun x => (D x : ℤ)) fun _ => rfl
  rintro ⟨D, hD⟩
  have hdem := demands_lineQ hφ hcard hD 0
  set a := contract (lineQ p 0 φ) D
  have hsq : (∑ h, a h) * (∑ h, a h) = s * s := by
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hdem.sq, Finset.sum_congr rfl fun g hg => hdem.corr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card, hs, nsmul_eq_mul, Nat.cast_sub hp0]
    push_cast
    ring
  rw [sum_contractQ] at hsq
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact centre D hD h1
  · refine centre _ hD.neg ?_
    simp only [SignType.coe_neg, Finset.sum_neg_distrib, h1, neg_neg]

end Quot

/-! ### The lists and the closing checks -/

section Lists

variable {p : ℕ} [hp : Fact p.Prime]

/-- A vector meeting the demands passes `leafOK` (as in `mem_of_inSearch`). -/
theorem leafOK_vecOf {C k : ℕ} {lam s : ℤ} {b : ZMod p → ℤ} (hb : Demands C k lam b)
    (hs : ∑ h, b h = s) :
    leafOK (Indexed.size (ZMod p)) (Indexed.addIdx (ZMod p)) (k + lam * ((C : ℤ) - 1))
      (lam * C) k s (vecOf p b) (vecOf p b).sum (sqSum (vecOf p b)) (absSum (vecOf p b)) =
      true := by
  set e : ZMod p ≃ Fin (Indexed.size (ZMod p)) := Indexed.equiv
  set F : Fin (Indexed.size (ZMod p)) → ℤ := fun i => b (e.symm i)
  have hL : vecOf p b = List.ofFn F := rfl
  have hsum (f : ℤ → ℤ) : ((List.ofFn F).map f).sum = ∑ h, f (b h) := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact e.symm.sum_comp (fun h => f (b h))
  have h1 : (vecOf p b).sum = s := by rw [hL, ← hs]; simpa using hsum id
  have h2 : sqSum (vecOf p b) = k + lam * ((C : ℤ) - 1) := by
    rw [hL, ← hb.sq]; exact hsum fun y => y * y
  have h3 : absSum (vecOf p b) = ∑ h, |b h| := by rw [hL]; exact hsum fun y => |y|
  have h4 : shiftsOK (Indexed.size (ZMod p)) (Indexed.addIdx (ZMod p)) (lam * C) (vecOf p b) =
      true := by
    rw [hL, shiftsOK, allTo_iff]
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
    rw [← hb.corr gH hgH0, sumTo_eq, ← sum_equiv (G := ZMod p)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hgH, ← Indexed.equiv_add, getD_ofFn F (e u).isLt, getD_ofFn F (e (u + gH)).isLt]
    simp [F]
  simp [leafOK, h1, h2, h3, h4, hb.abs, hb.parity]

/-- `inSearch` and `rotOK` with fibres of `C` list every vector meeting the demands with sum `s`
and `Σ h b(h) = 0`. -/
theorem lists_of_inSearch {C k : ℕ} {lam s : ℤ} {V0 W : List (List ℤ)}
    (hV : inSearch (Indexed.size (ZMod p)) (Indexed.addIdx (ZMod p)) C
      (k + lam * ((C : ℤ) - 1)) (lam * C) k s V0 = true)
    (hW : rotOK p V0 W = true) (t : ℕ) (b : ZMod p → ℤ) (hb : Demands C k lam b)
    (hs : ∑ h, b h = s) (hm : ∑ x, ((b x : ℤ) : ZMod p) * x = 0)
    (_ : ∀ h, b ((t : ZMod p) * h) = b h) : vecOf p b ∈ W := by
  obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => |b h|)
    Finset.univ_nonempty
  have hv0 : vecOf p (fun h => b (h + h₀)) ∈ V0 :=
    mem_of_inSearch (H := ZMod p) hV (hb.translate h₀)
      (fun h => by simpa using hmax (h + h₀) (Finset.mem_univ _))
      (by rw [← hs]; exact Fintype.sum_equiv (Equiv.addRight h₀) _ b fun _ => rfl)
  have hr := (allTo_iff _ _).1 (List.all_eq_true.1 hW _ hv0) (-h₀).val (ZMod.val_lt _)
  rw [rot_vecOf, m1ok_vecOf b hm, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hr
  exact hr

/-- `orbSearch` with orbit data for `h ↦ t h` lists every vector meeting the demands (fibres of
`C`) with sum `s` and `Σ h b(h) = 0` that is fixed by `t`. -/
theorem lists_of_orbSearch {C k : ℕ} {lam s : ℤ} {t : ℕ} {orb sz rep ex : List ℕ}
    {W : List (List ℤ)}
    (hV : orbSearch (Indexed.size (ZMod p)) (Indexed.addIdx (ZMod p)) C
      (k + lam * ((C : ℤ) - 1)) (lam * C) k s orb sz W = true)
    (ho : orbOK p t orb sz rep ex = true) (b : ZMod p → ℤ) (hb : Demands C k lam b)
    (hs : ∑ h, b h = s) (hm : ∑ x, ((b x : ℤ) : ZMod p) * x = 0)
    (hfix : ∀ h, b ((t : ZMod p) * h) = b h) : vecOf p b ∈ W := by
  have hn : Indexed.size (ZMod p) = p := rfl
  simp only [orbOK, Bool.and_eq_true, allTo_iff, decide_eq_true_eq, beq_iff_eq] at ho
  obtain ⟨horb, hsz⟩ := ho
  set us : List ℤ := (List.range sz.length).map fun i => b ((rep.getD i 0 : ℕ) : ZMod p)
    with hus
  have hlen : us.length = sz.length := by simp [us]
  have hbh : ∀ h < p, b (h : ZMod p) = us.getD (orb.getD h 0) 0 := by
    intro h hh
    obtain ⟨hi, he⟩ := horb h hh
    rw [hus, getD_map_range' _ _ hi]
    have e : ((h : ℕ) : ZMod p) =
        (t : ZMod p) ^ ex.getD h 0 * ((rep.getD (orb.getD h 0) 0 : ℕ) : ZMod p) := by
      have := congrArg (Nat.cast : ℕ → ZMod p) he
      rw [ZMod.natCast_mod] at this
      push_cast at this
      exact this.symm
    rw [e, fixed_pow hfix]
  have hvec : vecOf p b = expand (Indexed.size (ZMod p)) orb us := by
    refine List.ext_getElem (by simp [vecOf, expand, hn]) fun i h1 _ => ?_
    have hi : i < p := by simpa [vecOf] using h1
    simp only [vecOf, expand, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact hbh i hi
  have hsumf (f : ℤ → ℤ) : wsum sz (us.map f) = ∑ x, f (b x) := by
    rw [wsum_eq_sum f sz us hlen,
      sum_sizes f us (fun h hh => (horb h hh).1) (fun i hi => (hsz i hi).2),
      Finset.sum_congr rfl fun h hh => congrArg f (hbh h (Finset.mem_range.1 hh)).symm]
    have e := sum_equiv (G := ZMod p) fun i : ℕ => f (b (i : ZMod p))
    change _ = ∑ i ∈ Finset.range p, _ at e
    rw [← e]
    exact Finset.sum_congr rfl fun x _ => by
      rw [show (((Indexed.equiv x : Fin (Indexed.size (ZMod p))) : ℕ) : ZMod p) = x from
        ZMod.natCast_zmod_val x]
  have hs' : wsum sz us = s := by
    have := hsumf id
    rw [List.map_id] at this
    rw [this, ← hs]
    rfl
  have hq' : wsq sz us = k + lam * ((C : ℤ) - 1) := by
    rw [wsq_eq_wsum, hsumf fun u => u * u]
    exact hb.sq
  have hbd : ∀ u ∈ us, |u| ≤ (C : ℤ) := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hu
    exact hb.bound _
  have hpos : ∀ z ∈ sz, 0 < z := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    have := (hsz i hi).1
    rwa [List.getD_eq_getElem _ _ hi] at this
  have hne : sz ≠ [] := by
    intro h0
    have := (horb 0 hp.out.pos).1
    simp [h0] at this
  have hleaf := orbGo_sound sz us [] 0 0 hV hlen hne hpos hbd (by rw [zero_add]; exact hs')
    (by rw [zero_add]; exact hq')
  rw [List.reverse_nil, List.nil_append, ← hvec] at hleaf
  have hm1 : m1ok (Indexed.size (ZMod p)) (vecOf p b) = true := m1ok_vecOf b hm
  simp only [orbLeaf, leafOK_vecOf hb hs, hm1, Bool.not_true, Bool.false_or,
    List.contains_iff_mem] at hleaf
  exact hleaf

omit hp in
/-- `ptOK` at a point rules out every choice that passes `leafQ`. -/
theorem closes_of_ptOK (hp0 : 0 < p) {s : ℤ} {c : ℕ} {W : List (List ℤ)} {g : ℕ}
    (hg : g < p * p) (h : ptOK p s W g = true) (ys : List (List ℤ)) (hlen : ys.length = p + 1)
    (hW : ∀ y ∈ ys, y ∈ W) (hleaf : leafQ p s c ys = true) : False := by
  have := (allTo_iff _ _).1 hleaf g hg
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ptOK_sound hp0 h ys hlen hW this.1

omit hp in
/-- A passing `tomoGoL` with the leaf `leafQ` rules out every choice that passes `leafQ`. -/
theorem closes_of_tomoGoL (hp0 : 0 < p) {s : ℤ} {c : ℕ} {W : List (List ℤ)}
    {ws : List (List (List ℤ))} {R : List (List Tomography.Row)} (hc : certOK p ws = true)
    (hR : certRows p s ws = R) (h : tomoGoL p (leafQ p s c) W R [] = true)
    (ys : List (List ℤ)) (hlen : ys.length = p + 1) (hW : ∀ y ∈ ys, y ∈ W)
    (hleaf : leafQ p s c ys = true) : False :=
  no_choiceL hp0 hc hR h ys hlen hW (fun x hx => by
    have := (allTo_iff _ _).1 hleaf x hx
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1) hleaf

end Lists

/-! ### The table's groups -/

/-- Multiplier data (C10'): `n = k − λ ≠ 0` with `p ∤ n`, `t ≢ 0, 1 (mod p)`, and `n` the
product of the `q ^ e` over `fs = [(q, e, f), …]`, each `q` prime with `t ≡ q ^ f (mod p)`. -/
def MultOK (p t n : ℕ) (fs : List (ℕ × ℕ × ℕ)) : Prop :=
  n ≠ 0 ∧ n % p ≠ 0 ∧ t % p ≠ 0 ∧ t % p ≠ 1 ∧ n = (fs.map fun f => f.1 ^ f.2.1).prod ∧
    ∀ f ∈ fs, IsPrimeTD f.1 ∧ t % p = f.1 ^ f.2.2 % p

instance (p t n : ℕ) (fs : List (ℕ × ℕ × ℕ)) : Decidable (MultOK p t n fs) := by
  unfold MultOK; infer_instance

theorem MultOK.prime_dvd {p t n : ℕ} {fs : List (ℕ × ℕ × ℕ)} (h : MultOK p t n fs) {q : ℕ}
    (hq : q.Prime) (hqn : q ∣ n) : ∃ f : ℕ, (t : ZMod p) = (q : ZMod p) ^ f := by
  obtain ⟨-, -, -, -, hprod, hfs⟩ := h
  rw [hprod] at hqn
  obtain ⟨a, ha, hqa⟩ := (Prime.dvd_prod_iff hq.prime).1 hqn
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ha
  have hf' := hfs f hf
  have hqf : q = f.1 := (Nat.prime_dvd_prime_iff_eq hq hf'.1.prime).1 (hq.dvd_of_dvd_pow hqa)
  refine ⟨f.2.2, ?_⟩
  rw [hqf, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff']
  exact hf'.2

/-- `not_hasSDS_quot` on the table's group `Grp ms`, with `φ` given by the forms `A` (onto by the
preimages `P`) and the multiplier `t = 1` or C10' data. -/
theorem not_hasSDS_grp {ms : List ℕ} (p : ℕ) [hp : Fact p.Prime] {A P : List (List ℕ)}
    (hmap : MapOk ms [p, p] A) (hsurj : SurjCert ms [p, p] A P) (inst : Fintype (Grp ms))
    {c k : ℕ} {lam s : ℤ} (hcard : ms.prod = c * (p * p))
    (hs : s * s = k + lam * ((c : ℤ) * p * p - 1)) (hsp : (s : ZMod p) ≠ 0) {t : ℕ}
    (hmult : t = 1 ∨ ∃ (n : ℕ) (fs : List (ℕ × ℕ × ℕ)), (k : ℤ) - lam = n ∧ MultOK p t n fs)
    {W : List (List ℤ)}
    (hW : ∀ b : ZMod p → ℤ, Demands (c * p) k lam b → ∑ h, b h = s →
      ∑ x, ((b x : ℤ) : ZMod p) * x = 0 → (∀ h, b ((t : ZMod p) * h) = b h) → vecOf p b ∈ W)
    (hC : ∀ ys : List (List ℤ), ys.length = p + 1 → (∀ y ∈ ys, y ∈ W) →
      leafQ p s c ys = true → False) :
    ¬ @HasSDS (Grp ms) _ inst k lam := by
  let φ : Grp ms →+ ZMod p × ZMod p := linMap ms [p, p] A hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcardG : Fintype.card (Grp ms) = c * (p * p) := by rw [Grp.card_eq, hcard]
  refine not_hasSDS_quot p φ hφ hcardG hs hsp (t := t) ?_ hW hC
  intro D hD hsum hcen j h
  rcases hmult with rfl | ⟨n, fs, hk, hm⟩
  · simp
  · have hne (a : ℕ) (ha : a % p ≠ 0) : (a : ZMod p) ≠ 0 := fun h0 =>
      ha (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff a p).1 h0))
    have ht1 : (t : ZMod p) ≠ 1 := fun h1 => by
      have := (ZMod.natCast_eq_natCast_iff' t 1 p).1 (by rw [h1, Nat.cast_one])
      rw [Nat.mod_eq_of_lt hp.out.one_lt] at this
      exact hm.2.2.2.1 this
    exact fixed_lineQ hφ hcardG hD hsum hsp hcen hk hm.1 (hne n hm.2.1) (hne t hm.2.2.1) ht1
      (fun q hq hqn => hm.prime_dvd hq hqn) j h

end SignedDifferenceSets.Tomography
