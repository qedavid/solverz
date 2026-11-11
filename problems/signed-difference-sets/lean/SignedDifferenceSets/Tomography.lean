module

public import SignedDifferenceSets.TomographySearch
public import SignedDifferenceSets.ContractionCheck
public import SignedDifferenceSets.Symmetry

/-!
# Line tomography on `ZMod p × ZMod p` (I23)

The `p + 1` lines through `0` of `G = ZMod p × ZMod p` are the kernels of `lineMap p j`, `j ≤ p`,
and every `z ≠ 0` lies on exactly one (`card_lines_eq_one`). So the coset sums `Yⱼ` of `D` along
the lines satisfy `Σⱼ Yⱼ(lineⱼ g) = p D(g) + Σ D` (`sum_contract_lines`). An SDS with `Σ D = s`,
`p ∤ s`, translated so that `Σₓ D(x) x = 0` (C2, `exists_centered`), has line contractions that
meet C3's demands, sum to `s` and have `Σₜ t Yⱼ(t) = 0` in `ZMod p`, so each lies in the list
`W` (`mem_W`: `inSearch` lists the vectors `V0` with `|w₀|` largest, `rotOK` puts their
rotations with `Σ t w(t) ≡ 0` in `W`). `not_hasSDS`: if moreover `tomoGo` finds no choice from
`W` passing the certificate rows and the leaf (`Σⱼ Yⱼ(lineⱼ g) − s ∈ {0, ±p}`), there is none.
-/

@[expose] public section

namespace SignedDifferenceSets.Tomography

/-! ### The lines -/

/-- Line `j ≤ p` as a map onto `ZMod p`: `(a, b) ↦ b` for `j = 0`, `a + (j − 1) b` otherwise. -/
def lineMap (p : ℕ) : ℕ → (ZMod p × ZMod p →+ ZMod p)
  | 0 => AddMonoidHom.snd _ _
  | j + 1 => AddMonoidHom.fst _ _ + (AddMonoidHom.mulLeft (j : ZMod p)).comp (AddMonoidHom.snd _ _)

theorem lineMap_zero (p : ℕ) (g : ZMod p × ZMod p) : lineMap p 0 g = g.2 := rfl

theorem lineMap_succ (p j : ℕ) (g : ZMod p × ZMod p) : lineMap p (j + 1) g = g.1 + j * g.2 :=
  rfl

theorem lineMap_surjective (p j : ℕ) : Function.Surjective (lineMap p j) := by
  cases j with
  | zero => exact fun y => ⟨(0, y), rfl⟩
  | succ j => exact fun y => ⟨(y, 0), by simp [lineMap_succ]⟩

/-- The element with number `x = a p + b`. -/
def gOf (p x : ℕ) : ZMod p × ZMod p := (((x / p : ℕ) : ZMod p), ((x % p : ℕ) : ZMod p))

theorem lineIdx_cast (p j x : ℕ) : ((lineIdx p j x : ℕ) : ZMod p) = lineMap p j (gOf p x) := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [lineIdx, ZMod.natCast_mod, lineMap_succ, gOf]
    push_cast
    rfl

variable {p : ℕ} [hp : Fact p.Prime]

/-- Every `z ≠ 0` lies on exactly one line. -/
theorem card_lines_eq_one {z : ZMod p × ZMod p} (hz : z ≠ 0) :
    ((Finset.range (p + 1)).filter fun j => lineMap p j z = 0).card = 1 := by
  obtain ⟨a, b⟩ := z
  rw [Finset.card_eq_one]
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := fun ha => hz (by simp [ha])
    refine ⟨0, Finset.ext fun j => ?_⟩
    cases j with
    | zero => simp [lineMap_zero]
    | succ j => simp [lineMap_succ, ha]
  · refine ⟨(-a / b).val + 1, Finset.ext fun j => ?_⟩
    cases j with
    | zero => simp [lineMap_zero, hb]
    | succ j =>
      simp only [Finset.mem_filter, Finset.mem_range, lineMap_succ, Finset.mem_singleton]
      constructor
      · rintro ⟨hj, h⟩
        have hj' : (j : ZMod p) = -a / b := by
          rw [eq_div_iff hb]
          linear_combination h
        rw [← hj', ZMod.val_cast_of_lt (by omega)]
      · intro h
        have hj : j = (-a / b).val := by omega
        refine ⟨by have := ZMod.val_lt (-a / b); omega, ?_⟩
        rw [hj, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hb, add_neg_cancel]

/-- The lines' coset sums at `g` add up to `p D(g) + Σ D`. -/
theorem sum_contract_lines (D : ZMod p × ZMod p → SignType) (g : ZMod p × ZMod p) :
    ∑ j ∈ Finset.range (p + 1), contract (lineMap p j) D (lineMap p j g) =
      p * (D g : ℤ) + ∑ y, (D y : ℤ) := by
  have h1 (j : ℕ) : contract (lineMap p j) D (lineMap p j g) =
      ∑ y, if lineMap p j (y - g) = 0 then (D y : ℤ) else 0 := by
    rw [contract, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [map_sub, sub_eq_zero]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 (y : ZMod p × ZMod p) : ∑ j ∈ Finset.range (p + 1),
      (if lineMap p j (y - g) = 0 then (D y : ℤ) else 0) =
      (D y : ℤ) + if y = g then p * (D y : ℤ) else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hy : y = g
    · subst hy
      simp only [sub_self, map_zero, Finset.filter_true_of_mem (fun _ _ => trivial),
        Finset.card_range, ↓reduceIte]
      push_cast
      ring
    · simp only [card_lines_eq_one (sub_ne_zero.2 hy), hy, ↓reduceIte]
      simp
  simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- The coset sums along `φ` add up to `Σ D`. -/
theorem sum_contract (φ : ZMod p × ZMod p →+ ZMod p) (D : ZMod p × ZMod p → SignType) :
    ∑ h, contract φ D h = ∑ x, (D x : ℤ) :=
  sum_fibre φ _

/-- `Σₜ t Y(t)` of the coset sums along `φ` is `Σₓ D(x) φ(x)` in `ZMod p`. -/
theorem moment_contract (φ : ZMod p × ZMod p →+ ZMod p) (D : ZMod p × ZMod p → SignType) :
    ∑ h, ((contract φ D h : ℤ) : ZMod p) * h = ∑ x, ((D x : ℤ) : ZMod p) * φ x := by
  simp only [contract, Int.cast_sum, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ φ (fun x => ((D x : ℤ) : ZMod p) * φ x)]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-! ### Centring (C2) -/

/-- `Σₓ D(x) x = 0` in `ZMod p × ZMod p`. -/
def Centered (D : ZMod p × ZMod p → SignType) : Prop :=
  ∑ x, ((D x : ℤ) : ZMod p) * x.1 = 0 ∧ ∑ x, ((D x : ℤ) : ZMod p) * x.2 = 0

theorem Centered.moment_line {D : ZMod p × ZMod p → SignType} (h : Centered D) (j : ℕ) :
    ∑ h, ((contract (lineMap p j) D h : ℤ) : ZMod p) * h = 0 := by
  rw [moment_contract]
  cases j with
  | zero => simpa only [lineMap_zero] using h.2
  | succ j =>
    have e : ∑ x, ((D x : ℤ) : ZMod p) * lineMap p (j + 1) x =
        ∑ x, ((D x : ℤ) : ZMod p) * x.1 + (j : ZMod p) * ∑ x, ((D x : ℤ) : ZMod p) * x.2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by rw [lineMap_succ]; ring
    rw [e, h.1, h.2, mul_zero, add_zero]

theorem sum_translate (D : ZMod p × ZMod p → SignType) (t : ZMod p × ZMod p)
    (c : ZMod p × ZMod p → ZMod p) :
    ∑ x, ((D (x + t) : ℤ) : ZMod p) * c x = ∑ y, ((D y : ℤ) : ZMod p) * c (y - t) :=
  Fintype.sum_equiv (Equiv.addRight t) _ _ fun x => by simp

/-- A translate of `D` is centred when `p ∤ Σ D`. -/
theorem exists_centered (D : ZMod p × ZMod p → SignType)
    (hS : ∑ x, ((D x : ℤ) : ZMod p) ≠ 0) : ∃ t, Centered fun x => D (x + t) := by
  set S := ∑ x, ((D x : ℤ) : ZMod p) with hSdef
  refine ⟨((∑ x, ((D x : ℤ) : ZMod p) * x.1) / S, (∑ x, ((D x : ℤ) : ZMod p) * x.2) / S),
    ?_, ?_⟩
  · rw [sum_translate]
    simp only [Prod.fst_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hSdef]
    rw [mul_comm, div_mul_cancel₀ _ hS, sub_self]
  · rw [sum_translate]
    simp only [Prod.snd_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hSdef]
    rw [mul_comm, div_mul_cancel₀ _ hS, sub_self]

/-! ### The listed vectors -/

section List

variable {H : Type*} [AddCommGroup H] [Fintype H] [Indexed H]

/-- `inSearch` lists every vector meeting the demands, `Σ b = s` and `|b 0|` largest. -/
theorem mem_of_inSearch {c k : ℕ} {lam s : ℤ} {V : List (List ℤ)}
    (hn : inSearch (Indexed.size H) (Indexed.addIdx H) c (k + lam * ((c : ℤ) - 1)) (lam * c) k s
      V = true)
    {b : H → ℤ} (hb : Demands c k lam b) (hmax : ∀ h, |b h| ≤ |b 0|) (hs : ∑ h, b h = s) :
    List.ofFn (fun i => b (Indexed.equiv.symm i)) ∈ V := by
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
  change List.ofFn F ∈ V
  rw [hL]
  refine inSearch_sound hn x w (by rw [← hL, List.length_ofFn]) (hx ▸ hb.bound 0)
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

omit hp in
theorem inPart_add' {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {V : List (List ℤ)} {lo lo₂ : ℤ}
    {m₁ m₂ : ℕ} (h₁ : inPart n add c Q t k s V lo m₁ = true)
    (h₂ : inPart n add c Q t k s V lo₂ m₂ = true) (hlo : lo₂ = lo + m₁) :
    inPart n add c Q t k s V lo (m₁ + m₂) = true :=
  inPart_add h₁ (hlo ▸ h₂)

omit hp in
theorem inSearch_of_inPart {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {V : List (List ℤ)}
    {lo : ℤ} {m : ℕ} (h : inPart n add c Q t k s V lo m = true) (hlo : lo = -c)
    (hm : m = (2 * c + 1).toNat) : inSearch n add c Q t k s V = true := by
  subst hlo hm
  simp [inSearch, h]

end List

/-- The vector of `b` on `ZMod p` by element numbers. -/
def vecOf (p : ℕ) (b : ZMod p → ℤ) : List ℤ := List.ofFn fun i : Fin p => b (i : ℕ)

/-- `v` rotated: entry `i` is `v[(i + r) % p]`. -/
def rot (p r : ℕ) (v : List ℤ) : List ℤ := List.ofFn fun i : Fin p => v.getD ((i + r) % p) 0

/-- `Σᵢ i vᵢ ≡ 0 (mod p)`. -/
def m1ok (p : ℕ) (v : List ℤ) : Bool := sumTo (fun i => v.getD i 0 * i) p % p == 0

/-- Every rotation of a vector of `V0` with `m1ok` is in `W`. -/
def rotOK (p : ℕ) (V0 W : List (List ℤ)) : Bool :=
  V0.all fun v => allTo (fun r => !m1ok p (rot p r v) || W.contains (rot p r v)) p

theorem getD_map_range' {α : Type*} (f : ℕ → α) (d : α) {n t : ℕ} (ht : t < n) :
    ((List.range n).map f).getD t d = f t := by
  simp [List.getD_eq_getElem?_getD, ht]

theorem vecOf_getD (b : ZMod p → ℤ) {i : ℕ} (hi : i < p) : (vecOf p b).getD i 0 = b i := by
  rw [vecOf, getD_ofFn _ hi]

theorem rot_vecOf (b : ZMod p → ℤ) (h₀ : ZMod p) :
    rot p (-h₀).val (vecOf p fun h => b (h + h₀)) = vecOf p b := by
  unfold rot
  conv_rhs => rw [vecOf]
  congr 1
  funext i
  rw [vecOf_getD _ (Nat.mod_lt _ hp.out.pos), ZMod.natCast_mod, Nat.cast_add,
    ZMod.natCast_zmod_val, neg_add_cancel_right]

theorem m1ok_vecOf (b : ZMod p → ℤ) (h : ∑ x, ((b x : ℤ) : ZMod p) * x = 0) :
    m1ok p (vecOf p b) = true := by
  simp only [m1ok, beq_iff_eq]
  apply Int.emod_eq_zero_of_dvd
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, sumTo_eq]
  have e := sum_equiv (G := ZMod p) fun i : ℕ => (vecOf p b).getD i 0 * (i : ℤ)
  change _ = ∑ i ∈ Finset.range p, _ at e
  rw [← e, Int.cast_sum, ← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  change (((vecOf p b).getD x.val 0 * (x.val : ℤ) : ℤ) : ZMod p) = _
  rw [vecOf_getD _ (ZMod.val_lt x), Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Every vector meeting the demands with `Σ b = s` and `Σ t b(t) = 0` is in `W`. -/
theorem mem_W {k : ℕ} {lam s : ℤ} {V0 W : List (List ℤ)}
    (hV : inSearch (Indexed.size (ZMod p)) (Indexed.addIdx (ZMod p)) p
      (k + lam * ((p : ℤ) - 1)) (lam * p) k s V0 = true)
    (hW : rotOK p V0 W = true) {b : ZMod p → ℤ} (hb : Demands p k lam b) (hs : ∑ h, b h = s)
    (hm : ∑ x, ((b x : ℤ) : ZMod p) * x = 0) : vecOf p b ∈ W := by
  obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => |b h|)
    Finset.univ_nonempty
  have hv0 : vecOf p (fun h => b (h + h₀)) ∈ V0 :=
    mem_of_inSearch (H := ZMod p) hV (hb.translate h₀)
      (fun h => by simpa using hmax (h + h₀) (Finset.mem_univ _))
      (by rw [← hs]; exact Fintype.sum_equiv (Equiv.addRight h₀) _ b fun _ => rfl)
  have hr := (allTo_iff _ _).1 (List.all_eq_true.1 hW _ hv0) (-h₀).val (ZMod.val_lt _)
  rw [rot_vecOf, m1ok_vecOf b hm, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hr
  exact hr

/-! ### No SDS -/

/-- The demands on the coset sums along a line (C3, fibres of `p` elements). -/
theorem demands_line {k : ℕ} {lam : ℤ} {D : ZMod p × ZMod p → SignType} (hD : IsSDS k lam D)
    (j : ℕ) : Demands p k lam (contract (lineMap p j) D) := by
  have hc : Fintype.card (ZMod p × ZMod p) = p * Fintype.card (ZMod p) := by
    simp [Fintype.card_prod, ZMod.card]
  have hfib := card_fibre_eq (lineMap_surjective p j) hc
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  exact
    { bound := fun h => by
        have := abs_contract_le (lineMap p j) D h
        rwa [hfib] at this
      sq := by rw [hD.contract_sq, hfib 0, Nat.cast_sub hp1, Nat.cast_one]
      corr := fun g hg => by rw [hD.contract_autocorr _ g hg, hfib]
      abs := hD.sum_abs_contract_le _
      parity := hD.sum_abs_contract_parity _ }

/-- Line tomography (I23), the core: no SDS `(p², k, λ)` on `ZMod p × ZMod p` when `p ∤ s`, the
line contractions of every centred SDS with `Σ D = s` lie in `W`, and `tomoGo` with the
certificate `ws` finds no choice from `W`. -/
theorem not_hasSDS_of_mem (p : ℕ) [Fact p.Prime] {k : ℕ} {lam s : ℤ}
    (hs : s * s = k + lam * ((p : ℤ) * p - 1)) (hsp : (s : ZMod p) ≠ 0)
    {W : List (List ℤ)} {ws : List (List (List ℤ))} {R : List (List Row)}
    (hmem : ∀ D : ZMod p × ZMod p → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s →
      Centered D → ∀ j, vecOf p (contract (lineMap p j) D) ∈ W)
    (hc : certOK p ws = true) (hR : certRows p s ws = R) (h : tomoGo p s W R [] = true) :
    ¬ HasSDS (ZMod p × ZMod p) k lam := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have key : ∀ D : ZMod p × ZMod p → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s →
      Centered D → False := by
    intro D hD hsum hcen
    set ys := (List.range (p + 1)).map fun j => vecOf p (contract (lineMap p j) D) with hys
    refine no_choice hp0 hc hR h ys (by simp [ys]) (fun y hy => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
      exact hmem D hD hsum hcen j
    · rw [leafSDS, allTo_iff]
      intro x _
      have e : lineSum p ys x = p * (D (gOf p x) : ℤ) + s := by
        rw [lineSum, sumTo_eq, ← hsum, ← sum_contract_lines D (gOf p x)]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hys, getD_map_range' _ _ (Finset.mem_range.1 hj),
          vecOf_getD _ (lineIdx_lt hp0 j x), lineIdx_cast]
      rw [e, add_sub_cancel_right]
      unfold unitStep
      rcases D (gOf p x) with _ | _ | _ <;> simp
  have centre : ∀ D : ZMod p × ZMod p → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s →
      False := by
    intro D hD hsum
    have hS : ∑ x, ((D x : ℤ) : ZMod p) ≠ 0 := by
      rw [← Int.cast_sum, hsum]
      exact hsp
    obtain ⟨t, ht⟩ := exists_centered D hS
    refine key _ (hD.translate t) ?_ ht
    rw [← hsum]
    exact Fintype.sum_equiv (Equiv.addRight t) _ (fun x => (D x : ℤ)) fun _ => rfl
  rintro ⟨D, hD⟩
  have hdem := demands_line hD 0
  set a := contract (lineMap p 0) D
  have hsq : (∑ h, a h) * (∑ h, a h) = s * s := by
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hdem.sq, Finset.sum_congr rfl fun g hg => hdem.corr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card, hs, nsmul_eq_mul, Nat.cast_sub hp0]
    push_cast
    ring
  rw [sum_contract] at hsq
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact centre D hD h1
  · refine centre _ hD.neg ?_
    simp only [SignType.coe_neg, Finset.sum_neg_distrib, h1, neg_neg]

/-- Line tomography (I23): no SDS `(p², k, λ)` on `ZMod p × ZMod p` when `p ∤ s`, `inSearch`
lists in `V0` the vectors meeting a line contraction's demands (`|w₀|` largest), `rotOK` puts
their rotations with `Σ t w(t) ≡ 0` in `W`, and `tomoGo` with the certificate `ws` finds no
choice from `W`. -/
theorem not_hasSDS (p : ℕ) [Fact p.Prime] {k : ℕ} {lam s : ℤ}
    (hs : s * s = k + lam * ((p : ℤ) * p - 1)) (hsp : (s : ZMod p) ≠ 0)
    {V0 W : List (List ℤ)} {ws : List (List (List ℤ))} {R : List (List Row)}
    (hV : inSearch (Indexed.size (ZMod p)) (Indexed.addIdx (ZMod p)) p
      (k + lam * ((p : ℤ) - 1)) (lam * p) k s V0 = true)
    (hW : rotOK p V0 W = true) (hc : certOK p ws = true) (hR : certRows p s ws = R)
    (h : tomoGo p s W R [] = true) : ¬ HasSDS (ZMod p × ZMod p) k lam :=
  not_hasSDS_of_mem p hs hsp (fun _ hD hsum hcen j =>
    mem_W hV hW (demands_line hD j) (by rw [sum_contract, hsum]) (hcen.moment_line j)) hc hR h

end SignedDifferenceSets.Tomography
