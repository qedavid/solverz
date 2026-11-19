module

public import SignedDifferenceSets.PairSearch
public import SignedDifferenceSets.Doubling

/-!
# No SDS `Z` (27, 14, 5) and SDS `T` (27, 9, 0) with disjoint supports on C₃ × C₉ (C17x)

`K = ZMod 3 × ZMod 9`, numbered by `Indexed` (`(a, b) ↦ b + 9a`); the cosets of `ZMod 3 × 0` are
the numbers `b, b + 9, b + 18` (`kcos b`), their sums the coset sums along `snd : K → ZMod 9`.
The searches check the 13 shifts `g` with `g < −g` (`kShifts`; the sum at `−g` is the one at `g`),
their sums offset by `32`.
`zSearch` runs `PairSearch.go` over `Z` (`Z 0 = −1`, codes from `valsZ` elsewhere, coset-sum
vector among the candidates `cand`, moved into `ℕ` by `toN`) and, at each complete `Z`,
`tCheck` runs it over `T` on `Z`'s zeros, cosets with fewest zeros first, with the candidates `tc`
(pruned by cosets inside `Z`'s support). `zSearch_of_slices` splits `zSearch` at a
front. `no_pair`: with `Σ Z = 12` and `Σ T = 3` normalized by
signs and the one `−1` of `Z` translated to `0`, `LiftSearch.cover` lists the coset-sum vectors up
to rotation, and a passing `zSearch` on groups holding every rotation rules the pair out.
-/

@[expose] public section

namespace SignedDifferenceSets.PairCheck

open LiftSearch PairSearch

/-- The group `C₃ × C₉`. -/
abbrev K := ZMod 3 × ZMod 9

/-- Addition on `K`'s numbers. -/
def kAdd : ℕ → ℕ → ℕ := Indexed.addIdx K

/-- The coset of a number. -/
def kq (y : ℕ) : ℕ := y % 9

/-- The numbers of coset `b`. -/
def kcos (b : ℕ) : List ℕ := if b < 9 then [b, b + 9, b + 18] else []

/-- The shifts checked: one of each pair `g, −g`. -/
def kShifts : List ℕ := [1, 2, 3, 4, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- The step of position `x`. -/
def kStep (x : ℕ) : PairSearch.Step := PairSearch.mkStep 27 kAdd kShifts kq kcos x

/-- The shift sums of the empty assignment: the offset `32`. -/
def acc0 : List ℕ := List.replicate 13 32

/-- Candidate vectors in `ℕ`: each entry plus `3`. -/
def toN (L : List (List ℤ)) : List (List ℕ) := L.map (·.map fun z => (z + 3).toNat)

/-- `Z`'s order: coset by coset, all positions but `0`. -/
def zOrd : List ℕ := (List.range 9).flatMap fun b => (kcos b).filter fun y => y != 0

/-- Coset `b`'s positions outside the support `S`. -/
def rcount (S b : ℕ) : ℕ := ((kcos b).filter fun y => bit S y == 0).length

/-- `T`'s order: the positions outside `S`, cosets with fewest such positions first, ties by
number (core functions only: the kernel unfolds them). -/
def tOrd (S : ℕ) : List ℕ :=
  (List.range 4).flatMap fun k => ((List.range 9).filter fun b => rcount S b == k).flatMap
    fun b => (kcos b).filter fun y => bit S y == 0

/-- The candidates for `T` (entries `3` above the coset sums), `0` on every coset inside `S`. -/
def tStart (S : ℕ) (tc : List (List ℕ)) : List (List ℕ) :=
  tc.filter fun c => (List.range 9).all fun b =>
    !(kcos b).all (fun y => bit S y == 1) || Nat.beq (c.getD b 0) 3

/-- No `T` of weight `tw` with autocorrelation `0` and coset sums (plus `3`) in `tc` vanishes on
the support of `Z`, given by its masks `P`, `M`. -/
noncomputable def tCheck (tw : ℕ) (tc : List (List ℕ)) (P M : ℕ) : Bool :=
  nodupB (tOrd (Nat.lor P M)) && (tOrd (Nat.lor P M)).all (fun y => Nat.blt y 27) &&
    (List.range 27).all (fun y => bit (Nat.lor P M) y == 1 || (tOrd (Nat.lor P M)).contains y) &&
    PairSearch.go 32 [1, 2, 0] (Nat.lor P M) (fun _ _ => false)
      ((tOrd (Nat.lor P M)).map kStep) 0 0 0 acc0 tw (tStart (Nat.lor P M) tc)

/-- Every `Z` with `Z 0 = −1`, codes from `valsZ` elsewhere, `rZ + 1` nonzero values,
autocorrelation `λ = L − 32` and coset-sum vector in `cand` passes `tCheck`. -/
noncomputable def zSearch (L : ℕ) (valsZ : List ℕ) (rZ tw : ℕ) (tc cand : List (List ℤ)) :
    Bool :=
  PairSearch.go L valsZ 0 (tCheck tw (toN tc)) (zOrd.map kStep) 0 1 1 acc0 rZ (toN cand)

/-- Expand the nodes whose masks `(P, M, A)` are listed. -/
def exKeys (ks : List (ℕ × ℕ × ℕ)) (P M A : ℕ) : Bool :=
  ks.any fun k => Nat.beq k.1 P && Nat.beq k.2.1 M && Nat.beq k.2.2 A

/-- `zSearch`'s front: the nodes below the listed ones. -/
noncomputable def zFront (L : ℕ) (valsZ : List ℕ) (rZ : ℕ) (ks : List (ℕ × ℕ × ℕ))
    (cand : List (List ℤ)) : List PairSearch.Node :=
  PairSearch.front L valsZ 0 (exKeys ks) (zOrd.map kStep) 0 1 1 acc0 rZ (toN cand)

/-- The nodes `a, …, b − 1` of `zSearch`'s front pass. -/
noncomputable def zSlice (L : ℕ) (valsZ : List ℕ) (rZ tw : ℕ) (tc : List (List ℤ))
    (ks : List (ℕ × ℕ × ℕ)) (cand : List (List ℤ)) : ℕ → ℕ → Bool :=
  sliceAll (zFront L valsZ rZ ks cand) (PairSearch.Node.run L valsZ 0 (tCheck tw (toN tc)))

theorem zSearch_of_slices {L : ℕ} {valsZ : List ℕ} {rZ tw : ℕ} {tc cand : List (List ℤ)}
    {ks : List (ℕ × ℕ × ℕ)} (cuts : List ℕ)
    (hlen : (zFront L valsZ rZ ks cand).length ≤ CosetSearch.lastCut 0 cuts)
    (hsl : CosetSearch.SlicesPass (zSlice L valsZ rZ tw tc ks cand) (0 :: cuts)) :
    zSearch L valsZ rZ tw tc cand = true :=
  PairSearch.go_of_front _ _ _ _ _ _ _ fun nd hnd =>
    all_of_sliceAll cuts 0 hsl hlen nd (by rwa [List.drop_zero])

/-- Every rotation of every vector of `L`. -/
def rots (L : List (List ℤ)) : List (List ℤ) :=
  L.flatMap fun w => (List.range 9).map fun h => (List.range 9).map fun b => w.getD ((b + h) % 9) 0

/-! ### From `K` to its numbers -/

theorem size_K : Indexed.size K = 27 := rfl

theorem equiv_K (a : ZMod 3) (b : ZMod 9) :
    (Indexed.equiv ((a, b) : K) : ℕ) = b.val + 9 * a.val := rfl

/-- `E` on the numbers `0, …, 26`, `0` beyond. -/
def num (E : K → SignType) (i : ℕ) : ℤ :=
  if h : i < Indexed.size K then (E (Indexed.equiv.symm ⟨i, h⟩) : ℤ) else 0

theorem num_equiv (E : K → SignType) (x : K) : num E (Indexed.equiv x) = E x := by
  simp [num, (Indexed.equiv x).isLt]

theorem num_out (E : K → SignType) {i : ℕ} (h : 27 ≤ i) : num E i = 0 := by
  unfold num
  rw [dite_eq_right (by rw [size_K]; omega)]

theorem isSign_coe (s : SignType) : IsSign (s : ℤ) := by
  cases s
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl

theorem num_sign (E : K → SignType) (i : ℕ) : IsSign (num E i) := by
  unfold num
  split_ifs
  · exact isSign_coe _
  · exact Or.inr (Or.inl rfl)

theorem sum_num (φ : ℕ → ℤ) : ∑ i ∈ Finset.range 27, φ i = ∑ x : K, φ (Indexed.equiv x) := by
  rw [show (27 : ℕ) = Indexed.size K from rfl]
  exact (sum_equiv (G := K) φ).symm

theorem corr_num (E : K → SignType) (g' : K) :
    ∑ i ∈ Finset.range 27, num E i * num E (kAdd i (Indexed.equiv g')) =
      ∑ x, (E x : ℤ) * E (x + g') := by
  rw [sum_num]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [kAdd, ← Indexed.equiv_add, num_equiv, num_equiv]

theorem univ_zmod_three : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide

theorem num_cos (E : K → SignType) (b : ℕ) (hb : b < 9) :
    ((kcos b).map (num E)).sum = ∑ a : ZMod 3, (E (a, (b : ZMod 9)) : ℤ) := by
  have hv : ((b : ZMod 9)).val = b := ZMod.val_cast_of_lt hb
  have e : ∀ a : ZMod 3, num E (b + 9 * a.val) = E (a, (b : ZMod 9)) := fun a => by
    rw [← num_equiv E (a, (b : ZMod 9)), equiv_K, hv]
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  rw [show (0 : ZMod 3).val = 0 from rfl] at e0
  rw [show (1 : ZMod 3).val = 1 from rfl] at e1
  rw [show (2 : ZMod 3).val = 2 from rfl] at e2
  rw [univ_zmod_three, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, ← e0, ← e1, ← e2]
  simp only [kcos, hb, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring_nf

theorem contract_snd (E : K → SignType) (β : ZMod 9) :
    contract (AddMonoidHom.snd (ZMod 3) (ZMod 9)) E β = ∑ a : ZMod 3, (E (a, β) : ℤ) := by
  unfold contract
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (f := fun y => if (AddMonoidHom.snd (ZMod 3) (ZMod 9)) (a, y) = β
      then (E (a, y) : ℤ) else 0) β (fun y _ hy => ite_eq_right fun h => hy h)
    (fun h => absurd (Finset.mem_univ β) h)]
  exact ite_eq_left rfl

/-! ### The searches' soundness on `K`'s numbers -/

theorem numGroup_K : NumGroup 27 kAdd := numGroup_of_indexed K

theorem kStep_x (x : ℕ) : (kStep x).x = x := rfl

theorem map_kStep_x (l : List ℕ) : (l.map kStep).map PairSearch.Step.x = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, kStep_x, ih]

theorem testBit_one' (y : ℕ) : (1 : ℕ).testBit y = decide (y = 0) := by
  rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
  by_cases h : y = 0
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem testBit_of_bit {S y : ℕ} (h : bit S y = 1) : S.testBit y = true := by
  rw [bit_eq] at h
  cases hb : S.testBit y
  · rw [hb] at h; exact absurd h (by decide)
  · rfl

theorem kShifts_spec : ∀ g ∈ kShifts, 0 < g ∧ g < 27 := by decide

theorem length_acc0 : acc0.length = kShifts.length := rfl

theorem acc0_getD : ∀ i, i < kShifts.length → acc0.getD i 0 = 32 := by decide

theorem truth_cast {lam : ℤ} {L F : ℕ} {f : ℕ → ℤ} (h : (L : ℤ) - (32 : ℕ) = lam)
    (ht : Truth 27 kAdd lam F f) : Truth 27 kAdd ((L : ℤ) - (32 : ℕ)) F f := h ▸ ht

theorem code_mem_of_sign {z : ℤ} (hz : IsSign z) : code z ∈ [1, 2, 0] := by
  rcases hz with rfl | rfl | rfl <;> decide

/-- `tCheck` passing rules out a `t` of weight `tw` with autocorrelation `0`, coset sums (plus `3`)
in `tc`, vanishing on the support of the `z` whose masks are `P`, `M`. -/
theorem tCheck_sound {tw : ℕ} {tc : List (List ℕ)} {P M : ℕ} (h : tCheck tw tc P M = true)
    {t : ℕ → ℤ} (ht : Truth 27 kAdd 0 (Nat.lor P M) t)
    (hw : (tw : ℤ) = ∑ y ∈ Finset.range 27, t y * t y) {tv : List ℕ} (htv : tv ∈ tc)
    (hcos : ∀ b, b < 9 → (tv.getD b 0 : ℤ) = 3 + ((kcos b).map t).sum) : False := by
  unfold tCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨hnd, hlt⟩, hcov⟩, hgo⟩ := h
  have hsteps : ∀ st ∈ (tOrd (Nat.lor P M)).map kStep, st.nb = kShifts.map
      (fun g => (kAdd st.x g, kAdd st.x (negN 27 kAdd g))) ∧ code (t st.x) ∈ [1, 2, 0] ∧
      (tv.getD st.b 0 : ℤ) = 3 + (st.cs.map t).sum := by
    intro st hst
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hst
    exact ⟨rfl, code_mem_of_sign (ht.sign x), hcos _ (Nat.mod_lt _ (by norm_num))⟩
  have hinv : Inv 27 kAdd kShifts 32 t ((tOrd (Nat.lor P M)).map kStep) 0 0 0 acc0 tw := by
    refine ⟨fun y => by simp, length_acc0, fun i hi => ?_, ?_, fun st hst => ?_, ?_,
      fun y hy hf => ?_⟩
    · rw [acc0_getD i hi]; simp [onA]
    · rw [hw]; simp
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hst
      exact ⟨hlt x hx, Nat.zero_testBit _⟩
    · rw [map_kStep_x]; exact nodup_of_nodupB _ hnd
    · right
      rw [map_kStep_x]
      rcases hcov y (List.mem_range.2 hy) with h1 | h1
      · exact absurd (ht.zero y (testBit_of_bit h1)) hf
      · exact h1
  have hstart : tv ∈ tStart (Nat.lor P M) tc := by
    refine List.mem_filter.2 ⟨htv, List.all_eq_true.2 fun b hb => ?_⟩
    by_cases hall : (kcos b).all (fun y => bit (Nat.lor P M) y == 1) = true
    · rw [hall, Bool.not_true, Bool.false_or]
      have hz : ((kcos b).map t).sum = 0 := by
        refine List.sum_eq_zero fun u hu => ?_
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
        have := List.all_eq_true.1 hall y hy
        rw [beq_iff_eq] at this
        exact ht.zero y (testBit_of_bit this)
      have e := hcos b (List.mem_range.1 hb)
      rw [hz, add_zero] at e
      rw [show tv.getD b 0 = 3 by exact_mod_cast e]
      exact Nat.beq_refl _
    · rw [Bool.eq_false_iff.2 hall]
      rfl
  obtain ⟨_, _, -, hleaf⟩ := PairSearch.go_sound numGroup_K kShifts_spec (by norm_num)
    (truth_cast (by norm_num) ht) _ _ _ _ _ _ _ hgo hsteps hinv hstart
  exact Bool.false_ne_true hleaf

theorem zOrd_spec : ∀ x ∈ zOrd, x ≠ 0 ∧ x < 27 := by decide

theorem zOrd_cover : ∀ y < 27, y = 0 ∨ y ∈ zOrd := by decide

theorem zOrd_nodup : zOrd.Nodup := by decide

/-- `zSearch` passing rules out an SDS-like `z` (`z 0 = −1`, no other `−1`, 14 nonzero values,
autocorrelation `5`, coset sums (plus `3`) in `toN cand`) and a `t` as in `tCheck_sound` vanishing
where `z` does not. -/
theorem zSearch_sound {tc cand : List (List ℤ)} (h : zSearch 37 [1, 0] 13 9 tc cand = true)
    {z t : ℕ → ℤ} (hz : Truth 27 kAdd 5 0 z) (hz0 : z 0 = -1) (hzm : ∀ y, y ≠ 0 → z y ≠ -1)
    (hzw : (14 : ℤ) = ∑ y ∈ Finset.range 27, z y * z y) {zv : List ℕ} (hzv : zv ∈ toN cand)
    (hzcos : ∀ b, b < 9 → (zv.getD b 0 : ℤ) = 3 + ((kcos b).map z).sum)
    (ht : Truth 27 kAdd 0 0 t) (htw : (9 : ℤ) = ∑ y ∈ Finset.range 27, t y * t y)
    {tv : List ℕ} (htv : tv ∈ toN tc)
    (htcos : ∀ b, b < 9 → (tv.getD b 0 : ℤ) = 3 + ((kcos b).map t).sum)
    (hd : ∀ y, z y = 0 ∨ t y = 0) : False := by
  unfold zSearch at h
  have hsteps : ∀ st ∈ zOrd.map kStep, st.nb = kShifts.map
      (fun g => (kAdd st.x g, kAdd st.x (negN 27 kAdd g))) ∧ code (z st.x) ∈ [1, 0] ∧
      (zv.getD st.b 0 : ℤ) = 3 + (st.cs.map z).sum := by
    intro st hst
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hst
    refine ⟨rfl, ?_, hzcos _ (Nat.mod_lt _ (by norm_num))⟩
    rw [kStep_x]
    have := hzm x (zOrd_spec x hx).1
    rcases hz.sign x with h1 | h1 | h1
    · rw [h1]; decide
    · rw [h1]; decide
    · exact absurd h1 this
  have e : ∀ y ∈ Finset.range 27, z y * z y =
      (if (1 : ℕ).testBit y then (0 : ℤ) else z y * z y) + (if y = 0 then z 0 * z 0 else 0) := by
    intro y _
    rw [testBit_one']
    by_cases hy : y = 0
    · subst hy; simp
    · simp [hy]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range 27) 0,
    ite_eq_left (Finset.mem_range.2 (by norm_num)), hz0] at hzw
  have hinv : Inv 27 kAdd kShifts 32 z (zOrd.map kStep) 0 1 1 acc0 13 := by
    refine ⟨fun y => ?_, length_acc0, fun i hi => ?_, ?_, fun st hst => ?_, ?_,
      fun y hy hf => ?_⟩
    · rw [Nat.zero_testBit, testBit_one']
      by_cases hy : y = 0
      · subst hy; simp [hz0]
      · simp [hy]
    · obtain ⟨h0, hg⟩ := kShifts_spec _ (getD_mem hi)
      rw [acc0_getD i hi, Finset.sum_eq_zero fun y _ => ?_]
      · norm_num
      set g := kShifts.getD i 0
      simp only [onA, testBit_one']
      by_cases hy : y = 0
      · subst hy
        have : kAdd 0 g = g := by
          rw [numGroup_K.comm 0 g (by norm_num) hg, numGroup_K.zero g hg]
        simp [this, h0.ne']
      · simp [hy]
    · push_cast
      linarith
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hst
      refine ⟨(zOrd_spec x hx).2, ?_⟩
      rw [kStep_x, testBit_one']
      simpa using (zOrd_spec x hx).1
    · rw [map_kStep_x]; exact zOrd_nodup
    · rw [map_kStep_x, testBit_one']
      rcases zOrd_cover y hy with h1 | h1
      · left; simpa using h1
      · exact Or.inr h1
  obtain ⟨P, M, hPM, hleaf⟩ := PairSearch.go_sound numGroup_K kShifts_spec (by norm_num)
    (truth_cast (by norm_num) hz) _ _ _ _ _ _ _ h hsteps hinv hzv
  refine tCheck_sound hleaf ⟨ht.out, ht.sign, fun y hy => ?_, ht.corr⟩ htw htv htcos
  have hz' : z y ≠ 0 := by
    rw [show Nat.lor P M = P ||| M from rfl, Nat.testBit_or, Bool.or_eq_true, (hPM y).1,
      (hPM y).2, decide_eq_true_eq, decide_eq_true_eq] at hy
    rcases hy with h1 | h1 <;> rw [h1] <;> decide
  exact (hd y).resolve_left hz'

/-! ### From `Z` and `T` on `K` -/

/-- An SDS's sum squared is `k + λ (v − 1)` (C1). -/
theorem sum_mul_sum_of_isSDS {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ} {lam : ℤ}
    {D : G → SignType} (hD : IsSDS k lam D) :
    (∑ x, (D x : ℤ)) * ∑ x, (D x : ℤ) = k + lam * (Fintype.card G - 1) := by
  classical
  rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  have h0 : ∑ h, (D h : ℤ) * D (h + 0) = k := by
    simp only [add_zero]
    rw [← card_ne_zero_eq_sum_sq, hD.1]
  rw [h0, Finset.sum_congr rfl fun g hg => hD.2 g (Finset.ne_of_mem_erase hg),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]
  push_cast
  ring

theorem num_corr (E : K → SignType) {k : ℕ} {lam : ℤ} (hE : IsSDS k lam E) {g : ℕ} (h0 : 0 < g)
    (hg : g < 27) : ∑ i ∈ Finset.range 27, num E i * num E (kAdd i g) = lam := by
  obtain ⟨g', rfl⟩ : ∃ g' : K, (Indexed.equiv g' : ℕ) = g :=
    ⟨Indexed.equiv.symm ⟨g, hg⟩, by simp⟩
  rw [corr_num]
  refine hE.2 g' fun h => ?_
  rw [h, Indexed.equiv_zero] at h0
  exact lt_irrefl 0 h0

theorem num_sq (E : K → SignType) {k : ℕ} {lam : ℤ} (hE : IsSDS k lam E) :
    (k : ℤ) = ∑ i ∈ Finset.range 27, num E i * num E i := by
  rw [sum_num, ← hE.1, card_ne_zero_eq_sum_sq]
  simp [num_equiv]

theorem truth_num (E : K → SignType) {k : ℕ} {lam : ℤ} (hE : IsSDS k lam E) :
    Truth 27 kAdd lam 0 (num E) :=
  ⟨fun _ h => num_out E h, num_sign E, fun y h => by simp at h,
    fun _ h0 hg => num_corr E hE h0 hg⟩

/-- The coset-sum vector of `E` on the numbers. -/
def cosVec (E : K → SignType) : List ℤ :=
  (List.range 9).map fun b => ((kcos b).map (num E)).sum

theorem cosVec_getD (E : K → SignType) (b : ℕ) :
    (cosVec E).getD b 0 = ((kcos b).map (num E)).sum := by
  by_cases hb : b < 9
  · simp [cosVec, List.getD_eq_getElem?_getD, hb]
  · simp [cosVec, List.getD_eq_getElem?_getD, kcos, hb]

theorem num_ge (E : K → SignType) (i : ℕ) : -1 ≤ num E i := by
  rcases num_sign E i with h | h | h <;> rw [h] <;> norm_num

/-- The coset-sum vector of `E` in `ℕ` (entries plus `3`). -/
theorem cosVec_toN_getD (E : K → SignType) {b : ℕ} (hb : b < 9) :
    ((((cosVec E).map fun z => (z + 3).toNat).getD b 0 : ℕ) : ℤ) =
      3 + ((kcos b).map (num E)).sum := by
  have h3 : -3 ≤ ((kcos b).map (num E)).sum := by
    simp only [kcos, hb, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := num_ge E b
    have := num_ge E (b + 9)
    have := num_ge E (b + 18)
    linarith
  have hl : b < ((cosVec E).map fun z => (z + 3).toNat).length := by simp [cosVec, hb]
  rw [List.getD_eq_getElem _ _ hl, List.getElem_map]
  simp only [cosVec, List.getElem_map, List.getElem_range]
  rw [Int.toNat_of_nonneg (by linarith)]
  ring

theorem rot_idx : ∀ h₀ : ZMod 9, ∀ b : Fin 9,
    ((((b : ℕ) + (9 - h₀.val) % 9) % 9 : ℕ) : ZMod 9) + h₀ = ((b : ℕ) : ZMod 9) := by decide

/-- The coset-sum vector of an SDS `E` on `K` is a rotation of a vector `cover` lists. -/
theorem cosVec_mem_rots {k : ℕ} {lam : ℤ} {s : ℤ} {L : List (List ℤ)}
    (hcov : LiftSearch.cover (Indexed.size (ZMod 9)) (Indexed.addIdx (ZMod 9)) ((3 : ℕ) : ℤ)
      ((k : ℤ) + lam * (((3 : ℕ) : ℤ) - 1)) (lam * ((3 : ℕ) : ℤ)) (k : ℤ) s L = true)
    (E : K → SignType) (hE : IsSDS k lam E) (hs : ∑ x, (E x : ℤ) = s) : cosVec E ∈ rots L := by
  classical
  have hφ : Function.Surjective (AddMonoidHom.snd (ZMod 3) (ZMod 9)) := fun b => ⟨(0, b), rfl⟩
  have hcard : Fintype.card K = 3 * Fintype.card (ZMod 9) := by simp
  have hfib := card_fibre_eq hφ hcard
  set Y := contract (AddMonoidHom.snd (ZMod 3) (ZMod 9)) E with hY
  have hdem : Demands 3 k lam Y :=
    { bound := fun h => by
        have := abs_contract_le (AddMonoidHom.snd (ZMod 3) (ZMod 9)) E h
        rwa [hfib] at this
      sq := by rw [hE.contract_sq, hfib 0]; norm_num
      corr := fun g hg => by rw [hE.contract_autocorr _ g hg, hfib]
      abs := hE.sum_abs_contract_le _
      parity := hE.sum_abs_contract_parity _ }
  obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => |Y h|)
    Finset.univ_nonempty
  have hsum : ∑ h, Y (h + h₀) = s := by
    rw [Fintype.sum_equiv (Equiv.addRight h₀) (fun h => Y (h + h₀)) Y fun _ => rfl, ← hs,
      ← sum_fibre (AddMonoidHom.snd (ZMod 3) (ZMod 9))]
    rfl
  have hmem := LiftSearch.mem_of_cover hcov (hdem.translate h₀)
    (fun h => by simpa using hmax (h + h₀) (Finset.mem_univ _)) hsum
  refine List.mem_flatMap.2 ⟨_, hmem, List.mem_map.2 ⟨(9 - h₀.val) % 9,
    List.mem_range.2 (Nat.mod_lt _ (by norm_num)), ?_⟩⟩
  unfold cosVec
  refine List.map_congr_left fun b hb => ?_
  have hb9 := List.mem_range.1 hb
  have hj : (b + (9 - h₀.val) % 9) % 9 < Indexed.size (ZMod 9) := Nat.mod_lt _ (by norm_num)
  rw [getD_ofFn _ hj, num_cos E b hb9, ← contract_snd]
  exact congrArg Y (rot_idx h₀ ⟨b, hb9⟩)

/-- The sign of an SDS on `K` whose sum is `s` or `−s` can be chosen so that it is `s`. -/
theorem exists_sum_eq {k : ℕ} {lam : ℤ} {E : K → SignType} (hE : IsSDS k lam E) {s : ℤ}
    (hs : s * s = k + lam * 26) :
    ∃ σ : SignType, σ ≠ 0 ∧ ∑ x, ((σ * E x : SignType) : ℤ) = s := by
  have h := sum_mul_sum_of_isSDS hE
  rw [show Fintype.card K = 27 from rfl] at h
  rcases mul_self_eq_mul_self_iff.1 (h.trans (by rw [hs]; push_cast; ring)) with h1 | h1
  · exact ⟨1, by decide, by simpa using h1⟩
  · refine ⟨-1, by decide, ?_⟩
    simp only [SignType.coe_neg, neg_one_mul, Finset.sum_neg_distrib, h1, neg_neg]

theorem isSDS_smul {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ} {lam : ℤ} {E : G → SignType}
    (hE : IsSDS k lam E) {σ : SignType} (hσ : σ ≠ 0) : IsSDS k lam (fun x => σ * E x) := by
  cases σ
  · exact absurd rfl hσ
  · have e : (fun x => SignType.neg * E x) = fun x => -E x := funext fun x => by cases E x <;> rfl
    rw [e]; exact hE.neg
  · have e : (fun x => SignType.pos * E x) = E := funext fun x => by cases E x <;> rfl
    rw [e]; exact hE

theorem num_ne_neg_one (E : K → SignType) (hE : ∀ x, (E x : ℤ) = -1 → x = 0) {y : ℕ}
    (hy : y ≠ 0) : num E y ≠ -1 := by
  by_cases h27 : y < 27
  · obtain ⟨x, rfl⟩ : ∃ x : K, (Indexed.equiv x : ℕ) = y :=
      ⟨Indexed.equiv.symm ⟨y, h27⟩, by simp⟩
    rw [num_equiv]
    intro h
    rw [hE x h, Indexed.equiv_zero] at hy
    exact hy rfl
  · rw [num_out E (by omega)]; decide

/-- No SDS `Z` (27, 14, 5) and SDS `T` (27, 9, 0) on `K` have disjoint supports, given the covers
of their coset-sum vectors and passing searches on groups that hold every rotation of `Z`'s. -/
theorem no_pair {LY LT : List (List ℤ)} (groups : List (List (List ℤ)))
    (hY : LiftSearch.cover (Indexed.size (ZMod 9)) (Indexed.addIdx (ZMod 9)) ((3 : ℕ) : ℤ)
      (((14 : ℕ) : ℤ) + 5 * (((3 : ℕ) : ℤ) - 1)) (5 * ((3 : ℕ) : ℤ)) ((14 : ℕ) : ℤ) 12 LY = true)
    (hT : LiftSearch.cover (Indexed.size (ZMod 9)) (Indexed.addIdx (ZMod 9)) ((3 : ℕ) : ℤ)
      (((9 : ℕ) : ℤ) + 0 * (((3 : ℕ) : ℤ) - 1)) (0 * ((3 : ℕ) : ℤ)) ((9 : ℕ) : ℤ) 3 LT = true)
    (hgr : ∀ c ∈ rots LY, ∃ grp ∈ groups, c ∈ grp)
    (hsl : ∀ grp ∈ groups, zSearch 37 [1, 0] 13 9 (rots LT) grp = true)
    {Z T : K → SignType} (hZ : IsSDS 14 5 Z) (hT' : IsSDS 9 0 T)
    (hd : ∀ y, Z y = 0 ∨ T y = 0) : False := by
  classical
  -- signs: `Σ Z = 12`, `Σ T = 3`
  obtain ⟨σ, hσ, hsZ⟩ := exists_sum_eq hZ (s := 12) (by norm_num)
  obtain ⟨τ, hτ, hsT⟩ := exists_sum_eq hT' (s := 3) (by norm_num)
  have hZ₁ := isSDS_smul hZ hσ
  have hT₁ := isSDS_smul hT' hτ
  -- the one `−1` of `Z`
  have hcnt : ∑ x, (if ((σ * Z x : SignType) : ℤ) = -1 then (2 : ℤ) else 0) = 2 := by
    have e : ∀ x, (if ((σ * Z x : SignType) : ℤ) = -1 then (2 : ℤ) else 0) =
        |((σ * Z x : SignType) : ℤ)| - ((σ * Z x : SignType) : ℤ) := fun x => by
      generalize σ * Z x = s
      cases s <;> simp
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_sub_distrib, hZ₁.sum_abs, hsZ]
    norm_num
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hcnt
  have hone : (Finset.univ.filter fun x => ((σ * Z x : SignType) : ℤ) = -1).card = 1 := by
    have : ((Finset.univ.filter fun x => ((σ * Z x : SignType) : ℤ) = -1).card : ℤ) = 1 := by
      linarith
    exact_mod_cast this
  obtain ⟨m, hm⟩ := Finset.card_eq_one.1 hone
  have hmZ : ((σ * Z m : SignType) : ℤ) = -1 := by
    have : m ∈ Finset.univ.filter fun x => ((σ * Z x : SignType) : ℤ) = -1 := by
      rw [hm]; exact Finset.mem_singleton_self m
    exact (Finset.mem_filter.1 this).2
  have hmu : ∀ y, ((σ * Z y : SignType) : ℤ) = -1 → y = m := fun y hy => by
    have : y ∈ Finset.univ.filter fun x => ((σ * Z x : SignType) : ℤ) = -1 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
    rw [hm] at this
    exact Finset.mem_singleton.1 this
  -- translate it to `0`
  set Z₂ : K → SignType := fun x => σ * Z (x + m) with hZ₂def
  set T₂ : K → SignType := fun x => τ * T (x + m) with hT₂def
  have hZ₂ : IsSDS 14 5 Z₂ := hZ₁.translate m
  have hT₂ : IsSDS 9 0 T₂ := hT₁.translate m
  have hsZ₂ : ∑ x, (Z₂ x : ℤ) = 12 := by
    rw [← hsZ]; exact Fintype.sum_equiv (Equiv.addRight m) _ _ fun _ => rfl
  have hsT₂ : ∑ x, (T₂ x : ℤ) = 3 := by
    rw [← hsT]; exact Fintype.sum_equiv (Equiv.addRight m) _ _ fun _ => rfl
  have hZ₂m : ∀ x, (Z₂ x : ℤ) = -1 → x = 0 := fun x hx => by
    have := hmu _ hx
    simpa using this
  have hz0 : num Z₂ 0 = -1 := by
    have := num_equiv Z₂ 0
    rw [Indexed.equiv_zero] at this
    rw [this]
    simpa [hZ₂def] using hmZ
  have hzv := cosVec_mem_rots hY Z₂ hZ₂ hsZ₂
  have htv := cosVec_mem_rots hT T₂ hT₂ hsT₂
  obtain ⟨grp, hgrp, hzg⟩ := hgr _ hzv
  refine zSearch_sound (hsl grp hgrp) (truth_num Z₂ hZ₂) hz0
    (fun y hy => num_ne_neg_one Z₂ hZ₂m hy) (num_sq Z₂ hZ₂) (List.mem_map_of_mem hzg)
    (fun b hb => cosVec_toN_getD Z₂ hb) (truth_num T₂ hT₂) (num_sq T₂ hT₂)
    (List.mem_map_of_mem htv) (fun b hb => cosVec_toN_getD T₂ hb) fun y => ?_
  by_cases h27 : y < 27
  · obtain ⟨x, rfl⟩ : ∃ x : K, (Indexed.equiv x : ℕ) = y :=
      ⟨Indexed.equiv.symm ⟨y, h27⟩, by simp⟩
    rw [num_equiv, num_equiv]
    rcases hd (x + m) with h | h
    · left; simp [hZ₂def, h]
    · right; simp [hT₂def, h]
  · left; exact num_out Z₂ (by omega)

end SignedDifferenceSets.PairCheck
