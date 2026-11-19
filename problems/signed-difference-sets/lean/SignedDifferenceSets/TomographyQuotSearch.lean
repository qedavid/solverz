module

public import SignedDifferenceSets.Tomography

/-!
# Line tomography on a quotient, the kernel's side (I23)

Three checks on numbers for `TomographyQuot`. `orbSearch` lists the vectors on `n` coordinates
that are constant on given orbits (`orb h` the orbit of `h`, `sz` the orbit sizes): one value
per orbit in order, the last solved from the sum, pruned like `cut` with the orbit sizes as
weights; a complete vector passes when it fails the demands or `m1ok`, or is in `W`.
`ptOK p s W g`: the residues `Σⱼ yⱼ(lineⱼ g) mod p` reachable with every `yⱼ ∈ W` miss `s`.
`tomoGoL`: `tomoGo` with any leaf test, here `leafQ` (every `lineSum − s` is `p z` with
`|z| ≤ c`).
-/

@[expose] public section

namespace SignedDifferenceSets.Tomography

/-! ### Orbit-constant vectors -/

/-- The vector on `n` coordinates with entry `vals[orb h]` at `h`. -/
def expand (n : ℕ) (orb : List ℕ) (vals : List ℤ) : List ℤ :=
  (List.range n).map fun h => vals.getD (orb.getD h 0) 0

/-- A complete vector passes when it fails the demands or `m1ok`, or is in `W`. -/
def orbLeaf (n : ℕ) (add : ℕ → ℕ → ℕ) (Q t k s : ℤ) (W : List (List ℤ)) (y : List ℤ) :
    Bool :=
  !leafOK n add Q t k s y y.sum (sqSum y) (absSum y) || !m1ok n y || W.contains y

/-- The last orbit (size `z`) takes the value `r / z` that completes the sum `r`. -/
def orbLast (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (orb : List ℕ) (W : List (List ℤ))
    (z : ℕ) (pre : List ℤ) (r : ℤ) : Bool :=
  !(r % z == 0) || decide (c < |r / z|) ||
    orbLeaf n add Q t k s W (expand n orb (r / z :: pre).reverse)

/-- No orbit values completing `pre` (reversed; weighted sums `sum`, `sq`) for the orbits of
sizes `zs` give a vector outside `W` that meets the demands and `m1ok`. -/
def orbGo (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (orb : List ℕ) (W : List (List ℤ)) :
    List ℕ → List ℤ → ℤ → ℤ → Bool
  | [], _, _, _ => true
  | [z], pre, sum, _ => orbLast n add c Q t k s orb W z pre (s - sum)
  | z :: z' :: zs, pre, sum, sq =>
    cut c Q s (z :: z' :: zs).sum sum sq ||
      allRange (fun x => decide (Q - sq < z * (x * x)) ||
        orbGo n add c Q t k s orb W (z' :: zs) (x :: pre) (sum + z * x) (sq + z * (x * x)))
        (-c) (2 * c + 1).toNat

/-- Every vector constant on the orbits `orb` (sizes `sz`) meeting the demands and `m1ok` is
in `W`. -/
def orbSearch (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (orb sz : List ℕ)
    (W : List (List ℤ)) : Bool :=
  orbGo n add c Q t k s orb W sz [] 0 0

/-- `Σᵢ zᵢ uᵢ`. -/
def wsum : List ℕ → List ℤ → ℤ
  | z :: zs, u :: us => z * u + wsum zs us
  | _, _ => 0

/-- `Σᵢ zᵢ uᵢ²`. -/
def wsq : List ℕ → List ℤ → ℤ
  | z :: zs, u :: us => z * (u * u) + wsq zs us
  | _, _ => 0

/-- Each `uᵢ` repeated `zᵢ` times. -/
def rep : List ℕ → List ℤ → List ℤ
  | z :: zs, u :: us => List.replicate z u ++ rep zs us
  | _, _ => []

theorem sum_rep : ∀ (zs : List ℕ) (us : List ℤ), (rep zs us).sum = wsum zs us
  | [], _ => rfl
  | _ :: _, [] => rfl
  | z :: zs, u :: us => by simp [rep, wsum, sum_rep zs us]

theorem sqSum_rep : ∀ (zs : List ℕ) (us : List ℤ), sqSum (rep zs us) = wsq zs us
  | [], _ => rfl
  | _ :: _, [] => rfl
  | z :: zs, u :: us => by
    have := sqSum_rep zs us
    simp only [sqSum] at this
    simp [rep, wsq, sqSum, this, List.map_replicate, List.sum_replicate]

theorem length_rep : ∀ (zs : List ℕ) (us : List ℤ), us.length = zs.length →
    (rep zs us).length = zs.sum
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | z :: zs, u :: us, h => by
    simp only [List.length_cons, add_left_inj] at h
    simp [rep, length_rep zs us h]

theorem abs_rep_le {c : ℤ} : ∀ (zs : List ℕ) (us : List ℤ), (∀ u ∈ us, |u| ≤ c) →
    ∀ y ∈ rep zs us, |y| ≤ c
  | [], _, _, y, hy => by simp [rep] at hy
  | _ :: _, [], _, y, hy => by simp [rep] at hy
  | z :: zs, u :: us, hc, y, hy => by
    simp only [rep, List.mem_append, List.mem_replicate] at hy
    rcases hy with ⟨-, rfl⟩ | hy
    · exact hc _ List.mem_cons_self
    · exact abs_rep_le zs us (fun v hv => hc v (List.mem_cons_of_mem _ hv)) y hy

theorem wsq_nonneg : ∀ (zs : List ℕ) (us : List ℤ), 0 ≤ wsq zs us
  | [], _ => le_rfl
  | _ :: _, [] => le_rfl
  | z :: zs, u :: us => by
    have := wsq_nonneg zs us
    simp only [wsq]
    have : (0 : ℤ) ≤ z * (u * u) := mul_nonneg (by positivity) (mul_self_nonneg u)
    linarith

/-- A passing `orbGo` leaves every completion `us` (one value per remaining orbit) to the leaf. -/
theorem orbGo_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {orb : List ℕ}
    {W : List (List ℤ)} :
    ∀ (zs : List ℕ) (us pre : List ℤ) (sum sq : ℤ),
      orbGo n add c Q t k s orb W zs pre sum sq = true → us.length = zs.length → zs ≠ [] →
      (∀ z ∈ zs, 0 < z) → (∀ u ∈ us, |u| ≤ c) → sum + wsum zs us = s →
      sq + wsq zs us = Q → orbLeaf n add Q t k s W (expand n orb (pre.reverse ++ us)) = true
  | [], _, _, _, _, _, _, hne, _, _, _, _ => absurd rfl hne
  | [z], [], _, _, _, _, hlen, _, _, _, _, _ => by simp at hlen
  | [z], u :: _ :: _, _, _, _, _, hlen, _, _, _, _, _ => by simp at hlen
  | [z], [u], pre, sum, sq, h, _, _, hz, hc, hs, _ => by
    have hz0 : (z : ℤ) ≠ 0 := by exact_mod_cast (hz z List.mem_cons_self).ne'
    have hr : s - sum = z * u := by simp only [wsum] at hs; linarith
    have hu := hc u List.mem_cons_self
    simp only [orbGo, orbLast, hr, Int.mul_emod_right, Int.mul_ediv_cancel_left _ hz0] at h
    simpa [not_lt.2 hu] using h
  | z :: z' :: zs, [], _, _, _, _, hlen, _, _, _, _, _ => by simp at hlen
  | z :: z' :: zs, u :: us, pre, sum, sq, h, hlen, _, hz, hc, hs, hq => by
    have hcut := cut_false (c := c) (Q := Q) (s := s) (sum := sum) (sq := sq)
      (rep (z :: z' :: zs) (u :: us)) (abs_rep_le _ _ hc) (by rw [sum_rep]; exact hs)
      (by rw [sqSum_rep]; exact hq)
    rw [length_rep _ _ hlen] at hcut
    simp only [orbGo] at h
    rw [hcut, Bool.false_or] at h
    have hu := hc u List.mem_cons_self
    have hx := allRange_abs h hu
    have hw := wsq_nonneg (z' :: zs) us
    simp only [wsum, wsq] at hs hq
    have hsq : ¬ Q - sq < z * (u * u) := by linarith
    simp only [hsq, decide_false, Bool.false_or] at hx
    have := orbGo_sound (z' :: zs) us (u :: pre) (sum + z * u) (sq + z * (u * u)) hx
      (by simpa using hlen) (List.cons_ne_nil _ _)
      (fun y hy => hz y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy)) (by linarith) (by linarith)
    simpa using this

theorem wsum_eq_sum (f : ℤ → ℤ) :
    ∀ (zs : List ℕ) (us : List ℤ), us.length = zs.length →
      wsum zs (us.map f) = ∑ i ∈ Finset.range zs.length, (zs.getD i 0 : ℤ) * f (us.getD i 0)
  | [], _, _ => by simp [wsum]
  | _ :: _, [], h => by simp at h
  | z :: zs, u :: us, h => by
    simp only [List.length_cons, add_left_inj] at h
    rw [List.map_cons, wsum, wsum_eq_sum f zs us h, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- Summing over the orbits with their sizes is summing over the coordinates. -/
theorem sum_sizes (f : ℤ → ℤ) {n : ℕ} {orb sz : List ℕ} (us : List ℤ)
    (horb : ∀ h < n, orb.getD h 0 < sz.length)
    (hsz : ∀ i < sz.length,
      (sz.getD i 0 : ℤ) = sumTo (fun h => if orb.getD h 0 = i then 1 else 0) n) :
    ∑ i ∈ Finset.range sz.length, (sz.getD i 0 : ℤ) * f (us.getD i 0) =
      ∑ h ∈ Finset.range n, f (us.getD (orb.getD h 0) 0) := by
  have e1 : ∀ i ∈ Finset.range sz.length, (sz.getD i 0 : ℤ) * f (us.getD i 0) =
      ∑ h ∈ Finset.range n, if orb.getD h 0 = i then f (us.getD i 0) else 0 := by
    intro i hi
    rw [hsz i (Finset.mem_range.1 hi), sumTo_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.2 (horb h (Finset.mem_range.1 hh)))]

theorem wsq_eq_wsum : ∀ (zs : List ℕ) (us : List ℤ),
    wsq zs us = wsum zs (us.map fun u => u * u)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | z :: zs, u :: us => by simp [wsq, wsum, wsq_eq_wsum zs us]

/-- Orbit data for `h ↦ t h` on `ZMod p`: `h ≡ t^(ex h) · rep (orb h)` with `orb h < m`, and
orbit `i < m` has `sz i > 0` elements. -/
def orbOK (p t : ℕ) (orb sz rep ex : List ℕ) : Bool :=
  allTo (fun h => decide (orb.getD h 0 < sz.length) &&
    (t ^ ex.getD h 0 * rep.getD (orb.getD h 0) 0) % p == h) p &&
  allTo (fun i => decide (0 < sz.getD i 0) &&
    (sz.getD i 0 : ℤ) == sumTo (fun h => if orb.getD h 0 = i then 1 else 0) p) sz.length

/-! ### One point -/

/-- The residues `r' < p` with `r' ≡ r + v` for some `r ∈ R`, `v ∈ S`. -/
def ptStep (p : ℕ) (S R : List ℤ) : List ℤ :=
  ((List.range p).map fun r : ℕ => (r : ℤ)).filter fun r' =>
    R.any fun r => S.any fun v => (r + v - r') % (p : ℤ) == 0

/-- The residues of `Σ_{i < j} yᵢ(lineᵢ g)` with every `yᵢ ∈ W`. -/
def ptReach (p : ℕ) (W : List (List ℤ)) (g : ℕ) : ℕ → List ℤ
  | 0 => [0]
  | j + 1 => ptStep p (W.map fun y => y.getD (lineIdx p j g) 0) (ptReach p W g j)

/-- No choice from `W` has `Σⱼ yⱼ(lineⱼ g) ≡ s (mod p)`. -/
def ptOK (p : ℕ) (s : ℤ) (W : List (List ℤ)) (g : ℕ) : Bool :=
  !(ptReach p W g (p + 1)).any fun r => (r - s) % (p : ℤ) == 0

theorem ptReach_mem {p : ℕ} (hp : 0 < p) {W : List (List ℤ)} {g : ℕ} {ys : List (List ℤ)}
    (hW : ∀ y ∈ ys, y ∈ W) :
    ∀ j, j ≤ ys.length → ∃ r ∈ ptReach p W g j,
      (p : ℤ) ∣ r - sumTo (fun i => (ys.getD i []).getD (lineIdx p i g) 0) j
  | 0, _ => ⟨0, by simp [ptReach], by simp [sumTo]⟩
  | j + 1, hj => by
    obtain ⟨r, hr, hr'⟩ := ptReach_mem hp hW j (by omega)
    set v := (ys.getD j []).getD (lineIdx p j g) 0
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    have hd : (r + v) % (p : ℤ) - (r + v) = p * (-((r + v) / p)) := by
      rw [Int.emod_def]; ring
    have hv : v ∈ W.map fun y => y.getD (lineIdx p j g) 0 := by
      refine List.mem_map.2 ⟨ys.getD j [], hW _ ?_, rfl⟩
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have hmem : (r + v) % (p : ℤ) ∈ (List.range p).map fun r : ℕ => (r : ℤ) := by
      refine List.mem_map.2 ⟨((r + v) % p).toNat, List.mem_range.2 ?_, ?_⟩
      · have := Int.emod_lt_of_pos (r + v) hp'
        omega
      · exact Int.toNat_of_nonneg (Int.emod_nonneg _ hp'.ne')
    refine ⟨(r + v) % p, List.mem_filter.2 ⟨hmem, List.any_eq_true.2 ⟨r, hr,
      List.any_eq_true.2 ⟨v, hv, beq_iff_eq.2 ?_⟩⟩⟩, ?_⟩
    · have : r + v - (r + v) % (p : ℤ) = p * ((r + v) / p) := by rw [Int.emod_def]; ring
      rw [this, Int.mul_emod_right]
    · rw [sumTo]
      have e : (r + v) % (p : ℤ) - (sumTo (fun i => (ys.getD i []).getD (lineIdx p i g) 0) j + v) =
          ((r + v) % p - (r + v)) + (r - sumTo (fun i => (ys.getD i []).getD (lineIdx p i g) 0) j)
          := by ring
      rw [e, hd]
      exact dvd_add (dvd_mul_right _ _) hr'

/-- A passing `ptOK` leaves no choice from `W` with `lineSum g ≡ s (mod p)`. -/
theorem ptOK_sound {p : ℕ} (hp : 0 < p) {s : ℤ} {W : List (List ℤ)} {g : ℕ}
    (h : ptOK p s W g = true) (ys : List (List ℤ)) (hlen : ys.length = p + 1)
    (hW : ∀ y ∈ ys, y ∈ W) (hint : (lineSum p ys g - s) % (p : ℤ) = 0) : False := by
  obtain ⟨r, hr, hr'⟩ := ptReach_mem (g := g) hp hW (p + 1) hlen.ge
  have e : (r - s) % (p : ℤ) = 0 := by
    have : r - s = (r - lineSum p ys g) + (lineSum p ys g - s) := by ring
    rw [this]
    exact Int.emod_eq_zero_of_dvd (dvd_add hr' (Int.dvd_of_emod_eq_zero hint))
  have h1 : (ptReach p W g (p + 1)).any (fun r => (r - s) % (p : ℤ) == 0) = false := by
    simpa [ptOK] using h
  exact List.any_eq_false.1 h1 r hr (beq_iff_eq.2 e)

/-! ### The line search with any leaf -/

/-- Every `lineSum − s` is `p z` with `|z| ≤ c`. -/
def leafQ (p : ℕ) (s : ℤ) (c : ℕ) (ys : List (List ℤ)) : Bool :=
  allTo (fun x => (lineSum p ys x - s) % (p : ℤ) == 0 &&
    decide (|lineSum p ys x - s| ≤ (p : ℤ) * c)) (p * p)

/-- `tomoGo` whose leaves pass when they fail `leaf`. -/
def tomoGoL (p : ℕ) (leaf : List (List ℤ) → Bool) (W : List (List ℤ)) :
    List (List Row) → List (List ℤ) → Bool
  | [], cur => !leaf cur.reverse
  | rs :: rest, cur =>
    let tg := rs.map fun r => (r.1.headD [], r.2 - rowSum p r.1.tail cur)
    W.all fun y => !(tg.all fun q => (dot p q.1 y - q.2) % (p : ℤ) == 0) ||
      tomoGoL p leaf W rest (y :: cur)

/-- `tomoGoL`'s top `m` levels; a node `m` levels down is left to the list `P`. -/
def tomoTopL (p : ℕ) (leaf : List (List ℤ) → Bool) (W : List (List ℤ))
    (P : List (List (List ℤ))) : ℕ → List (List Row) → List (List ℤ) → Bool
  | 0, _, cur => P.contains cur
  | _ + 1, [], cur => !leaf cur.reverse
  | m + 1, rs :: rest, cur =>
    let tg := rs.map fun r => (r.1.headD [], r.2 - rowSum p r.1.tail cur)
    W.all fun y => !(tg.all fun q => (dot p q.1 y - q.2) % (p : ℤ) == 0) ||
      tomoTopL p leaf W P m rest (y :: cur)

theorem tomoGoL_cons (p : ℕ) (leaf : List (List ℤ) → Bool) (W : List (List ℤ)) (rs : List Row)
    (rest : List (List Row)) (cur : List (List ℤ)) :
    tomoGoL p leaf W (rs :: rest) cur =
      W.all fun y => !rowsHold p rs (y :: cur) || tomoGoL p leaf W rest (y :: cur) := by
  simp only [tomoGoL, targets_eq]

theorem tomoTopL_cons (p : ℕ) (leaf : List (List ℤ) → Bool) (W : List (List ℤ))
    (P : List (List (List ℤ))) (m : ℕ) (rs : List Row) (rest : List (List Row))
    (cur : List (List ℤ)) :
    tomoTopL p leaf W P (m + 1) (rs :: rest) cur =
      W.all fun y => !rowsHold p rs (y :: cur) || tomoTopL p leaf W P m rest (y :: cur) := by
  simp only [tomoTopL, targets_eq]

/-- `tomoGoL` from its top `m` levels and the checks of the nodes they leave to `P`. -/
theorem tomoGoL_of_top {p : ℕ} {leaf : List (List ℤ) → Bool} {W : List (List ℤ)}
    {P : List (List (List ℤ))} :
    ∀ (m : ℕ) (R : List (List Row)) (cur : List (List ℤ)), tomoTopL p leaf W P m R cur = true →
      (∀ q ∈ P, tomoGoL p leaf W (R.drop m) q = true) → tomoGoL p leaf W R cur = true
  | 0, R, cur, h, hP => by
    simp only [tomoTopL, List.contains_iff_mem] at h
    simpa using hP cur h
  | _ + 1, [], cur, h, _ => by simpa only [tomoTopL, tomoGoL] using h
  | m + 1, rs :: rest, cur, h, hP => by
    rw [tomoTopL_cons, List.all_eq_true] at h
    rw [tomoGoL_cons, List.all_eq_true]
    intro y hy
    rcases Bool.or_eq_true _ _ ▸ h y hy with h1 | h1
    · simp [h1]
    · simp only [Bool.or_eq_true]
      exact Or.inr (tomoGoL_of_top m rest (y :: cur) h1 (by simpa using hP))

theorem tomoGoL_sound {p : ℕ} {leaf : List (List ℤ) → Bool} {W : List (List ℤ)} :
    ∀ (R : List (List Row)) (cur rest : List (List ℤ)), tomoGoL p leaf W R cur = true →
      rest.length = R.length → (∀ y ∈ rest, y ∈ W) →
      (∀ i < R.length, rowsHold p (R.getD i []) ((rest.take (i + 1)).reverse ++ cur) = true) →
      leaf (cur.reverse ++ rest) = true → False
  | [], cur, rest, h, hlen, _, _, hleaf => by
    rw [List.length_nil, List.length_eq_zero_iff] at hlen
    subst hlen
    simp_all [tomoGoL]
  | rs :: R, cur, [], _, hlen, _, _, _ => by simp at hlen
  | rs :: R, cur, y :: rest, h, hlen, hW, hrows, hleaf => by
    rw [tomoGoL_cons, List.all_eq_true] at h
    have hy := h y (hW y List.mem_cons_self)
    have h0 := hrows 0 (by simp)
    simp only [List.getD_cons_zero, zero_add, List.take_succ_cons, List.take_zero,
      List.reverse_singleton, List.singleton_append] at h0
    rw [h0, Bool.not_true, Bool.false_or] at hy
    refine tomoGoL_sound R (y :: cur) rest hy (by simpa using hlen)
      (fun z hz => hW z (List.mem_cons_of_mem _ hz)) (fun i hi => ?_) ?_
    · have := hrows (i + 1) (by simp; omega)
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this
    · simpa [List.reverse_cons, List.append_assoc] using hleaf

/-- No choice of one vector of `W` per line with integral line sums passes `leaf` when the
certificate is sound and `tomoGoL` passes. -/
theorem no_choiceL {p : ℕ} (hp : 0 < p) {s : ℤ} {leaf : List (List ℤ) → Bool}
    {W : List (List ℤ)} {ws : List (List (List ℤ))} {R : List (List Row)}
    (hc : certOK p ws = true) (hR : certRows p s ws = R) (h : tomoGoL p leaf W R [] = true)
    (ys : List (List ℤ)) (hlen : ys.length = p + 1) (hW : ∀ y ∈ ys, y ∈ W)
    (hint : ∀ x < p * p, (lineSum p ys x - s) % (p : ℤ) = 0) (hleaf : leaf ys = true) :
    False := by
  simp only [certOK, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hwl, hwv⟩ := hc
  have hRl : R.length = p + 1 := by rw [← hR, certRows, List.length_map, List.length_range, hwl]
  refine tomoGoL_sound R [] ys h (by rw [hlen, hRl]) hW (fun i hi => ?_) (by simpa using hleaf)
  rw [List.append_nil]
  rw [hRl] at hi
  subst hR
  have hi' : i < ws.length := by omega
  rw [certRows, List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
    List.getElem_range]
  unfold rowsHold
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  have hv := List.all_eq_true.1 ((allTo_iff _ _).1 hwv i hi') w hw
  simpa using rowOf_holds hp hint (d := i) (by omega) (by omega) hv

end SignedDifferenceSets.Tomography
