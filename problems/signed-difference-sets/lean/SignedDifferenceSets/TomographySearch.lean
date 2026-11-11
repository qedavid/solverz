module

public import SignedDifferenceSets.VectorSearch

/-!
# Line tomography, the kernel's side (I23)

Numbers `x < p²` stand for `(x / p, x % p) ∈ ZMod p × ZMod p`; line `j ≤ p` sends `x` to
`lineIdx p j x` (`b` for `j = 0`, `a + (j − 1) b` otherwise), and for vectors `ys` on the lines
`lineSum p ys x = Σⱼ ysⱼ(lineⱼ x)`. `tomoGo` tries one vector of `W` per line, line by line,
pruned by certificate rows: a `w` on the numbers whose pushforwards to the later lines vanish
mod `p` gives `Σ_{j ≤ d} ⟨pushⱼ w, yⱼ⟩ ≡ s Σ w (mod p)` once every `lineSum − s` is divisible
by `p`; a leaf passes when every `lineSum − s` is `0` or `±p`. `no_choice`: a passing search
leaves no choice with such leaves. `inSearch`: `noVector`'s search whose leaves must be listed
(every vector meeting the demands with `|w₀|` largest is in the list).
-/

@[expose] public section

namespace SignedDifferenceSets.Tomography

/-! ### Lines and the search over them -/

/-- Line `j` on element numbers `x = a p + b`: `b` for `j = 0`, `a + (j − 1) b` otherwise. -/
def lineIdx (p : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x % p
  | j + 1, x => (x / p + j * (x % p)) % p

theorem lineIdx_lt {p : ℕ} (hp : 0 < p) (j x : ℕ) : lineIdx p j x < p := by
  cases j <;> exact Nat.mod_lt _ hp

/-- `Σⱼ ysⱼ(lineⱼ x)` over the lines `j ≤ p`. -/
def lineSum (p : ℕ) (ys : List (List ℤ)) (x : ℕ) : ℤ :=
  sumTo (fun j => (ys.getD j []).getD (lineIdx p j x) 0) (p + 1)

/-- `f` is `0` or `±p`. -/
def unitStep (p : ℕ) (f : ℤ) : Bool := f == 0 || f == (p : ℤ) || f == -(p : ℤ)

/-- Every `lineSum − s` is `0` or `±p`. -/
def leafSDS (p : ℕ) (s : ℤ) (ys : List (List ℤ)) : Bool :=
  allTo (fun x => unitStep p (lineSum p ys x - s)) (p * p)

/-- `acc` with `v` added at position `i`. -/
def addAt : ℕ → ℤ → List ℤ → List ℤ
  | _, _, [] => []
  | 0, v, a :: acc => (a + v) :: acc
  | i + 1, v, a :: acc => a :: addAt i v acc

/-- `acc` plus line `j`'s coset sums of `w`, read from the element number `x` on. -/
def pushFrom (p j : ℕ) : ℕ → List ℤ → List ℤ → List ℤ
  | _, [], acc => acc
  | x, v :: w, acc => pushFrom p j (x + 1) w (addAt (lineIdx p j x) v acc)

/-- Line `j`'s coset sums of `w` (a vector on the element numbers), in one pass. -/
def push (p j : ℕ) (w : List ℤ) : List ℤ := pushFrom p j 0 w (List.replicate p 0)

/-- `Σ_{t < p} P_t y_t`. -/
def dot (p : ℕ) (P y : List ℤ) : ℤ := sumTo (fun t => P.getD t 0 * y.getD t 0) p

/-- `Σᵢ ⟨Psᵢ, ysᵢ⟩` over the common length. -/
def rowSum (p : ℕ) : List (List ℤ) → List (List ℤ) → ℤ
  | P :: Ps, y :: ys => dot p P y + rowSum p Ps ys
  | _, _ => 0

/-- A certificate row at depth `d`: line `d, d − 1, …, 0`'s pushforwards mod `p`, and the
target `s Σ w` mod `p`. -/
abbrev Row := List (List ℤ) × ℤ

/-- The row of `w` at depth `d`. -/
def rowOf (p : ℕ) (s : ℤ) (d : ℕ) (w : List ℤ) : Row :=
  ((List.range (d + 1)).reverse.map fun j => (push p j w).map (· % (p : ℤ)),
    s * sumTo (fun x => w.getD x 0) (p * p) % p)

/-- `w`'s pushforwards to the lines after `d` vanish mod `p`. -/
def vanishes (p d : ℕ) (w : List ℤ) : Bool :=
  w.length == p * p &&
    allTo (fun j => decide (j ≤ d) || (push p j w).all fun v => v % (p : ℤ) == 0) (p + 1)

/-- The rows of the certificate `ws` (`ws[d]`: the vectors `w` at depth `d`). -/
def certRows (p : ℕ) (s : ℤ) (ws : List (List (List ℤ))) : List (List Row) :=
  (List.range ws.length).map fun d => (ws.getD d []).map (rowOf p s d)

/-- `ws` has a level per line and its vectors vanish after their depth. -/
def certOK (p : ℕ) (ws : List (List (List ℤ))) : Bool :=
  ws.length == p + 1 && allTo (fun d => (ws.getD d []).all (vanishes p d)) ws.length

/-- The rows `rs` hold for the chosen vectors `y :: cur` (newest first). -/
def rowsHold (p : ℕ) (rs : List Row) (cur : List (List ℤ)) : Bool :=
  rs.all fun r => (rowSum p r.1 cur - r.2) % (p : ℤ) == 0

/-- No completion of the chosen vectors `cur` (newest first) by one vector of `W` per level of
`R` passes the rows and the leaf. Each level's targets are computed once per node. -/
def tomoGo (p : ℕ) (s : ℤ) (W : List (List ℤ)) : List (List Row) → List (List ℤ) → Bool
  | [], cur => !leafSDS p s cur.reverse
  | rs :: rest, cur =>
    let tg := rs.map fun r => (r.1.headD [], r.2 - rowSum p r.1.tail cur)
    W.all fun y => !(tg.all fun q => (dot p q.1 y - q.2) % (p : ℤ) == 0) ||
      tomoGo p s W rest (y :: cur)

/-- `tomoGo`'s top `m` levels; a node `m` levels down is left to the list `P`. -/
def tomoTop (p : ℕ) (s : ℤ) (W : List (List ℤ)) (P : List (List (List ℤ))) :
    ℕ → List (List Row) → List (List ℤ) → Bool
  | 0, _, cur => P.contains cur
  | _ + 1, [], cur => !leafSDS p s cur.reverse
  | m + 1, rs :: rest, cur =>
    let tg := rs.map fun r => (r.1.headD [], r.2 - rowSum p r.1.tail cur)
    W.all fun y => !(tg.all fun q => (dot p q.1 y - q.2) % (p : ℤ) == 0) ||
      tomoTop p s W P m rest (y :: cur)

theorem targets_eq (p : ℕ) (rs : List Row) (y : List ℤ) (cur : List (List ℤ)) :
    ((rs.map fun r => (r.1.headD [], r.2 - rowSum p r.1.tail cur)).all
      fun q => (dot p q.1 y - q.2) % (p : ℤ) == 0) = rowsHold p rs (y :: cur) := by
  unfold rowsHold
  rw [List.all_map]
  refine List.all_congr rfl fun r => ?_
  rcases r with ⟨_ | ⟨P, Ps⟩, t⟩
  · simp [rowSum, dot, sumTo_eq]
  · simp only [Function.comp, List.headD_cons, List.tail_cons, rowSum]
    congr 2
    ring

theorem tomoGo_cons (p : ℕ) (s : ℤ) (W : List (List ℤ)) (rs : List Row)
    (rest : List (List Row)) (cur : List (List ℤ)) :
    tomoGo p s W (rs :: rest) cur =
      W.all fun y => !rowsHold p rs (y :: cur) || tomoGo p s W rest (y :: cur) := by
  simp only [tomoGo, targets_eq]

theorem tomoTop_cons (p : ℕ) (s : ℤ) (W : List (List ℤ)) (P : List (List (List ℤ))) (m : ℕ)
    (rs : List Row) (rest : List (List Row)) (cur : List (List ℤ)) :
    tomoTop p s W P (m + 1) (rs :: rest) cur =
      W.all fun y => !rowsHold p rs (y :: cur) || tomoTop p s W P m rest (y :: cur) := by
  simp only [tomoTop, targets_eq]

/-- `tomoGo` from its top `m` levels and the checks of the nodes they leave to `P`. -/
theorem tomoGo_of_top {p : ℕ} {s : ℤ} {W : List (List ℤ)} {P : List (List (List ℤ))} :
    ∀ (m : ℕ) (R : List (List Row)) (cur : List (List ℤ)), tomoTop p s W P m R cur = true →
      (∀ q ∈ P, tomoGo p s W (R.drop m) q = true) → tomoGo p s W R cur = true
  | 0, R, cur, h, hP => by
    simp only [tomoTop, List.contains_iff_mem] at h
    simpa using hP cur h
  | _ + 1, [], cur, h, _ => by simpa only [tomoTop, tomoGo] using h
  | m + 1, rs :: rest, cur, h, hP => by
    rw [tomoTop_cons, List.all_eq_true] at h
    rw [tomoGo_cons, List.all_eq_true]
    intro y hy
    rcases Bool.or_eq_true _ _ ▸ h y hy with h1 | h1
    · simp [h1]
    · simp only [Bool.or_eq_true]
      exact Or.inr (tomoGo_of_top m rest (y :: cur) h1 (by simpa using hP))

/-- A passing `tomoGo` leaves no completion `rest` from `W` whose rows hold and whose leaf
passes. -/
theorem tomoGo_sound {p : ℕ} {s : ℤ} {W : List (List ℤ)} :
    ∀ (R : List (List Row)) (cur rest : List (List ℤ)), tomoGo p s W R cur = true →
      rest.length = R.length → (∀ y ∈ rest, y ∈ W) →
      (∀ i < R.length, rowsHold p (R.getD i []) ((rest.take (i + 1)).reverse ++ cur) = true) →
      leafSDS p s (cur.reverse ++ rest) = true → False
  | [], cur, rest, h, hlen, _, _, hleaf => by
    rw [List.length_nil, List.length_eq_zero_iff] at hlen
    subst hlen
    simp_all [tomoGo]
  | rs :: R, cur, [], _, hlen, _, _, _ => by simp at hlen
  | rs :: R, cur, y :: rest, h, hlen, hW, hrows, hleaf => by
    rw [tomoGo_cons, List.all_eq_true] at h
    have hy := h y (hW y List.mem_cons_self)
    have h0 := hrows 0 (by simp)
    simp only [List.getD_cons_zero, zero_add, List.take_succ_cons, List.take_zero,
      List.reverse_singleton, List.singleton_append] at h0
    rw [h0, Bool.not_true, Bool.false_or] at hy
    refine tomoGo_sound R (y :: cur) rest hy (by simpa using hlen)
      (fun z hz => hW z (List.mem_cons_of_mem _ hz)) (fun i hi => ?_) ?_
    · have := hrows (i + 1) (by simp; omega)
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this
    · simpa [List.reverse_cons, List.append_assoc] using hleaf

/-! ### Why the rows hold -/

theorem length_addAt : ∀ (i : ℕ) (v : ℤ) (acc : List ℤ), (addAt i v acc).length = acc.length
  | 0, _, [] => rfl
  | _ + 1, _, [] => rfl
  | 0, _, _ :: _ => rfl
  | i + 1, v, _ :: acc => by simp [addAt, length_addAt i v acc]

theorem getD_addAt : ∀ (i : ℕ) (v : ℤ) (acc : List ℤ) (t : ℕ), t < acc.length →
    (addAt i v acc).getD t 0 = acc.getD t 0 + if i = t then v else 0
  | _, _, [], t, h => by simp at h
  | 0, v, a :: acc, 0, _ => by simp [addAt]
  | 0, v, a :: acc, t + 1, _ => by simp [addAt]
  | i + 1, v, a :: acc, 0, _ => by simp [addAt]
  | i + 1, v, a :: acc, t + 1, h => by
    simp only [addAt, List.getD_cons_succ]
    rw [getD_addAt i v acc t (by simpa using h)]
    simp

theorem length_pushFrom (p j : ℕ) :
    ∀ (x : ℕ) (w acc : List ℤ), (pushFrom p j x w acc).length = acc.length
  | _, [], _ => rfl
  | x, v :: w, acc => by rw [pushFrom, length_pushFrom p j (x + 1) w, length_addAt]

theorem getD_pushFrom (p j : ℕ) : ∀ (x : ℕ) (w acc : List ℤ) (t : ℕ), t < acc.length →
    (pushFrom p j x w acc).getD t 0 = acc.getD t 0 +
      ∑ i ∈ Finset.range w.length, if lineIdx p j (x + i) = t then w.getD i 0 else 0
  | x, [], acc, t, _ => by simp [pushFrom]
  | x, v :: w, acc, t, h => by
    rw [pushFrom, getD_pushFrom p j (x + 1) w _ t (by rwa [length_addAt]), getD_addAt _ _ _ _ h,
      List.length_cons, Finset.sum_range_succ']
    have e (i : ℕ) : x + 1 + i = x + (i + 1) := by omega
    simp only [e, add_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem length_push (p j : ℕ) (w : List ℤ) : (push p j w).length = p := by
  rw [push, length_pushFrom, List.length_replicate]

theorem getD_push {p : ℕ} (j : ℕ) (w : List ℤ) {t : ℕ} (ht : t < p) :
    (push p j w).getD t 0 =
      ∑ i ∈ Finset.range w.length, if lineIdx p j i = t then w.getD i 0 else 0 := by
  rw [push, getD_pushFrom p j 0 w _ t (by simpa using ht)]
  simp [List.getD_eq_getElem?_getD, ht]

theorem getD_map_emod (l : List ℤ) (t : ℕ) (q : ℤ) :
    (l.map (· % q)).getD t 0 = l.getD t 0 % q := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[t]? <;> simp

theorem getD_map_range (f : ℕ → ℤ) {n t : ℕ} (ht : t < n) :
    ((List.range n).map f).getD t 0 = f t := by
  simp [List.getD_eq_getElem?_getD, ht]

theorem sum_map_range (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

/-- `Σₓ wₓ · lineSum x` collects line by line into the pushforwards. -/
theorem sum_mul_lineSum {p : ℕ} (hp : 0 < p) (ys : List (List ℤ)) {w : List ℤ}
    (hw : w.length = p * p) :
    ∑ x ∈ Finset.range (p * p), w.getD x 0 * lineSum p ys x =
      ∑ j ∈ Finset.range (p + 1), ∑ t ∈ Finset.range p,
        (push p j w).getD t 0 * (ys.getD j []).getD t 0 := by
  simp only [lineSum, sumTo_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx (x : ℕ) : w.getD x 0 * (ys.getD j []).getD (lineIdx p j x) 0 =
      ∑ t ∈ Finset.range p, if lineIdx p j x = t then
        w.getD x 0 * (ys.getD j []).getD t 0 else 0 := by
    rw [Finset.sum_ite_eq]
    simp [lineIdx_lt hp j x]
  simp only [hx]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [getD_push _ _ (Finset.mem_range.1 ht), hw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem rowSum_map (p : ℕ) (g h : ℕ → List ℤ) :
    ∀ l : List ℕ, rowSum p (l.map g) (l.map h) = (l.map fun j => dot p (g j) (h j)).sum
  | [] => by simp [rowSum]
  | j :: l => by simp [rowSum, rowSum_map p g h l]

theorem take_eq_map {α : Type*} (ys : List (List α)) {n : ℕ} (hn : n ≤ ys.length) :
    ys.take n = (List.range n).map fun j => ys.getD j [] := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.getElem_take, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem]

theorem dvd_of_emod {p : ℕ} {z : ℤ} (h : z % (p : ℤ) = 0) : ((z : ℤ) : ZMod p) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd z p).2 (Int.dvd_of_emod_eq_zero h)

/-- A row of a vanishing `w` holds once every `lineSum − s` is divisible by `p`. -/
theorem rowOf_holds {p : ℕ} (hp : 0 < p) {s : ℤ} {ys : List (List ℤ)}
    (hint : ∀ x < p * p, (lineSum p ys x - s) % (p : ℤ) = 0) {d : ℕ} (hd : d + 1 ≤ ys.length)
    (hdp : d ≤ p) {w : List ℤ} (hv : vanishes p d w = true) :
    (rowSum p (rowOf p s d w).1 (ys.take (d + 1)).reverse - (rowOf p s d w).2) % (p : ℤ) = 0 := by
  have e1 : rowSum p (rowOf p s d w).1 (ys.take (d + 1)).reverse =
      ∑ j ∈ Finset.range (d + 1), dot p ((push p j w).map (· % (p : ℤ))) (ys.getD j []) := by
    rw [take_eq_map ys hd, ← List.map_reverse, rowOf, rowSum_map, List.map_reverse,
      List.sum_reverse, sum_map_range]
  rw [e1]
  simp only [rowOf]
  refine Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_)
  simp only [vanishes, Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨hwl, hv⟩ := hv
  have hsum := sum_mul_lineSum hp ys hwl
  have hcast : (∑ x ∈ Finset.range (p * p), w.getD x 0 * lineSum p ys x : ZMod p) =
      (s : ZMod p) * ∑ x ∈ Finset.range (p * p), (w.getD x 0 : ZMod p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := dvd_of_emod (hint x (Finset.mem_range.1 hx))
    push_cast at this
    rw [sub_eq_zero.1 this, mul_comm]
  have hv' : ∀ j ∈ Finset.range (p + 1), d < j → ∀ t ∈ Finset.range p,
      ((push p j w).getD t 0 : ZMod p) = 0 := by
    intro j hj hdj t ht
    have := (allTo_iff _ _).1 hv j (Finset.mem_range.1 hj)
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_le.2 hdj, false_or, List.all_eq_true,
      beq_iff_eq] at this
    have ht' : t < (push p j w).length := by rw [length_push]; exact Finset.mem_range.1 ht
    rw [List.getD_eq_getElem _ _ ht']
    exact dvd_of_emod (this _ (List.getElem_mem _))
  have hsplit : (∑ j ∈ Finset.range (p + 1), ∑ t ∈ Finset.range p,
      (push p j w).getD t 0 * (ys.getD j []).getD t 0 : ZMod p) =
      ∑ j ∈ Finset.range (d + 1), ∑ t ∈ Finset.range p,
        ((push p j w).getD t 0 : ZMod p) * (ys.getD j []).getD t 0 := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : d + 1 ≤ p + 1), add_eq_left]
    refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun t ht => ?_
    have hj' := Finset.mem_Ico.1 hj
    rw [hv' j (Finset.mem_range.2 hj'.2) (by omega) t ht, zero_mul]
  have hcast' := congrArg (Int.cast : ℤ → ZMod p) hsum
  push_cast at hcast'
  rw [hcast, hsplit] at hcast'
  have hmod (j t : ℕ) : (((push p j w).map (· % (p : ℤ))).getD t 0 : ZMod p) =
      ((push p j w).getD t 0 : ZMod p) := by
    rw [getD_map_emod, ZMod.intCast_mod]
  have hA : ((∑ j ∈ Finset.range (d + 1),
      dot p ((push p j w).map (· % (p : ℤ))) (ys.getD j []) : ℤ) : ZMod p) =
      ∑ j ∈ Finset.range (d + 1), ∑ t ∈ Finset.range p,
        ((push p j w).getD t 0 : ZMod p) * (ys.getD j []).getD t 0 := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dot, sumTo_eq]
    push_cast
    exact Finset.sum_congr rfl fun t _ => by rw [hmod j t]
  have hB : ((s * sumTo (fun x => w.getD x 0) (p * p) % p : ℤ) : ZMod p) =
      (s : ZMod p) * ∑ x ∈ Finset.range (p * p), (w.getD x 0 : ZMod p) := by
    rw [ZMod.intCast_mod, sumTo_eq]
    push_cast
    rfl
  rw [Int.cast_sub, hA, hB, hcast', sub_self]

theorem emod_of_unitStep {p : ℕ} {f : ℤ} (h : unitStep p f = true) : f % (p : ℤ) = 0 := by
  simp only [unitStep, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl <;> simp

/-- No choice of one vector of `W` per line passes the leaf when the certificate is sound and
`tomoGo` passes. -/
theorem no_choice {p : ℕ} (hp : 0 < p) {s : ℤ} {W : List (List ℤ)}
    {ws : List (List (List ℤ))} {R : List (List Row)} (hc : certOK p ws = true)
    (hR : certRows p s ws = R) (h : tomoGo p s W R [] = true) (ys : List (List ℤ))
    (hlen : ys.length = p + 1) (hW : ∀ y ∈ ys, y ∈ W) (hleaf : leafSDS p s ys = true) :
    False := by
  simp only [certOK, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hwl, hwv⟩ := hc
  have hRl : R.length = p + 1 := by rw [← hR, certRows, List.length_map, List.length_range, hwl]
  have hint : ∀ x < p * p, (lineSum p ys x - s) % (p : ℤ) = 0 := fun x hx =>
    emod_of_unitStep ((allTo_iff _ _).1 hleaf x hx)
  refine tomoGo_sound R [] ys h (by rw [hlen, hRl]) hW (fun i hi => ?_) (by simpa using hleaf)
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

/-! ### Listing the vectors that meet the demands -/

/-- `go` (VectorSearch) whose leaves pass when the vector is in `V`. -/
def goIn (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s top : ℤ) (V : List (List ℤ)) :
    ℕ → List ℤ → ℤ → ℤ → ℤ → Bool
  | 0, pre, sum, sq, abs => !leafOK n add Q t k s pre.reverse sum sq abs || V.contains pre.reverse
  | rem + 1, pre, sum, sq, abs =>
    cut c Q s (rem + 1) sum sq ||
      allRange (fun x => decide (Q - sq < x * x) ||
        goIn n add c Q t k s top V rem (x :: pre) (sum + x) (sq + x * x) (abs + |x|))
        (-top) (2 * top + 1).toNat

/-- The search's first coordinates `lo, …, lo + m − 1` (`|w₀|` bounds the rest). -/
def inPart (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (V : List (List ℤ)) (lo : ℤ) (m : ℕ) :
    Bool :=
  allRange (fun x => decide (Q < x * x) ||
    goIn n add c Q t k s |x| V (n - 1) [x] x (x * x) |x|) lo m

/-- Every vector meeting the demands with `|w₀|` largest is in `V`. -/
def inSearch (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (V : List (List ℤ)) : Bool :=
  cut c Q s n 0 0 || inPart n add c Q t k s V (-c) (2 * c + 1).toNat

theorem allRange_add (f : ℤ → Bool) (lo : ℤ) (m₁ m₂ : ℕ) :
    allRange f lo (m₁ + m₂) = (allRange f lo m₁ && allRange f (lo + m₁) m₂) := by
  induction m₁ generalizing lo with
  | zero => simp [allRange]
  | succ m ih =>
    rw [Nat.succ_add, allRange, allRange, ih, Bool.and_assoc]
    congr 3
    push_cast
    ring

/-- `inPart` over `m₁ + m₂` coordinates from its two halves. -/
theorem inPart_add {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {V : List (List ℤ)} {lo : ℤ}
    {m₁ m₂ : ℕ} (h₁ : inPart n add c Q t k s V lo m₁ = true)
    (h₂ : inPart n add c Q t k s V (lo + m₁) m₂ = true) :
    inPart n add c Q t k s V lo (m₁ + m₂) = true := by
  rw [inPart, allRange_add]
  exact Bool.and_eq_true_iff.2 ⟨h₁, h₂⟩

theorem goIn_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s top : ℤ} {V : List (List ℤ)} :
    ∀ (w pre : List ℤ) (sum sq abs : ℤ),
      goIn n add c Q t k s top V w.length pre sum sq abs = true →
      (∀ y ∈ w, |y| ≤ top) → (∀ y ∈ w, |y| ≤ c) →
      sum + w.sum = s → sq + sqSum w = Q → abs + absSum w ≤ k →
      (k - (abs + absSum w)) % 2 = 0 → shiftsOK n add t (pre.reverse ++ w) = true →
      pre.reverse ++ w ∈ V
  | [], pre, sum, sq, abs, h, _, _, hs, hq, ha, hp, hw => by
    simp only [List.sum_nil, add_zero, sqSum, absSum, List.map_nil, List.append_nil] at *
    simpa [goIn, leafOK, hs, hq, ha, hp, hw] using h
  | x :: w, pre, sum, sq, abs, h, ht, hc, hs, hq, ha, hp, hw => by
    have hcut := cut_false (x :: w) hc hs hq
    simp only [List.length_cons, goIn] at h
    rw [List.length_cons] at hcut
    rw [hcut, Bool.false_or] at h
    simp only [List.mem_cons, forall_eq_or_imp] at ht hc
    have hx := allRange_abs h ht.1
    simp only [sqSum, absSum, List.map_cons, List.sum_cons] at hs hq ha hp
    have hsq : ¬ Q - sq < x * x := by have := sqSum_nonneg w; simp only [sqSum] at this; linarith
    simp only [hsq, decide_false, Bool.false_or] at hx
    have := goIn_sound w (x :: pre) (sum + x) (sq + x * x) (abs + |x|) hx ht.2 hc.2
      (by linarith) (by simp only [sqSum]; linarith) (by simp only [absSum]; linarith)
      (by simp only [absSum]; rw [show abs + |x| + absSum w = abs + (|x| + absSum w) by ring]
          exact hp)
      (by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hw)
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using this

/-- `inSearch` lists every vector meeting the demands with `|x|` largest. -/
theorem inSearch_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {V : List (List ℤ)}
    (h : inSearch n add c Q t k s V = true) (x : ℤ) (w : List ℤ) (hn : (x :: w).length = n)
    (hx : |x| ≤ c) (htop : ∀ y ∈ w, |y| ≤ |x|) (hc : ∀ y ∈ w, |y| ≤ c)
    (hs : (x :: w).sum = s) (hq : sqSum (x :: w) = Q) (ha : absSum (x :: w) ≤ k)
    (hp : (k - absSum (x :: w)) % 2 = 0) (hw : shiftsOK n add t (x :: w) = true) :
    x :: w ∈ V := by
  have hcall : ∀ y ∈ x :: w, |y| ≤ c := by
    simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨hx, hc⟩
  have hcut := cut_false (sum := 0) (sq := 0) (x :: w) hcall (by simpa using hs)
    (by simpa using hq)
  rw [hn] at hcut
  rw [inSearch, hcut, Bool.false_or, inPart] at h
  have hr := allRange_abs h hx
  simp only [sqSum, absSum, List.map_cons, List.sum_cons] at hs hq ha hp
  have hsq : ¬ Q < x * x := by have := sqSum_nonneg w; simp only [sqSum] at this; linarith
  simp only [hsq, decide_false, Bool.false_or] at hr
  have hlen : n - 1 = w.length := by simp at hn; omega
  rw [hlen] at hr
  simpa using goIn_sound w [x] x (x * x) |x| hr htop hc (by linarith)
    (by simp only [sqSum]; linarith) (by simp only [absSum]; linarith)
    (by simp only [absSum]; exact hp) (by simpa using hw)

end SignedDifferenceSets.Tomography
