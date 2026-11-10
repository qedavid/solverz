module

public import SignedDifferenceSets.LiftSearch

/-!
# A sign vector with given autocorrelation, searched position by position (C17x)

`go` assigns `f` in the order of its steps, each position from a list of codes (`1` for `+1`, `2`
for `−1`, `0`). It keeps `f` on the assigned positions `A` in masks `P`, `M`, for each shift `g` of
a list `gs` the sum `off + Σ F(y) F(y + g)` of the assigned part `F` (`off ≥ v` keeps it in `ℕ`),
the number `r` of nonzero values still to place, and candidate coset-sum vectors. A nonzero value
is cut when a shift's sum is further than `2r` from `L = off + λ` (each nonzero value still to
place moves it by at most `2`); a value is cut when fewer positions than `r` are left, or when the
position's coset, all assigned or known zero (mask `F`), has a sum no candidate has there. A zero
value changes no sum, so it skips that work. A complete assignment goes to `leaf`. Everything the
kernel evaluates is written with recursors (`List.rec`, `Bool.rec`), which it reduces directly.
`go_sound`: if `go` passes, every `f` meeting the demands reaches `leaf` with masks of `f`, and
`leaf` passes them. `go_of_front`: `go` passes if it passes from every node of a `front`.
-/

@[expose] public section

namespace SignedDifferenceSets.PairSearch

open LiftSearch

/-- One position of the order: its number, its partners `(x + g, x − g)` for every shift `g`
checked, the elements of its coset and the coset's number. -/
structure Step where
  /-- The position. -/
  x : ℕ
  /-- Per shift `g`, the partners `x + g` and `x − g`. -/
  nb : List (ℕ × ℕ)
  /-- The elements of its coset. -/
  cs : List ℕ
  /-- The coset's number. -/
  b : ℕ

/-- The step of position `x`: partners on `0, …, v − 1` for the shifts `gs`, coset `cos (q x)`. -/
def mkStep (v : ℕ) (add : ℕ → ℕ → ℕ) (gs : List ℕ) (q : ℕ → ℕ) (cos : ℕ → List ℕ) (x : ℕ) :
    Step :=
  ⟨x, gs.map fun g => (add x g, add x (negN v add g)), cos (q x), q x⟩

/-- `l.all p`, by the recursor. -/
noncomputable def allR {α : Type} (p : α → Bool) (l : List α) : Bool :=
  @List.rec α (fun _ => Bool) true (fun a _ ih => @Bool.rec (fun _ => Bool) false ih (p a)) l

/-- Each shift's sum after the step's position gets a nonzero value: its partners marked in `A`
(the value's sign) add, those marked in `B` (the other sign) subtract. -/
noncomputable def updR (A B : ℕ) (nb : List (ℕ × ℕ)) : List ℕ → List ℕ :=
  @List.rec (ℕ × ℕ) (fun _ => List ℕ → List ℕ) (fun _ => [])
    (fun yw _ ih acc => @List.rec ℕ (fun _ => List ℕ) []
      (fun c acc' _ => @Prod.rec ℕ ℕ (fun _ => List ℕ)
        (fun y w => Nat.sub (Nat.add (Nat.add c (bit A y)) (bit A w))
          (Nat.add (bit B y) (bit B w)) :: ih acc') yw) acc) nb

/-- Every sum lies in `[lo, hi]`. -/
noncomputable def nearR (lo hi : ℕ) (acc : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) true
    (fun c _ ih => @Bool.rec (fun _ => Bool) false
      (@Bool.rec (fun _ => Bool) false ih (Nat.ble c hi)) (Nat.ble lo c)) acc

/-- The sums after the step's position gets code `u` (`1` or `2`). -/
noncomputable def accU (st : Step) (P M u : ℕ) (acc : List ℕ) : List ℕ :=
  updR (bif Nat.beq u 1 then P else M) (bif Nat.beq u 1 then M else P) st.nb acc

/-- Position `y` is assigned (`A`) or known zero (`F`). -/
def settled (A F y : ℕ) : Bool := Nat.beq (bit A y) 1 || Nat.beq (bit F y) 1

/-- The plus mask after position `x` gets code `u`. -/
def nextP (P x u : ℕ) : ℕ := bif Nat.beq u 1 then Nat.lor P (2 ^ x) else P

/-- The minus mask after position `x` gets code `u`. -/
def nextM (M x u : ℕ) : ℕ := bif Nat.beq u 2 then Nat.lor M (2 ^ x) else M

/-- How many of the positions `ys` the mask `P` marks. -/
def cnt (P : ℕ) : List ℕ → ℕ
  | [] => 0
  | y :: ys => Nat.add (bit P y) (cnt P ys)

/-- The candidates after the step: if its coset is settled, those whose entry there, less `3`, is
its sum. -/
def nextCand (st : Step) (A F P M : ℕ) (cand : List (List ℕ)) : List (List ℕ) :=
  bif st.cs.all (settled A F) then
    cand.filter fun c => Nat.beq (Nat.add (c.getD st.b 0) (cnt M st.cs)) (Nat.add 3 (cnt P st.cs))
  else cand

/-- A nonzero code `u` is cut: none left to place, too few positions left (`n`), a sum out of
reach, or no candidate left. -/
noncomputable def cutNZ (L F n : ℕ) (st : Step) (P M A : ℕ) (acc : List ℕ) (r : ℕ)
    (cand : List (List ℕ)) (u : ℕ) : Bool :=
  Nat.beq r 0 || Nat.blt n (Nat.sub r 1) ||
    !nearR (Nat.sub L (Nat.mul 2 (Nat.sub r 1))) (Nat.add L (Nat.mul 2 (Nat.sub r 1)))
      (accU st P M u acc) ||
    (nextCand st (Nat.lor A (2 ^ st.x)) F (nextP P st.x u) (nextM M st.x u) cand).isEmpty

/-- The code `0` is cut: too few positions left (`n`), or no candidate left. -/
def cutZ (F n : ℕ) (st : Step) (P M A r : ℕ) (cand : List (List ℕ)) : Bool :=
  Nat.blt n r || (nextCand st (Nat.lor A (2 ^ st.x)) F P M cand).isEmpty

/-- Code `u` at step `st`: `z` when it is cut, else `k` at the next state. -/
noncomputable def tryU {β : Type} (z : β) (L F n : ℕ) (st : Step) (P M A : ℕ) (acc : List ℕ)
    (r : ℕ) (cand : List (List ℕ)) (k : ℕ → ℕ → ℕ → List ℕ → ℕ → List (List ℕ) → β) (u : ℕ) :
    β :=
  @Bool.rec (fun _ => β)
    (@Bool.rec (fun _ => β)
      (k (nextP P st.x u) (nextM M st.x u) (Nat.lor A (2 ^ st.x)) (accU st P M u acc)
        (Nat.sub r 1)
        (nextCand st (Nat.lor A (2 ^ st.x)) F (nextP P st.x u) (nextM M st.x u) cand)) z
      (cutNZ L F n st P M A acc r cand u))
    (@Bool.rec (fun _ => β)
      (k P M (Nat.lor A (2 ^ st.x)) acc r (nextCand st (Nat.lor A (2 ^ st.x)) F P M cand)) z
      (cutZ F n st P M A r cand))
    (Nat.beq u 0)

/-- The search over the steps `sts` from masks `P`, `M`, assigned positions `A`, shift sums
`acc`, `r` nonzero values to place and candidates `cand` (entries `3` above the coset sums), all in
`ℕ`: `true` when every assignment is cut or passes `leaf`. -/
noncomputable def go (L : ℕ) (vals : List ℕ) (F : ℕ) (leaf : ℕ → ℕ → Bool) (sts : List Step) :
    ℕ → ℕ → ℕ → List ℕ → ℕ → List (List ℕ) → Bool :=
  @List.rec Step (fun _ => ℕ → ℕ → ℕ → List ℕ → ℕ → List (List ℕ) → Bool)
    (fun P M _ _ r _ => !Nat.beq r 0 || leaf P M)
    (fun st sts ih P M A acc r cand =>
      allR (tryU true L F sts.length st P M A acc r cand ih) vals) sts

theorem go_cons (L : ℕ) (vals : List ℕ) (F : ℕ) (leaf : ℕ → ℕ → Bool) (st : Step)
    (sts : List Step) (P M A : ℕ) (acc : List ℕ) (r : ℕ) (cand : List (List ℕ)) :
    go L vals F leaf (st :: sts) P M A acc r cand =
      allR (tryU true L F sts.length st P M A acc r cand (go L vals F leaf sts)) vals := rfl

/-! ### The kernel's functions, by their equations -/

theorem allR_eq {α : Type} (p : α → Bool) : ∀ l : List α, allR p l = l.all p
  | [] => rfl
  | a :: l => by
    change @Bool.rec (fun _ => Bool) false (allR p l) (p a) = (a :: l).all p
    rw [List.all_cons, allR_eq p l]
    cases p a <;> rfl

theorem updR_cons (A B : ℕ) (yw : ℕ × ℕ) (nb : List (ℕ × ℕ)) (c : ℕ) (acc : List ℕ) :
    updR A B (yw :: nb) (c :: acc) = Nat.sub (Nat.add (Nat.add c (bit A yw.1)) (bit A yw.2))
      (Nat.add (bit B yw.1) (bit B yw.2)) :: updR A B nb acc := rfl

theorem length_updR (A B : ℕ) : ∀ (nb : List (ℕ × ℕ)) (acc : List ℕ),
    (updR A B nb acc).length = min nb.length acc.length
  | [], _ => by simp [updR]
  | _ :: _, [] => by simp [updR]
  | yw :: nb, c :: acc => by
    rw [updR_cons, List.length_cons, length_updR A B nb acc]
    simp [Nat.succ_min_succ]

theorem updR_getD (A B : ℕ) : ∀ (nb : List (ℕ × ℕ)) (acc : List ℕ) (i : ℕ),
    i < nb.length → i < acc.length →
      (updR A B nb acc).getD i 0 = Nat.sub (Nat.add (Nat.add (acc.getD i 0)
        (bit A (nb.getD i (0, 0)).1)) (bit A (nb.getD i (0, 0)).2))
        (Nat.add (bit B (nb.getD i (0, 0)).1) (bit B (nb.getD i (0, 0)).2))
  | [], _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)
  | yw :: nb, c :: acc, 0, _, _ => by
    rw [updR_cons]
    simp only [List.getD_cons_zero]
  | yw :: nb, c :: acc, i + 1, h1, h2 => by
    rw [updR_cons]
    simp only [List.getD_cons_succ]
    exact updR_getD A B nb acc i (by simpa using h1) (by simpa using h2)

theorem nearR_of {lo hi : ℕ} : ∀ acc : List ℕ,
    (∀ i, i < acc.length → lo ≤ acc.getD i 0 ∧ acc.getD i 0 ≤ hi) → nearR lo hi acc = true
  | [], _ => rfl
  | c :: acc, h => by
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    change @Bool.rec (fun _ => Bool) false
      (@Bool.rec (fun _ => Bool) false (nearR lo hi acc) (Nat.ble c hi)) (Nat.ble lo c) = true
    rw [Nat.ble_eq_true_of_le h0.1, Nat.ble_eq_true_of_le h0.2]
    exact nearR_of acc fun i hi' => by simpa using h (i + 1) (by simpa using hi')

theorem tryU_zero {β : Type} (z : β) (L F n : ℕ) (st : Step) (P M A : ℕ) (acc : List ℕ)
    (r : ℕ) (cand : List (List ℕ)) (k : ℕ → ℕ → ℕ → List ℕ → ℕ → List (List ℕ) → β) :
    tryU z L F n st P M A acc r cand k 0 = bif cutZ F n st P M A r cand then z else
      k P M (Nat.lor A (2 ^ st.x)) acc r (nextCand st (Nat.lor A (2 ^ st.x)) F P M cand) := by
  unfold tryU
  cases cutZ F n st P M A r cand <;> rfl

theorem tryU_nz {β : Type} (z : β) (L F n : ℕ) (st : Step) (P M A : ℕ) (acc : List ℕ)
    (r : ℕ) (cand : List (List ℕ)) (k : ℕ → ℕ → ℕ → List ℕ → ℕ → List (List ℕ) → β) {u : ℕ}
    (hu : Nat.beq u 0 = false) :
    tryU z L F n st P M A acc r cand k u = bif cutNZ L F n st P M A acc r cand u then z else
      k (nextP P st.x u) (nextM M st.x u) (Nat.lor A (2 ^ st.x)) (accU st P M u acc)
        (Nat.sub r 1)
        (nextCand st (Nat.lor A (2 ^ st.x)) F (nextP P st.x u) (nextM M st.x u) cand) := by
  unfold tryU
  rw [hu]
  cases cutNZ L F n st P M A acc r cand u <;> rfl

/-! ### Soundness -/

variable {v : ℕ} {add : ℕ → ℕ → ℕ}

/-- `f` on the positions `A` marks, `0` elsewhere. -/
def onA (A : ℕ) (f : ℕ → ℤ) (y : ℕ) : ℤ := if A.testBit y then f y else 0

/-- The masks `P`, `M` mark `f`'s `+1` and `−1` on `A`. -/
def EncA (A : ℕ) (f : ℕ → ℤ) (P M : ℕ) : Prop :=
  ∀ y, P.testBit y = (A.testBit y && decide (f y = 1)) ∧
    M.testBit y = (A.testBit y && decide (f y = -1))

/-- What the search assumes of `f`: signs, `0` from `v` on and where `F` marks, autocorrelation
`λ` at every shift `0 < g < v`. -/
structure Truth (v : ℕ) (add : ℕ → ℕ → ℕ) (lam : ℤ) (F : ℕ) (f : ℕ → ℤ) : Prop where
  out : ∀ y, v ≤ y → f y = 0
  sign : ∀ y, IsSign (f y)
  zero : ∀ y, F.testBit y = true → f y = 0
  corr : ∀ g, 0 < g → g < v → ∑ y ∈ Finset.range v, f y * f (add y g) = lam

/-- The state before the steps `sts`: masks of `f` on `A`, `off` plus the shift sums of `f` on `A`
for the shifts `gs`, `r` its nonzero values off `A`, the steps' positions new, distinct and holding
every nonzero value off `A`. -/
structure Inv (v : ℕ) (add : ℕ → ℕ → ℕ) (gs : List ℕ) (off : ℕ) (f : ℕ → ℤ) (sts : List Step)
    (P M A : ℕ) (acc : List ℕ) (r : ℕ) : Prop where
  enc : EncA A f P M
  len : acc.length = gs.length
  acc : ∀ i, i < gs.length → ((acc.getD i 0 : ℕ) : ℤ) =
    off + ∑ y ∈ Finset.range v, onA A f y * onA A f (add y (gs.getD i 0))
  rest : (r : ℤ) = ∑ y ∈ Finset.range v, if A.testBit y then 0 else f y * f y
  fresh : ∀ st ∈ sts, st.x < v ∧ A.testBit st.x = false
  nodup : (sts.map Step.x).Nodup
  cover : ∀ y, y < v → f y ≠ 0 → A.testBit y = true ∨ y ∈ sts.map Step.x

variable {f : ℕ → ℤ}

theorem getD_mem {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem valM_of_encA (hs : ∀ y, IsSign (f y)) {A P M : ℕ} (h : EncA A f P M) (y : ℕ) :
    valM P M y = onA A f y := by
  have hP := (h y).1
  have hM := (h y).2
  simp only [valM, bit_eq, hP, hM, onA]
  cases hA : A.testBit y
  · simp
  · rcases hs y with h1 | h1 | h1 <;> simp [h1]

theorem testBit_lor_two_pow (A x y : ℕ) :
    (Nat.lor A (2 ^ x)).testBit y = (A.testBit y || decide (y = x)) := by
  rw [show Nat.lor A (2 ^ x) = A ||| 2 ^ x from rfl, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h : y = x
  · subst h; simp
  · simp [h, Ne.symm h]

theorem encA_step {A P M x : ℕ} (h : EncA A f P M) :
    EncA (Nat.lor A (2 ^ x)) f (if f x = 1 then Nat.lor P (2 ^ x) else P)
      (if f x = -1 then Nat.lor M (2 ^ x) else M) := by
  intro y
  have hP := (h y).1
  have hM := (h y).2
  rw [testBit_lor_two_pow]
  constructor
  · split_ifs with h1
    · rw [testBit_lor_two_pow, hP]
      by_cases hy : y = x
      · subst hy; simp [h1]
      · simp [hy]
    · rw [hP]
      by_cases hy : y = x
      · subst hy; simp [h1]
      · simp [hy]
  · split_ifs with h1
    · rw [testBit_lor_two_pow, hM]
      by_cases hy : y = x
      · subst hy; simp [h1]
      · simp [hy]
    · rw [hM]
      by_cases hy : y = x
      · subst hy; simp [h1]
      · simp [hy]

theorem nextP_code {z : ℤ} (hz : IsSign z) (P x : ℕ) :
    nextP P x (code z) = if z = 1 then Nat.lor P (2 ^ x) else P := by
  rcases hz with rfl | rfl | rfl <;> rfl

theorem nextM_code {z : ℤ} (hz : IsSign z) (M x : ℕ) :
    nextM M x (code z) = if z = -1 then Nat.lor M (2 ^ x) else M := by
  rcases hz with rfl | rfl | rfl <;> rfl

/-- The masks `accU` reads, against the sign. -/
theorem orient_sub {z : ℤ} (hz : IsSign z) (h0 : z ≠ 0) (P M y : ℕ) :
    ((bit (bif Nat.beq (code z) 1 then P else M) y : ℕ) : ℤ) -
      (bit (bif Nat.beq (code z) 1 then M else P) y : ℕ) = z * valM P M y := by
  rcases hz with rfl | rfl | rfl
  · change ((bit P y : ℕ) : ℤ) - (bit M y : ℕ) = 1 * valM P M y
    simp [valM]
  · exact absurd rfl h0
  · change ((bit M y : ℕ) : ℤ) - (bit P y : ℕ) = -1 * valM P M y
    simp [valM]

theorem cnt_sub (P M : ℕ) : ∀ ys : List ℕ,
    ((cnt P ys : ℕ) : ℤ) - cnt M ys = (ys.map (valM P M)).sum
  | [] => by simp [cnt]
  | y :: ys => by
    simp only [cnt, Nat.add_eq, List.map_cons, List.sum_cons, valM]
    push_cast
    rw [← cnt_sub P M ys]
    ring

theorem add_ne_self (hG : NumGroup v add) {x g : ℕ} (hx : x < v) (hg : g < v) (h0 : 0 < g) :
    add x g ≠ x := by
  intro h
  obtain ⟨hn, hn0⟩ := hG.negN_spec hx
  have e1 : add (negN v add x) (add x g) = g := by
    rw [← hG.assoc _ _ _ hn hx hg, hn0, hG.comm 0 g hG.pos hg, hG.zero _ hg]
  have e2 : add (negN v add x) (add x g) = 0 := by rw [h, hn0]
  omega

/-- The shift sums after `x` gets `f x`, from those before. -/
theorem corr_step (hG : NumGroup v add) {A A' x g : ℕ}
    (hA' : ∀ y, A'.testBit y = (A.testBit y || decide (y = x))) (hx : x < v)
    (hA : A.testBit x = false) (hg : g < v) (h0 : 0 < g) :
    ∑ y ∈ Finset.range v, onA A' f y * onA A' f (add y g) =
      ∑ y ∈ Finset.range v, onA A f y * onA A f (add y g) +
        f x * (onA A f (add x g) + onA A f (add x (negN v add g))) := by
  rw [hG.corr_update hg (onA A f) (onA A' f)]
  congr 1
  have hd : ∀ y, onA A' f y - onA A f y = if y = x then f x else 0 := by
    intro y
    simp only [onA, hA']
    by_cases hy : y = x
    · subst hy; simp [hA]
    · simp [hy]
  have hxg : onA A' f (add x g) = onA A f (add x g) := by
    simp [onA, hA', add_ne_self hG hx hg h0]
  simp only [hd, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' _ _ _, ite_eq_left (Finset.mem_range.2 hx), hxg]

/-- A shift sum of signs on `0, …, v − 1` is at least `−v`. -/
theorem corr_ge (hs : ∀ y, IsSign (f y)) (A g : ℕ) :
    -(v : ℤ) ≤ ∑ y ∈ Finset.range v, onA A f y * onA A f (add y g) := by
  have hon : ∀ y, IsSign (onA A f y) := fun y => by
    unfold onA
    split_ifs
    · exact hs y
    · exact Or.inr (Or.inl rfl)
  have h1 : ∀ y, (-1 : ℤ) ≤ onA A f y * onA A f (add y g) := fun y => by
    rcases hon y with h | h | h <;> rcases hon (add y g) with h' | h' | h' <;> rw [h, h'] <;>
      norm_num
  calc -(v : ℤ) = ∑ _y ∈ Finset.range v, (-1 : ℤ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun y _ => h1 y

/-- The shift sums of `f` on `A` are within `2r` of `λ`, `r` the nonzero values off `A`. -/
theorem corr_close (hG : NumGroup v add) {lam : ℤ} {F : ℕ} (ht : Truth v add lam F f) (A : ℕ)
    {g : ℕ} (hg : g < v) (h0 : 0 < g) :
    |lam - ∑ y ∈ Finset.range v, onA A f y * onA A f (add y g)| ≤
      2 * ∑ y ∈ Finset.range v, if A.testBit y then 0 else f y * f y := by
  set E : ℕ → ℤ := fun y => if A.testBit y then 0 else f y
  have hfE : ∀ y, f y = onA A f y + E y := fun y => by
    simp only [onA, E]; split_ifs <;> ring
  have hEabs : ∀ y, |E y| = if A.testBit y then 0 else f y * f y := fun y => by
    simp only [E]
    split_ifs
    · simp
    · rcases ht.sign y with h | h | h <;> simp [h]
  have habs : ∀ y, |onA A f y| ≤ 1 := fun y => by
    simp only [onA]; split_ifs
    · rcases ht.sign y with h | h | h <;> simp [h]
    · simp
  have hfabs : ∀ y, |f y| ≤ 1 := fun y => by rcases ht.sign y with h | h | h <;> simp [h]
  have e : lam - ∑ y ∈ Finset.range v, onA A f y * onA A f (add y g) =
      ∑ y ∈ Finset.range v, E y * f (add y g) +
        ∑ y ∈ Finset.range v, onA A f y * E (add y g) := by
    rw [← ht.corr g h0 hg, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hfE y, hfE (add y g)]
    ring
  rw [e]
  have h1 : |∑ y ∈ Finset.range v, E y * f (add y g)| ≤ ∑ y ∈ Finset.range v, |E y| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hfabs _)
  have h2 : |∑ y ∈ Finset.range v, onA A f y * E (add y g)| ≤ ∑ y ∈ Finset.range v, |E y| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← hG.sum_shift hg (fun y => |E y|)]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (habs _)
  have h3 : ∑ y ∈ Finset.range v, |E y| =
      ∑ y ∈ Finset.range v, if A.testBit y then 0 else f y * f y :=
    Finset.sum_congr rfl fun y _ => hEabs y
  rw [two_mul, ← h3]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The soundness of `go`: a passing search, an `f` meeting the demands and the invariant give
masks of `f` that pass `leaf`. -/
theorem go_sound (hG : NumGroup v add) {gs : List ℕ} (hgs : ∀ g ∈ gs, 0 < g ∧ g < v)
    {off L : ℕ} (hoff : v ≤ off) {vals : List ℕ} {F : ℕ} {leaf : ℕ → ℕ → Bool}
    (ht : Truth v add ((L : ℤ) - off) F f) {tv : List ℕ} :
    ∀ (sts : List Step) (P M A : ℕ) (acc : List ℕ) (r : ℕ) (cand : List (List ℕ)),
      go L vals F leaf sts P M A acc r cand = true →
      (∀ st ∈ sts, st.nb = gs.map (fun g => (add st.x g, add st.x (negN v add g))) ∧
        code (f st.x) ∈ vals ∧ (tv.getD st.b 0 : ℤ) = 3 + (st.cs.map f).sum) →
      Inv v add gs off f sts P M A acc r → tv ∈ cand →
      ∃ P' M', (∀ y, P'.testBit y = decide (f y = 1) ∧ M'.testBit y = decide (f y = -1)) ∧
        leaf P' M' = true
  | [], P, M, A, acc, r, cand, h, _, hi, _ => by
    have hA : ∀ y, f y ≠ 0 → A.testBit y = true := by
      intro y hf
      have hy : y < v := by
        by_contra hy; exact hf (ht.out y (by omega))
      have := hi.cover y hy hf
      simpa using this
    have hr : r = 0 := by
      have := hi.rest
      rw [Finset.sum_eq_zero fun y _ => ?_] at this
      · exact_mod_cast this
      · by_cases hf : f y = 0
        · simp [hf]
        · simp [hA y hf]
    subst hr
    have h' : leaf P M = true := h
    refine ⟨P, M, fun y => ?_, h'⟩
    rw [(hi.enc y).1, (hi.enc y).2]
    by_cases hf : f y = 0
    · simp [hf]
    · simp [hA y hf]
  | st :: sts, P, M, A, acc, r, cand, h, hst, hi, htv => by
    obtain ⟨hnb, hval, hcos⟩ := hst st List.mem_cons_self
    have hst' : ∀ st' ∈ sts, st'.nb = gs.map
        (fun g => (add st'.x g, add st'.x (negN v add g))) ∧ code (f st'.x) ∈ vals ∧
        (tv.getD st'.b 0 : ℤ) = 3 + (st'.cs.map f).sum :=
      fun st' h' => hst st' (List.mem_cons_of_mem _ h')
    obtain ⟨hxv, hxA⟩ := hi.fresh st List.mem_cons_self
    have hsgn := ht.sign st.x
    rw [go_cons, allR_eq, List.all_eq_true] at h
    have h := h (code (f st.x)) hval
    obtain ⟨A', hA'eq⟩ : ∃ A', Nat.lor A (2 ^ st.x) = A' := ⟨_, rfl⟩
    have hA' : ∀ y, A'.testBit y = (A.testBit y || decide (y = st.x)) := fun y => by
      rw [← hA'eq]; exact testBit_lor_two_pow A st.x y
    have henc' : EncA A' f (nextP P st.x (code (f st.x))) (nextM M st.x (code (f st.x))) := by
      rw [nextP_code hsgn, nextM_code hsgn, ← hA'eq]; exact encA_step hi.enc
    -- the nonzero values off the new assigned set
    have hterm : ∀ y, (if A.testBit y then (0 : ℤ) else f y * f y) =
        (if A'.testBit y then 0 else f y * f y) + (if y = st.x then f y * f y else 0) := by
      intro y
      rw [hA']
      by_cases hy : y = st.x
      · subst hy; simp [hxA]
      · simp [hy]
    have hsplit : ∑ y ∈ Finset.range v, (if A.testBit y then 0 else f y * f y) =
        ∑ y ∈ Finset.range v, (if A'.testBit y then 0 else f y * f y) + f st.x * f st.x := by
      rw [Finset.sum_congr rfl fun y _ => hterm y, Finset.sum_add_distrib,
        Finset.sum_ite_eq' (Finset.range v) st.x, ite_eq_left (Finset.mem_range.2 hxv)]
    have hr0 := hi.rest
    rw [hsplit] at hr0
    have hnodup := List.nodup_cons.1 (by simpa using hi.nodup :
      (st.x :: sts.map Step.x).Nodup)
    have hfresh' : ∀ st' ∈ sts, st'.x < v ∧ A'.testBit st'.x = false := by
      intro st' h'
      obtain ⟨h1, h2⟩ := hi.fresh st' (List.mem_cons_of_mem _ h')
      refine ⟨h1, ?_⟩
      have : st'.x ≠ st.x := fun e => hnodup.1 (e ▸ List.mem_map_of_mem h')
      simp [hA', h2, this]
    have hcover' : ∀ y, y < v → f y ≠ 0 → A'.testBit y = true ∨ y ∈ sts.map Step.x := by
      intro y hy hf
      rcases hi.cover y hy hf with h1 | h1
      · left; simp [hA', h1]
      · simp only [List.map_cons, List.mem_cons] at h1
        rcases h1 with h1 | h1
        · left; simp [hA', h1]
        · exact Or.inr h1
    -- the count left fits in the steps left
    have hcnt : ∀ r' : ℕ, (r' : ℤ) =
        ∑ y ∈ Finset.range v, (if A'.testBit y then 0 else f y * f y) → r' ≤ sts.length := by
      intro r' hr'
      have hle : (r' : ℤ) ≤ (((Finset.range v).filter fun y =>
          A'.testBit y = false ∧ f y ≠ 0).card : ℤ) := by
        rw [hr', Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_le_sum fun y _ => ?_
        cases hA : A'.testBit y
        · rcases ht.sign y with h1 | h1 | h1 <;> simp [h1]
        · simp
      have hsub : ((Finset.range v).filter fun y => A'.testBit y = false ∧ f y ≠ 0) ⊆
          (sts.map Step.x).toFinset := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_range] at hy
        rcases hcover' y hy.1 hy.2.2 with h1 | h1
        · rw [hy.2.1] at h1; exact absurd h1 Bool.false_ne_true
        · exact List.mem_toFinset.2 h1
      have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
      rw [List.length_map] at this
      omega
    -- the candidates
    have hcand' : tv ∈ nextCand st A' F (nextP P st.x (code (f st.x)))
        (nextM M st.x (code (f st.x))) cand := by
      unfold nextCand
      cases hs : st.cs.all (settled A' F)
      · exact htv
      · refine List.mem_filter.2 ⟨htv, ?_⟩
        have hsum : (st.cs.map f).sum = (st.cs.map (valM (nextP P st.x (code (f st.x)))
            (nextM M st.x (code (f st.x))))).sum := by
          congr 1
          refine List.map_congr_left fun y hy => ?_
          rw [valM_of_encA ht.sign henc']
          have hy' := List.all_eq_true.1 hs y hy
          simp only [settled, Bool.or_eq_true, Nat.beq_eq, bit_eq] at hy'
          unfold onA
          rcases hy' with h1 | h1
          · have : A'.testBit y = true := by
              cases hb : A'.testBit y
              · rw [hb] at h1; exact absurd h1 (by decide)
              · rfl
            rw [ite_eq_left this]
          · have hF : F.testBit y = true := by
              cases hb : F.testBit y
              · rw [hb] at h1; exact absurd h1 (by decide)
              · rfl
            rw [ht.zero y hF]
            split_ifs <;> rfl
        have e : ((tv.getD st.b 0 + cnt (nextM M st.x (code (f st.x))) st.cs : ℕ) : ℤ) =
            ((3 + cnt (nextP P st.x (code (f st.x))) st.cs : ℕ) : ℤ) := by
          have := cnt_sub (nextP P st.x (code (f st.x))) (nextM M st.x (code (f st.x))) st.cs
          push_cast
          rw [hcos, hsum]
          linarith
        have e' := Nat.cast_injective (R := ℤ) e
        change Nat.beq (Nat.add _ _) (Nat.add _ _) = true
        rw [show Nat.add (tv.getD st.b 0) (cnt (nextM M st.x (code (f st.x))) st.cs) =
          Nat.add 3 (cnt (nextP P st.x (code (f st.x))) st.cs) from e']
        exact Nat.beq_refl _
    have hne : ∀ P' M', tv ∈ nextCand st A' F P' M' cand →
        (nextCand st A' F P' M' cand).isEmpty = false := by
      intro P' M' hm
      cases hc : nextCand st A' F P' M' cand with
      | nil => rw [hc] at hm; simp at hm
      | cons _ _ => rfl
    by_cases h0 : f st.x = 0
    · -- the code `0`: nothing changes but `A` and the candidates
      have hc0 : code (f st.x) = 0 := by rw [h0]; rfl
      rw [hc0] at h hcand' henc'
      change tv ∈ nextCand st A' F P M cand at hcand'
      change EncA A' f P M at henc'
      have hrest' : (r : ℤ) = ∑ y ∈ Finset.range v, (if A'.testBit y then 0 else f y * f y) := by
        rw [hr0, h0]; ring
      have hcut : cutZ F sts.length st P M A r cand = false := by
        unfold cutZ
        rw [hA'eq, hne P M hcand', Bool.or_false]
        cases hb : Nat.blt sts.length r
        · rfl
        · simp only [Nat.blt_eq] at hb; have := hcnt r hrest'; omega
      rw [tryU_zero, hcut, hA'eq, Bool.cond_false] at h
      have hacc' : ∀ i, i < gs.length → ((acc.getD i 0 : ℕ) : ℤ) =
          off + ∑ y ∈ Finset.range v, onA A' f y * onA A' f (add y (gs.getD i 0)) := by
        intro i hi'
        have hg := hgs _ (getD_mem hi')
        rw [hi.acc i hi', corr_step hG hA' hxv hxA hg.2 hg.1, h0, zero_mul, add_zero]
      exact go_sound hG hgs hoff ht sts _ _ _ _ _ _ h hst'
        ⟨henc', hi.len, hacc', hrest', hfresh', hnodup.2, hcover'⟩ hcand'
    · -- a nonzero code: the sums move
      have hu : Nat.beq (code (f st.x)) 0 = false := by
        rcases hsgn with h1 | h1 | h1
        · rw [h1]; rfl
        · exact absurd h1 h0
        · rw [h1]; rfl
      have hsq : f st.x * f st.x = 1 := by rcases hsgn with h1 | h1 | h1 <;> simp_all
      have hr1 : 1 ≤ r := by
        have hnn : 0 ≤ ∑ y ∈ Finset.range v, (if A'.testBit y then 0 else f y * f y) :=
          Finset.sum_nonneg fun y _ => by split_ifs <;> nlinarith
        have : (1 : ℤ) ≤ r := by linarith
        exact_mod_cast this
      have hrest' : ((Nat.sub r 1 : ℕ) : ℤ) =
          ∑ y ∈ Finset.range v, (if A'.testBit y then 0 else f y * f y) := by
        rw [Nat.sub_eq, Nat.cast_sub hr1]
        push_cast
        linarith
      have hlen' : (accU st P M (code (f st.x)) acc).length = gs.length := by
        rw [accU, length_updR, hnb, hi.len]; simp
      have hacc' : ∀ i, i < gs.length → (((accU st P M (code (f st.x)) acc).getD i 0 : ℕ) : ℤ) =
          off + ∑ y ∈ Finset.range v, onA A' f y * onA A' f (add y (gs.getD i 0)) := by
        intro i hi'
        have hg := hgs _ (getD_mem hi')
        have hnbi : st.nb.getD i (0, 0) =
            (add st.x (gs.getD i 0), add st.x (negN v add (gs.getD i 0))) := by
          rw [hnb, List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
            List.getD_eq_getElem _ _ hi']
        rw [accU, updR_getD _ _ _ _ i (by rw [hnb]; simpa using hi') (by rw [hi.len]; exact hi'),
          hnbi]
        have hc := hi.acc i hi'
        have hstep := corr_step hG hA' hxv hxA hg.2 hg.1 (f := f)
        have ho1 := orient_sub hsgn h0 P M (add st.x (gs.getD i 0))
        have ho2 := orient_sub hsgn h0 P M (add st.x (negN v add (gs.getD i 0)))
        rw [valM_of_encA ht.sign hi.enc] at ho1 ho2
        have hge := corr_ge ht.sign A' (gs.getD i 0) (v := v) (add := add) (f := f)
        have hv : (v : ℤ) ≤ off := by exact_mod_cast hoff
        simp only [Nat.add_eq, Nat.sub_eq]
        have key : ((acc.getD i 0 + bit (bif Nat.beq (code (f st.x)) 1 then P else M)
              (add st.x (gs.getD i 0)) + bit (bif Nat.beq (code (f st.x)) 1 then P else M)
              (add st.x (negN v add (gs.getD i 0))) : ℕ) : ℤ) -
            ((bit (bif Nat.beq (code (f st.x)) 1 then M else P) (add st.x (gs.getD i 0)) +
              bit (bif Nat.beq (code (f st.x)) 1 then M else P)
                (add st.x (negN v add (gs.getD i 0))) : ℕ) : ℤ) =
            off + ∑ y ∈ Finset.range v, onA A' f y * onA A' f (add y (gs.getD i 0)) := by
          push_cast
          rw [hstep]
          linear_combination hc + ho1 + ho2
        rw [Nat.cast_sub (by omega), key]
      have hnear : nearR (Nat.sub L (Nat.mul 2 (Nat.sub r 1)))
          (Nat.add L (Nat.mul 2 (Nat.sub r 1))) (accU st P M (code (f st.x)) acc) = true := by
        refine nearR_of _ fun i hi' => ?_
        rw [hlen'] at hi'
        have e := hacc' i hi'
        have hg := hgs _ (getD_mem hi')
        have hcl := abs_le.1 (corr_close hG ht A' hg.2 hg.1)
        rw [← hrest'] at hcl
        simp only [Nat.sub_eq, Nat.add_eq, Nat.mul_eq] at hcl ⊢
        constructor <;> omega
      have hcut : cutNZ L F sts.length st P M A acc r cand (code (f st.x)) = false := by
        unfold cutNZ
        rw [hA'eq, hnear, hne _ _ hcand', Bool.not_true, Bool.or_false, Bool.or_false]
        cases hb : Nat.beq r 0
        · cases hb' : Nat.blt sts.length (Nat.sub r 1)
          · rfl
          · simp only [Nat.blt_eq] at hb'; have := hcnt _ hrest'; omega
        · have := Nat.eq_of_beq_eq_true hb; omega
      rw [tryU_nz _ _ _ _ _ _ _ _ _ _ _ _ hu, hcut, hA'eq, Bool.cond_false] at h
      exact go_sound hG hgs hoff ht sts _ _ _ _ _ _ h hst'
        ⟨henc', hlen', hacc', hrest', hfresh', hnodup.2, hcover'⟩ hcand'

/-! ### Splitting the search -/

/-- A state of `go`: the steps left and its arguments. -/
structure Node where
  /-- The steps left. -/
  sts : List Step
  /-- The plus mask. -/
  P : ℕ
  /-- The minus mask. -/
  M : ℕ
  /-- The assigned positions. -/
  A : ℕ
  /-- The shift sums. -/
  acc : List ℕ
  /-- The nonzero values left. -/
  r : ℕ
  /-- The candidates. -/
  cand : List (List ℕ)

/-- `go` from a node. -/
noncomputable def Node.run (L : ℕ) (vals : List ℕ) (F : ℕ) (leaf : ℕ → ℕ → Bool) (nd : Node) :
    Bool :=
  go L vals F leaf nd.sts nd.P nd.M nd.A nd.acc nd.r nd.cand

/-- The nodes below a state that `go` does not cut, expanded while `ex P M A` holds. -/
noncomputable def front (L : ℕ) (vals : List ℕ) (F : ℕ) (ex : ℕ → ℕ → ℕ → Bool)
    (sts : List Step) : ℕ → ℕ → ℕ → List ℕ → ℕ → List (List ℕ) → List Node :=
  @List.rec Step (fun _ => ℕ → ℕ → ℕ → List ℕ → ℕ → List (List ℕ) → List Node)
    (fun P M A acc r cand => [⟨[], P, M, A, acc, r, cand⟩])
    (fun st sts ih P M A acc r cand =>
      bif ex P M A then flatL (tryU [] L F sts.length st P M A acc r cand ih) vals
      else [⟨st :: sts, P, M, A, acc, r, cand⟩]) sts

theorem tryU_lift {L F n : ℕ} {st : Step} {P M A : ℕ} {acc : List ℕ} {r : ℕ}
    {cand : List (List ℕ)} {Q : Node → Prop}
    {kf : ℕ → ℕ → ℕ → List ℕ → ℕ → List (List ℕ) → List Node}
    {kg : ℕ → ℕ → ℕ → List ℕ → ℕ → List (List ℕ) → Bool}
    (hk : ∀ P M A acc r cand, (∀ nd ∈ kf P M A acc r cand, Q nd) → kg P M A acc r cand = true)
    (u : ℕ) :
    (∀ nd ∈ tryU [] L F n st P M A acc r cand kf u, Q nd) →
      tryU true L F n st P M A acc r cand kg u = true := by
  unfold tryU
  cases Nat.beq u 0
  · cases cutNZ L F n st P M A acc r cand u
    · exact hk _ _ _ _ _ _
    · intro _; rfl
  · cases cutZ F n st P M A r cand
    · exact hk _ _ _ _ _ _
    · intro _; rfl

/-- `go` passes if it passes from every node of a front. -/
theorem go_of_front {L : ℕ} {vals : List ℕ} {F : ℕ} {leaf : ℕ → ℕ → Bool}
    {ex : ℕ → ℕ → ℕ → Bool} : ∀ (sts : List Step) (P M A : ℕ) (acc : List ℕ) (r : ℕ)
      (cand : List (List ℕ)), (∀ nd ∈ front L vals F ex sts P M A acc r cand,
        nd.run L vals F leaf = true) → go L vals F leaf sts P M A acc r cand = true
  | [], P, M, A, acc, r, cand, h => h ⟨[], P, M, A, acc, r, cand⟩ List.mem_cons_self
  | st :: sts, P, M, A, acc, r, cand, h => by
    change ∀ nd ∈ (bif ex P M A then
      flatL (tryU [] L F sts.length st P M A acc r cand (front L vals F ex sts)) vals
      else [⟨st :: sts, P, M, A, acc, r, cand⟩]), nd.run L vals F leaf = true at h
    cases hex : ex P M A
    · rw [hex] at h
      exact h ⟨st :: sts, P, M, A, acc, r, cand⟩ List.mem_cons_self
    · rw [hex, Bool.cond_true] at h
      rw [go_cons, allR_eq, List.all_eq_true]
      intro u hu
      exact tryU_lift (Q := fun nd => nd.run L vals F leaf = true)
        (fun P M A acc r cand hk => go_of_front sts P M A acc r cand hk) u
        (fun nd hnd => h nd ((mem_flatL _ _ _).2 ⟨u, hu, hnd⟩))

end SignedDifferenceSets.PairSearch
