module

public import SignedDifferenceSets.TomographySearch

/-!
# Splitting `inSearch` below its first coordinate (I23)

`inPart` checks the first coordinates `lo, …, lo + m − 1` in one kernel check. `inPartTop` runs
only the top `d + 1` levels and leaves each node there, prefix `p`, to `belowIn … p`, checked
in separate declarations; `inPart_of_top` joins them (as `noVector_of_top` does for `noVector`).
-/

@[expose] public section

namespace SignedDifferenceSets.Tomography

/-- `goIn` below the prefix `p` (coordinates in order; `|p₀|` bounds the rest). -/
def belowIn (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (V : List (List ℤ)) (p : List ℤ) :
    Bool :=
  goIn n add c Q t k s |p.headD 0| V (n - p.length) p.reverse p.sum (sqSum p) (absSum p)

/-- `goIn`'s top `d` levels; a node `d` levels down, reversed prefix `pre`, is left to `P`. -/
def goInTop (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s top : ℤ) (V : List (List ℤ))
    (P : List (List ℤ)) : ℕ → ℕ → List ℤ → ℤ → ℤ → ℤ → Bool
  | 0, _, pre, _, _, _ => P.contains pre.reverse
  | _ + 1, 0, pre, sum, sq, abs =>
    !leafOK n add Q t k s pre.reverse sum sq abs || V.contains pre.reverse
  | d + 1, rem + 1, pre, sum, sq, abs =>
    cut c Q s (rem + 1) sum sq ||
      allRange (fun x => decide (Q - sq < x * x) ||
        goInTop n add c Q t k s top V P d rem (x :: pre) (sum + x) (sq + x * x) (abs + |x|))
        (-top) (2 * top + 1).toNat

/-- `inPart` with each node `d + 1` levels down left to `P`. -/
def inPartTop (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (V : List (List ℤ))
    (P : List (List ℤ)) (d : ℕ) (lo : ℤ) (m : ℕ) : Bool :=
  allRange (fun x => decide (Q < x * x) ||
    goInTop n add c Q t k s |x| V P d (n - 1) [x] x (x * x) |x|) lo m

theorem goIn_of_goInTop {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s top : ℤ} {V : List (List ℤ)}
    {P : List (List ℤ)} (hP : ∀ p ∈ P, belowIn n add c Q t k s V p = true) :
    ∀ (d rem : ℕ) (pre : List ℤ) (sum sq abs : ℤ), pre ≠ [] →
      top = |pre.reverse.headD 0| → rem + pre.length = n → sum = pre.sum → sq = sqSum pre →
      abs = absSum pre → goInTop n add c Q t k s top V P d rem pre sum sq abs = true →
      goIn n add c Q t k s top V rem pre sum sq abs = true
  | 0, rem, pre, sum, sq, abs, _, htop, hlen, hs, hq, ha, h => by
    simp only [goInTop, List.contains_iff_mem] at h
    have hb := hP _ h
    simp only [belowIn, List.reverse_reverse, List.length_reverse, sqSum, absSum,
      List.map_reverse, List.sum_reverse_int] at hb
    rw [htop, hs, hq, ha, show rem = n - pre.length by omega]
    exact hb
  | _ + 1, 0, pre, sum, sq, abs, _, _, _, _, _, _, h => by
    simpa only [goInTop, goIn] using h
  | d + 1, rem + 1, pre, sum, sq, abs, hne, htop, hlen, hs, hq, ha, h => by
    simp only [goInTop, Bool.or_eq_true, allRange_iff] at h
    simp only [goIn, Bool.or_eq_true, allRange_iff]
    rcases h with h | h
    · exact Or.inl h
    refine Or.inr fun x h1 h2 => ?_
    rcases h x h1 h2 with hx | hx
    · exact Or.inl hx
    refine Or.inr (goIn_of_goInTop hP d rem (x :: pre) (sum + x) (sq + x * x) (abs + |x|)
      (List.cons_ne_nil _ _) (by rw [headD_reverse_cons hne, htop]) ?_ ?_ ?_ ?_ hx)
    · simp only [List.length_cons]; omega
    · rw [List.sum_cons, hs]; ring
    · simp only [sqSum, List.map_cons, List.sum_cons] at hq ⊢; rw [hq]; ring
    · simp only [absSum, List.map_cons, List.sum_cons] at ha ⊢; rw [ha]; ring

/-- `inPart` from its top levels and the checks of the prefixes they leave to `P`. -/
theorem inPart_of_top {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {V : List (List ℤ)}
    {P : List (List ℤ)} {d : ℕ} {lo : ℤ} {m : ℕ} (hn : 0 < n)
    (h : inPartTop n add c Q t k s V P d lo m = true)
    (hP : ∀ p ∈ P, belowIn n add c Q t k s V p = true) :
    inPart n add c Q t k s V lo m = true := by
  simp only [inPartTop, Bool.or_eq_true, allRange_iff] at h
  simp only [inPart, Bool.or_eq_true, allRange_iff]
  intro x h1 h2
  rcases h x h1 h2 with hx | hx
  · exact Or.inl hx
  refine Or.inr (goIn_of_goInTop hP d (n - 1) [x] x (x * x) |x| (List.cons_ne_nil _ _)
    (by simp) (by simp; omega) (by simp) (by simp [sqSum]) (by simp [absSum]) hx)

end SignedDifferenceSets.Tomography
