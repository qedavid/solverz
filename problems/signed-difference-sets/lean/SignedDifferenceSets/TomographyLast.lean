module

public import SignedDifferenceSets.TomographySplit

/-!
# `inSearch` with the last coordinate solved from the sum (I23)

`goInL` is `goIn` whose last level tries only `x = s − Σ`: every other `x` misses the sum, which
`goIn`'s leaf rejects anyway (`goIn_of_goInL`). `inPartL` and `belowInL` are `inPart` and
`belowIn` on `goInL` and imply them (`inPart_of_inPartL`, `belowIn_of_belowInL`), so a row checks
the cheaper search and reuses `inSearch`'s soundness and splits unchanged.
-/

@[expose] public section

namespace SignedDifferenceSets.Tomography

/-- `goIn` with the last coordinate solved from the sum. -/
def goInL (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s top : ℤ) (V : List (List ℤ)) :
    ℕ → List ℤ → ℤ → ℤ → ℤ → Bool
  | 0, pre, sum, sq, abs =>
    !leafOK n add Q t k s pre.reverse sum sq abs || V.contains pre.reverse
  | 1, pre, sum, sq, abs =>
    decide (top < |s - sum|) ||
      goInL n add c Q t k s top V 0 ((s - sum) :: pre) (sum + (s - sum))
        (sq + (s - sum) * (s - sum)) (abs + |s - sum|)
  | rem + 2, pre, sum, sq, abs =>
    cut c Q s (rem + 2) sum sq ||
      allRange (fun x => decide (Q - sq < x * x) ||
        goInL n add c Q t k s top V (rem + 1) (x :: pre) (sum + x) (sq + x * x) (abs + |x|))
        (-top) (2 * top + 1).toNat

theorem goIn_of_goInL {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s top : ℤ} {V : List (List ℤ)} :
    ∀ (rem : ℕ) (pre : List ℤ) (sum sq abs : ℤ),
      goInL n add c Q t k s top V rem pre sum sq abs = true →
      goIn n add c Q t k s top V rem pre sum sq abs = true
  | 0, pre, sum, sq, abs, h => by simpa only [goIn, goInL] using h
  | 1, pre, sum, sq, abs, h => by
    simp only [goInL, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [goIn, Bool.or_eq_true, allRange_iff]
    refine Or.inr fun x h1 h2 => Or.inr ?_
    by_cases hx : x = s - sum
    · subst hx
      rcases h with h | h
      · exfalso
        have h3 : 0 ≤ 2 * top + 1 := by
          by_contra hneg
          rw [Int.toNat_of_nonpos (by omega)] at h2
          omega
        rw [Int.toNat_of_nonneg h3] at h2
        exact (not_le.2 h) (abs_le.2 ⟨by omega, by omega⟩)
      · simpa only [goIn, goInL] using h
    · have hne : (sum + x == s) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        exact hx (by omega)
      simp [leafOK, hne]
  | rem + 2, pre, sum, sq, abs, h => by
    rw [goInL.eq_3] at h
    rw [goIn.eq_2]
    simp only [Bool.or_eq_true, allRange_iff] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    refine Or.inr fun x h1 h2 => ?_
    rcases h x h1 h2 with hx | hx
    · exact Or.inl hx
    exact Or.inr (goIn_of_goInL (rem + 1) _ _ _ _ hx)

/-- `belowIn` on `goInL`. -/
def belowInL (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (V : List (List ℤ)) (p : List ℤ) :
    Bool :=
  goInL n add c Q t k s |p.headD 0| V (n - p.length) p.reverse p.sum (sqSum p) (absSum p)

theorem belowIn_of_belowInL {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {V : List (List ℤ)}
    {p : List ℤ} (h : belowInL n add c Q t k s V p = true) :
    belowIn n add c Q t k s V p = true :=
  goIn_of_goInL _ _ _ _ _ h

/-- `inPart` on `goInL`. -/
def inPartL (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (V : List (List ℤ)) (lo : ℤ) (m : ℕ) :
    Bool :=
  allRange (fun x => decide (Q < x * x) ||
    goInL n add c Q t k s |x| V (n - 1) [x] x (x * x) |x|) lo m

theorem inPart_of_inPartL {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {V : List (List ℤ)}
    {lo : ℤ} {m : ℕ} (h : inPartL n add c Q t k s V lo m = true) :
    inPart n add c Q t k s V lo m = true := by
  simp only [inPartL, Bool.or_eq_true, allRange_iff] at h
  simp only [inPart, Bool.or_eq_true, allRange_iff]
  intro x h1 h2
  rcases h x h1 h2 with hx | hx
  · exact Or.inl hx
  · exact Or.inr (goIn_of_goInL _ _ _ _ _ hx)

end SignedDifferenceSets.Tomography
