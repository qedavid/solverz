module

public import SignedDifferenceSets.VectorSearch

/-!
# Splitting the vector search on two levels

`noVector_of_top`'s coverage check compares every node at the split depth with every listed
prefix, so its cost grows with the square of the number of prefixes. `below_of_top` splits the
search below one prefix `p` the same way, so a large search splits at a shallow depth into few
groups, and each group again into few prefixes.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- `below` a prefix `p` from `goTop`'s levels under `p` and the checks of the nodes it leaves to
`P`. -/
theorem below_of_top {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {P : List (List ℤ)} {d : ℕ}
    {p : List ℤ} (hne : p ≠ []) (hlen : p.length ≤ n)
    (htop : goTop n add c Q t k s |p.headD 0| P d (n - p.length) p.reverse p.sum (sqSum p)
      (absSum p) = true)
    (hP : ∀ q ∈ P, below n add c Q t k s q = true) : below n add c Q t k s p = true := by
  unfold below
  refine go_of_goTop hP d (n - p.length) p.reverse p.sum (sqSum p) (absSum p)
    (by simpa using hne) (by simp) (by simp only [List.length_reverse]; omega) (by simp)
    (by simp [sqSum, List.map_reverse]) (by simp [absSum, List.map_reverse]) htop

end SignedDifferenceSets
