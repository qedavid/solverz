module

public import SignedDifferenceSets.MaDividedRes

/-!
# C38 without a residue: the plain divided search, split

With no residue primes (`M = 1`) C38's search `noVectorRes` is `noVector`, so a row of C38 at any
prime `p` (`p = 2` included, through the bounds list) can take `noVector`'s split certificate
(`noVector_of_top`) for each bound.
-/

@[expose] public section

namespace SignedDifferenceSets

theorem goRes_one {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s top x0 : ℤ} :
    ∀ (rem : ℕ) (pre : List ℤ) (sum sq abs : ℤ),
      goRes n add c Q t k s top 1 x0 rem pre sum sq abs = go n add c Q t k s top rem pre sum sq abs
  | 0, _, _, _, _ => rfl
  | rem + 1, pre, sum, sq, abs => by
    simp only [goRes, go, Int.emod_one, bne_self_eq_false, Bool.or_false, goRes_one rem]

theorem noVectorRes_one {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} :
    noVectorRes n add c Q t k s 1 = noVector n add c Q t k s := by
  simp only [noVectorRes, noVector, goRes_one]

/-- C38 with no residue primes, each bound's search given as `noVector` (which splits). -/
theorem MaDivResCert.not_hasSDS_noVector {w : Row} {c : MaDivResCert} (h : c.Valid w)
    (hqs : c.qs = []) (hpos : ∀ m ∈ c.r :: c.ks, 0 < m) (inst : Fintype (Grp w.ms))
    (hn : ∀ k' ∈ c.bounds, noVector (@Indexed.size (Grp (c.r :: c.ks)) _ (Grp.indexed _ hpos))
      (@Indexed.addIdx (Grp (c.r :: c.ks)) _ (Grp.indexed _ hpos))
      ((w.ms.prod / (c.r * c.p * c.ks.prod) : ℕ) : ℤ) c.Q c.t k' c.s' = true) :
    ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam :=
  MaDivResCert.not_hasSDS h hpos inst fun k' hk' => by
    rw [show (c.M : ℤ) = 1 by simp [MaDivResCert.M, hqs], noVectorRes_one]
    exact hn k' hk'

end SignedDifferenceSets
