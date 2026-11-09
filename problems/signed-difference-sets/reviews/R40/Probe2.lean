import SignedDifferenceSets.MaEdgeRows
open SignedDifferenceSets

#print axioms SignedDifferenceSets.IsSDS.dvd_lam_mul_of_ma
#print axioms SignedDifferenceSets.MaEdgeCert.not_hasSDS
#print axioms SignedDifferenceSets.MaEdgeRows.maEdgeRows_kills
#print axioms SignedDifferenceSets.MaEdgeRows.n2847_not_hasSDS
#print axioms SignedDifferenceSets.MaEdgeRows.n21854_not_hasSDS
#print axioms SignedDifferenceSets.MaEdgeRows.n54548_not_hasSDS
#print axioms SignedDifferenceSets.MaEdgeRows.n69420_not_hasSDS
#print axioms SignedDifferenceSets.MaEdgeRows.n23593_not_hasSDS
#check @SignedDifferenceSets.IsSDS.dvd_lam_mul_of_ma
#print SignedDifferenceSets.MaEdgeCert.Kills

-- probe: a row theorem is literally "no SDS" on the row's group, written out without HasSDS / Grp
example : ¬ ∃ D : ZMod 2 × ZMod 2 × ZMod 72 → SignType,
    (Finset.univ.filter fun x => D x ≠ 0).card = 148 ∧
      ∀ g : ZMod 2 × ZMod 2 × ZMod 72, g ≠ 0 → ∑ x, ((D x : ℤ) * (D (x + g) : ℤ)) = 4 :=
  MaEdgeRows.n21854_not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 147) 201 5 := MaEdgeRows.n54548_not_hasSDS
