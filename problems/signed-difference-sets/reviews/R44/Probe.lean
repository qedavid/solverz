import SignedDifferenceSets.PairRows.N464
import SignedDifferenceSets.Tests.PairSearch
import SignedDifferenceSets.Answer.N449

/-! Refuter probe for C37: statement shape, definitions, axioms. -/

-- The theorem is literally the row's goal (N464 = SDS(54,46,10,[3,18])).
example : ¬ SignedDifferenceSets.HasSDS (ZMod 3 × ZMod 18) 46 10 :=
  SignedDifferenceSets.PairRows.N464.n464_not_hasSDS

-- HasSDS / IsSDS unfold to the approved definitions.
example : SignedDifferenceSets.HasSDS (ZMod 3 × ZMod 18) 46 10 =
    ∃ D : ZMod 3 × ZMod 18 → SignType, SignedDifferenceSets.IsSDS 46 10 D := rfl
example (D : ZMod 3 × ZMod 18 → SignType) : SignedDifferenceSets.IsSDS 46 10 D ↔
    ((Finset.univ.filter fun x => D x ≠ 0).card = 46 ∧
      ∀ g : ZMod 3 × ZMod 18, g ≠ 0 → ∑ x, ((D x : ℤ) * (D (x + g) : ℤ)) = 10) := Iff.rfl

-- Non-vacuity: the same group type does carry an SDS (N449).
example : SignedDifferenceSets.HasSDS (ZMod 3 × ZMod 18) 38 2 :=
  SignedDifferenceSets.Answer.N449.hasSDS

#check @SignedDifferenceSets.PairRows.N464.n464_not_hasSDS
#check @SignedDifferenceSets.halves_of_isSDS
#check @SignedDifferenceSets.PairCheck.no_pair
#print SignedDifferenceSets.PairRows.N464.split
#print axioms SignedDifferenceSets.PairRows.N464.n464_not_hasSDS
#print axioms SignedDifferenceSets.halves_of_isSDS
#print axioms SignedDifferenceSets.PairCheck.no_pair
#print axioms SignedDifferenceSets.PairCheck.zSearch_sound
#print axioms SignedDifferenceSets.PairCheck.tCheck_sound
#print axioms SignedDifferenceSets.PairCheck.zSearch_of_slices
#print axioms SignedDifferenceSets.PairSearch.go_sound
#print axioms SignedDifferenceSets.PairSearch.go_of_front
#print axioms SignedDifferenceSets.PairRows.N464.slices
#print axioms SignedDifferenceSets.PairRows.N464.split_bijective
#print axioms SignedDifferenceSets.PairRows.N464.groups_cover
#print axioms SignedDifferenceSets.Tests.PairSearch.n449_halves
#print axioms SignedDifferenceSets.Tests.PairSearch.n449_search_finds
