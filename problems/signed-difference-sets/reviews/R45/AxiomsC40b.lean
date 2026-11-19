import SignedDifferenceSets.TomographyRows.N3074
import SignedDifferenceSets.TomographyRows.N3104

/-! Refuter (C40): axioms of the last two rows; their types restated from `instances.csv`. -/

open SignedDifferenceSets

#print axioms TomographyRows.N3074.not_hasSDS
#print axioms TomographyRows.N3104.not_hasSDS

example : ¬ HasSDS (ZMod 11 × ZMod 11) 76 45 := TomographyRows.N3074.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 11) 105 46 := TomographyRows.N3104.not_hasSDS
