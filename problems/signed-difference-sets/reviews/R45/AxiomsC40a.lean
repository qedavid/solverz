import SignedDifferenceSets.TomographyRows.N346
import SignedDifferenceSets.TomographyRows.N348
import SignedDifferenceSets.TomographyRows.N354
import SignedDifferenceSets.TomographyRows.N3044
import SignedDifferenceSets.TomographyRows.N3058
import SignedDifferenceSets.TomographyRows.N3068
import SignedDifferenceSets.TomographyRows.N3072
import SignedDifferenceSets.TomographyOrbit
import SignedDifferenceSets.Tests.Tomography

/-! Refuter (C40): axioms of the tomography theorems and the seven built rows; each row's type
restated from `instances.csv` with the default instances. -/

open SignedDifferenceSets

#print axioms Tomography.not_hasSDS_of_mem
#print axioms Tomography.not_hasSDS
#print axioms Tomography.not_hasSDS_prime
#print axioms Tomography.fixed_line
#print axioms Tomography.sum_contract_lines
#print axioms SignedDifferenceSets.IsSDS.exists_translate_fixed_contract
#print axioms TomographyRows.N346.not_hasSDS
#print axioms TomographyRows.N348.not_hasSDS
#print axioms TomographyRows.N354.not_hasSDS
#print axioms TomographyRows.N3044.not_hasSDS
#print axioms TomographyRows.N3058.not_hasSDS
#print axioms TomographyRows.N3068.not_hasSDS
#print axioms TomographyRows.N3072.not_hasSDS

example : ¬ HasSDS (ZMod 7 × ZMod 7) 25 2 := TomographyRows.N346.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7) 25 3 := TomographyRows.N348.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7) 33 4 := TomographyRows.N354.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 11) 40 3 := TomographyRows.N3044.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 11) 60 7 := TomographyRows.N3058.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 11) 76 5 := TomographyRows.N3068.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 11) 76 17 := TomographyRows.N3072.not_hasSDS

-- the main theorems' full statements
#check @Tomography.not_hasSDS
#check @Tomography.not_hasSDS_prime
#check @Tomography.fixed_line
