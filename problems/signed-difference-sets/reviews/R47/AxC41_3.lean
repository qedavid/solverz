import SignedDifferenceSets.TomographyQuotNC
import SignedDifferenceSets.TomographyQuotRows.N2096
import SignedDifferenceSets.TomographyQuotRows.N2097
import SignedDifferenceSets.TomographyQuotRows.N32213
import SignedDifferenceSets.TomographyQuotRows.N35656
import SignedDifferenceSets.TomographyQuotRows.N35786
import SignedDifferenceSets.TomographyQuotRows.N35802
import SignedDifferenceSets.TomographyQuotRows.N35810
import SignedDifferenceSets.TomographyQuotRows.N35814
import SignedDifferenceSets.TomographyQuotRows.N35836
import SignedDifferenceSets.TomographyQuotRows.N35838
import SignedDifferenceSets.TomographyQuotRows.N35842
import SignedDifferenceSets.TomographyQuotRows.N35877
import SignedDifferenceSets.TomographyQuotRows.N6742

open SignedDifferenceSets

#print axioms TomographyQuotRows.N2096.not_hasSDS
example : ¬ HasSDS (ZMod 5 × ZMod 20) 97 72 := TomographyQuotRows.N2096.not_hasSDS
#print axioms TomographyQuotRows.N2097.not_hasSDS
example : ¬ HasSDS (ZMod 10 × ZMod 10) 97 72 := TomographyQuotRows.N2097.not_hasSDS
#print axioms TomographyQuotRows.N32213.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 342 151 := TomographyQuotRows.N32213.not_hasSDS
#print axioms TomographyQuotRows.N35656.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 145 8 := TomographyQuotRows.N35656.not_hasSDS
#print axioms TomographyQuotRows.N35786.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 280 17 := TomographyQuotRows.N35786.not_hasSDS
#print axioms TomographyQuotRows.N35802.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 289 56 := TomographyQuotRows.N35802.not_hasSDS
#print axioms TomographyQuotRows.N35810.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 289 150 := TomographyQuotRows.N35810.not_hasSDS
#print axioms TomographyQuotRows.N35814.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 289 228 := TomographyQuotRows.N35814.not_hasSDS
#print axioms TomographyQuotRows.N35836.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 316 65 := TomographyQuotRows.N35836.not_hasSDS
#print axioms TomographyQuotRows.N35838.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 316 117 := TomographyQuotRows.N35838.not_hasSDS
#print axioms TomographyQuotRows.N35842.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 316 273 := TomographyQuotRows.N35842.not_hasSDS
#print axioms TomographyQuotRows.N35877.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 360 89 := TomographyQuotRows.N35877.not_hasSDS
#print axioms TomographyQuotRows.N6742.not_hasSDS
example : ¬ HasSDS (ZMod 13 × ZMod 13) 120 7 := TomographyQuotRows.N6742.not_hasSDS
