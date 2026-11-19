import SignedDifferenceSets.TomographyFlat
import SignedDifferenceSets.TomographyFlatSplit
import SignedDifferenceSets.Tests.TomographyFlat
import SignedDifferenceSets.TomographyFlatRows.N1227
import SignedDifferenceSets.TomographyFlatRows.N1252
import SignedDifferenceSets.TomographyFlatRows.N1253
import SignedDifferenceSets.TomographyFlatRows.N1262
import SignedDifferenceSets.TomographyFlatRows.N1272
import SignedDifferenceSets.TomographyFlatRows.N1307
import SignedDifferenceSets.TomographyFlatRows.N14590
import SignedDifferenceSets.TomographyFlatRows.N14591
import SignedDifferenceSets.TomographyFlatRows.N14593
import SignedDifferenceSets.TomographyFlatRows.N14688
import SignedDifferenceSets.TomographyFlatRows.N14689
import SignedDifferenceSets.TomographyFlatRows.N14691
import SignedDifferenceSets.TomographyFlatRows.N14807
import SignedDifferenceSets.TomographyFlatRows.N14808
import SignedDifferenceSets.TomographyFlatRows.N14810
import SignedDifferenceSets.TomographyFlatRows.N15017
import SignedDifferenceSets.TomographyFlatRows.N15018
import SignedDifferenceSets.TomographyFlatRows.N15019
import SignedDifferenceSets.TomographyFlatRows.N15020
import SignedDifferenceSets.TomographyFlatRows.N15059
import SignedDifferenceSets.TomographyFlatRows.N15060
import SignedDifferenceSets.TomographyFlatRows.N15062
import SignedDifferenceSets.TomographyFlatRows.N15122
import SignedDifferenceSets.TomographyFlatRows.N15123
import SignedDifferenceSets.TomographyFlatRows.N15124
import SignedDifferenceSets.TomographyFlatRows.N15125
import SignedDifferenceSets.TomographyFlatRows.N23597
import SignedDifferenceSets.TomographyFlatRows.N23726
import SignedDifferenceSets.TomographyFlatRows.N23765
import SignedDifferenceSets.TomographyFlatRows.N23831
import SignedDifferenceSets.TomographyFlatRows.N33408
import SignedDifferenceSets.TomographyFlatRows.N33564
import SignedDifferenceSets.TomographyFlatRows.N33687
import SignedDifferenceSets.TomographyFlatRows.N33717
import SignedDifferenceSets.TomographyFlatRows.N46206
import SignedDifferenceSets.TomographyFlatRows.N46207
import SignedDifferenceSets.TomographyFlatRows.N757
import SignedDifferenceSets.TomographyFlatRows.N8508
import SignedDifferenceSets.TomographyFlatRows.N8517
import SignedDifferenceSets.TomographyFlatRows.N8532
import SignedDifferenceSets.TomographyFlatRows.N8541

open SignedDifferenceSets

#print axioms SignedDifferenceSets.TomographyFlat.not_hasSDS_flat_core
#print axioms SignedDifferenceSets.TomographyFlat.not_hasSDS_flat
#print axioms SignedDifferenceSets.TomographyFlat.not_hasSDS_flat_nc
#print axioms SignedDifferenceSets.TomographyFlat.flatKill_of_top
#print axioms SignedDifferenceSets.TomographyFlat.sum_contract_flat
#print axioms SignedDifferenceSets.TomographyFlat.flatGo_of_top
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 20 1 := TomographyFlatRows.N1227.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N1227.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 41 4 := TomographyFlatRows.N1252.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N1252.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 9) 41 4 := TomographyFlatRows.N1253.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N1253.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 41 10 := TomographyFlatRows.N1262.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N1262.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 49 6 := TomographyFlatRows.N1272.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N1272.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 64 33 := TomographyFlatRows.N1307.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N1307.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 121 24 := TomographyFlatRows.N14590.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N14590.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 9) 121 24 := TomographyFlatRows.N14591.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N14591.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 9 × ZMod 9) 121 24 := TomographyFlatRows.N14593.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N14593.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 141 2 := TomographyFlatRows.N14688.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N14688.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 9) 141 2 := TomographyFlatRows.N14689.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N14689.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 9 × ZMod 9) 141 2 := TomographyFlatRows.N14691.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N14691.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 170 67 := TomographyFlatRows.N14807.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N14807.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 9) 170 67 := TomographyFlatRows.N14808.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N14808.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 9 × ZMod 9) 170 67 := TomographyFlatRows.N14810.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N14810.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 213 86 := TomographyFlatRows.N15017.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15017.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 9) 213 86 := TomographyFlatRows.N15018.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15018.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 27) 213 86 := TomographyFlatRows.N15019.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15019.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 9 × ZMod 9) 213 86 := TomographyFlatRows.N15020.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15020.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 221 70 := TomographyFlatRows.N15059.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15059.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 9) 221 70 := TomographyFlatRows.N15060.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15060.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 9 × ZMod 9) 221 70 := TomographyFlatRows.N15062.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15062.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 234 5 := TomographyFlatRows.N15122.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15122.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 9) 234 5 := TomographyFlatRows.N15123.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15123.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 27) 234 5 := TomographyFlatRows.N15124.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15124.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 9 × ZMod 9) 234 5 := TomographyFlatRows.N15125.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N15125.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 33) 41 4 := TomographyFlatRows.N23597.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N23597.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 33) 184 21 := TomographyFlatRows.N23726.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N23726.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 33) 201 38 := TomographyFlatRows.N23765.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N23765.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 33) 248 151 := TomographyFlatRows.N23831.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N23831.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 39) 189 50 := TomographyFlatRows.N33408.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N33408.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 39) 266 109 := TomographyFlatRows.N33564.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N33564.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 39) 319 3 := TomographyFlatRows.N33687.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N33687.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 39) 329 16 := TomographyFlatRows.N33717.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N33717.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 15) 316 45 := TomographyFlatRows.N46206.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N46206.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 45) 316 45 := TomographyFlatRows.N46207.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N46207.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) 58 42 := TomographyFlatRows.N757.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N757.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 21) 145 102 := TomographyFlatRows.N8508.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N8508.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 21) 148 21 := TomographyFlatRows.N8517.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N8517.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 21) 153 2 := TomographyFlatRows.N8532.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N8532.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 21) 157 9 := TomographyFlatRows.N8541.not_hasSDS
#print axioms SignedDifferenceSets.TomographyFlatRows.N8541.not_hasSDS
