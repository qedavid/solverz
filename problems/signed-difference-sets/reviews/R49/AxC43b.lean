import SignedDifferenceSets.TomographyQuot
import SignedDifferenceSets.TomographyQuotRows.N15384
import SignedDifferenceSets.TomographyQuotRows.N20163
import SignedDifferenceSets.TomographyQuotRows.N20237
import SignedDifferenceSets.TomographyQuotRows.N31718
import SignedDifferenceSets.TomographyQuotRows.N31719
import SignedDifferenceSets.TomographyQuotRows.N36069
import SignedDifferenceSets.TomographyQuotRows.N36111
import SignedDifferenceSets.TomographyQuotRows.N36149
import SignedDifferenceSets.TomographyQuotRows.N36151
import SignedDifferenceSets.TomographyQuotRows.N36165
import SignedDifferenceSets.TomographyQuotRows.N36195
import SignedDifferenceSets.TomographyQuotRows.N36265
import SignedDifferenceSets.TomographyQuotRows.N38727
import SignedDifferenceSets.TomographyQuotRows.N4987
import SignedDifferenceSets.TomographyQuotRows.N5017
import SignedDifferenceSets.TomographyQuotRows.N5025
import SignedDifferenceSets.TomographyQuotRows.N54417
import SignedDifferenceSets.TomographyQuotRows.N54433
import SignedDifferenceSets.TomographyQuotRows.N54434
import SignedDifferenceSets.TomographyQuotRows.N54437
import SignedDifferenceSets.TomographyQuotRows.N54438
import SignedDifferenceSets.TomographyQuotRows.N54449
import SignedDifferenceSets.TomographyQuotRows.N54450
import SignedDifferenceSets.TomographyQuotRows.N54473
import SignedDifferenceSets.TomographyQuotRows.N54474
import SignedDifferenceSets.TomographyQuotRows.N54489
import SignedDifferenceSets.TomographyQuotRows.N54490
import SignedDifferenceSets.TomographyQuotRows.N54505
import SignedDifferenceSets.TomographyQuotRows.N54506
import SignedDifferenceSets.TomographyQuotRows.N54553
import SignedDifferenceSets.TomographyQuotRows.N54554
import SignedDifferenceSets.TomographyQuotRows.N54561
import SignedDifferenceSets.TomographyQuotRows.N54562
import SignedDifferenceSets.TomographyQuotRows.N54585
import SignedDifferenceSets.TomographyQuotRows.N54586
import SignedDifferenceSets.TomographyQuotRows.N54593
import SignedDifferenceSets.TomographyQuotRows.N54594
import SignedDifferenceSets.TomographyQuotRows.N54637
import SignedDifferenceSets.TomographyQuotRows.N54638
import SignedDifferenceSets.TomographyQuotRows.N54713
import SignedDifferenceSets.TomographyQuotRows.N54714
import SignedDifferenceSets.TomographyQuotRows.N54725
import SignedDifferenceSets.TomographyQuotRows.N54726
import SignedDifferenceSets.TomographyQuotRows.N54741
import SignedDifferenceSets.TomographyQuotRows.N54742
import SignedDifferenceSets.TomographyQuotRows.N54777
import SignedDifferenceSets.TomographyQuotRows.N54778
import SignedDifferenceSets.TomographyQuotRows.N54826
import SignedDifferenceSets.TomographyQuotRows.N54841
import SignedDifferenceSets.TomographyQuotRows.N54842
import SignedDifferenceSets.TomographyQuotRows.N54850
import SignedDifferenceSets.TomographyQuotRows.N54953
import SignedDifferenceSets.TomographyQuotRows.N54954
import SignedDifferenceSets.TomographyQuotRows.N54961
import SignedDifferenceSets.TomographyQuotRows.N54962
import SignedDifferenceSets.TomographyQuotRows.N54973
import SignedDifferenceSets.TomographyQuotRows.N54974
import SignedDifferenceSets.TomographyQuotRows.N55001
import SignedDifferenceSets.TomographyQuotRows.N55002
import SignedDifferenceSets.TomographyQuotRows.N55061
import SignedDifferenceSets.TomographyQuotRows.N55062
import SignedDifferenceSets.TomographyQuotRows.N55106

open SignedDifferenceSets

example : ¬ HasSDS (ZMod 7 × ZMod 35) 76 5 := TomographyQuotRows.N15384.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N15384.not_hasSDS
example : ¬ HasSDS (ZMod 5 × ZMod 55) 213 22 := TomographyQuotRows.N20163.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N20163.not_hasSDS
example : ¬ HasSDS (ZMod 5 × ZMod 55) 259 135 := TomographyQuotRows.N20237.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N20237.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 45 2 := TomographyQuotRows.N31718.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N31718.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 49) 45 2 := TomographyQuotRows.N31719.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N31719.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 33) 197 94 := TomographyQuotRows.N36069.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N36069.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 33) 233 4 := TomographyQuotRows.N36111.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N36111.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 33) 262 81 := TomographyQuotRows.N36149.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N36149.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 33) 262 99 := TomographyQuotRows.N36151.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N36151.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 33) 281 100 := TomographyQuotRows.N36165.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N36165.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 33) 302 79 := TomographyQuotRows.N36195.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N36195.not_hasSDS
example : ¬ HasSDS (ZMod 11 × ZMod 33) 337 24 := TomographyQuotRows.N36265.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N36265.not_hasSDS
example : ¬ HasSDS (ZMod 5 × ZMod 75) 353 292 := TomographyQuotRows.N38727.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N38727.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 21) 46 3 := TomographyQuotRows.N4987.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N4987.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 21) 77 34 := TomographyQuotRows.N5017.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N5017.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 21) 82 39 := TomographyQuotRows.N5025.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N5025.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 44 1 := TomographyQuotRows.N54417.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54417.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 81 2 := TomographyQuotRows.N54433.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54433.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 81 2 := TomographyQuotRows.N54434.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54434.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 81 14 := TomographyQuotRows.N54437.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54437.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 81 14 := TomographyQuotRows.N54438.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54438.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 89 10 := TomographyQuotRows.N54449.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54449.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 89 10 := TomographyQuotRows.N54450.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54450.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 124 15 := TomographyQuotRows.N54473.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54473.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 124 15 := TomographyQuotRows.N54474.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54474.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 169 6 := TomographyQuotRows.N54489.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54489.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 169 6 := TomographyQuotRows.N54490.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54490.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 169 60 := TomographyQuotRows.N54505.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54505.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 169 60 := TomographyQuotRows.N54506.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54506.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 201 8 := TomographyQuotRows.N54553.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54553.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 201 8 := TomographyQuotRows.N54554.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54554.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 201 50 := TomographyQuotRows.N54561.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54561.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 201 50 := TomographyQuotRows.N54562.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54562.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 209 46 := TomographyQuotRows.N54585.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54585.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 209 46 := TomographyQuotRows.N54586.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54586.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 220 27 := TomographyQuotRows.N54593.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54593.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 220 27 := TomographyQuotRows.N54594.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54594.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 236 85 := TomographyQuotRows.N54637.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54637.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 236 85 := TomographyQuotRows.N54638.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54638.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 280 3 := TomographyQuotRows.N54713.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54713.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 280 3 := TomographyQuotRows.N54714.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54714.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 284 7 := TomographyQuotRows.N54725.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54725.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 284 7 := TomographyQuotRows.N54726.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54726.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 284 175 := TomographyQuotRows.N54741.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54741.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 284 175 := TomographyQuotRows.N54742.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54742.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 289 138 := TomographyQuotRows.N54777.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54777.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 289 138 := TomographyQuotRows.N54778.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54778.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 344 11 := TomographyQuotRows.N54826.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54826.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 344 193 := TomographyQuotRows.N54841.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54841.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 344 193 := TomographyQuotRows.N54842.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54842.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 345 12 := TomographyQuotRows.N54850.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54850.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 364 33 := TomographyQuotRows.N54953.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54953.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 364 33 := TomographyQuotRows.N54954.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54954.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 364 201 := TomographyQuotRows.N54961.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54961.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 364 201 := TomographyQuotRows.N54962.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54962.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 364 297 := TomographyQuotRows.N54973.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54973.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 364 297 := TomographyQuotRows.N54974.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N54974.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 396 317 := TomographyQuotRows.N55001.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N55001.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 396 317 := TomographyQuotRows.N55002.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N55002.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 401 292 := TomographyQuotRows.N55061.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N55061.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 401 292 := TomographyQuotRows.N55062.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N55062.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 440 109 := TomographyQuotRows.N55106.not_hasSDS
#print axioms SignedDifferenceSets.TomographyQuotRows.N55106.not_hasSDS
