import SignedDifferenceSets.KleinTomography
import SignedDifferenceSets.Tests.KleinTomography
import SignedDifferenceSets.KleinTomographyRows.N11534
import SignedDifferenceSets.KleinTomographyRows.N11535
import SignedDifferenceSets.KleinTomographyRows.N11538
import SignedDifferenceSets.KleinTomographyRows.N11540
import SignedDifferenceSets.KleinTomographyRows.N11541
import SignedDifferenceSets.KleinTomographyRows.N14164
import SignedDifferenceSets.KleinTomographyRows.N14165
import SignedDifferenceSets.KleinTomographyRows.N22020
import SignedDifferenceSets.KleinTomographyRows.N22021
import SignedDifferenceSets.KleinTomographyRows.N22022
import SignedDifferenceSets.KleinTomographyRows.N22023
import SignedDifferenceSets.KleinTomographyRows.N22024
import SignedDifferenceSets.KleinTomographyRows.N22025
import SignedDifferenceSets.KleinTomographyRows.N22028
import SignedDifferenceSets.KleinTomographyRows.N22029
import SignedDifferenceSets.KleinTomographyRows.N22030
import SignedDifferenceSets.KleinTomographyRows.N28407
import SignedDifferenceSets.KleinTomographyRows.N28409
import SignedDifferenceSets.KleinTomographyRows.N28411
import SignedDifferenceSets.KleinTomographyRows.N28413
import SignedDifferenceSets.KleinTomographyRows.N28497
import SignedDifferenceSets.KleinTomographyRows.N28499
import SignedDifferenceSets.KleinTomographyRows.N28501
import SignedDifferenceSets.KleinTomographyRows.N28503
import SignedDifferenceSets.KleinTomographyRows.N30796
import SignedDifferenceSets.KleinTomographyRows.N30797
import SignedDifferenceSets.KleinTomographyRows.N35300
import SignedDifferenceSets.KleinTomographyRows.N35302
import SignedDifferenceSets.KleinTomographyRows.N40502
import SignedDifferenceSets.KleinTomographyRows.N40503
import SignedDifferenceSets.KleinTomographyRows.N40504
import SignedDifferenceSets.KleinTomographyRows.N40505
import SignedDifferenceSets.KleinTomographyRows.N40506
import SignedDifferenceSets.KleinTomographyRows.N40507
import SignedDifferenceSets.KleinTomographyRows.N40508
import SignedDifferenceSets.KleinTomographyRows.N40509
import SignedDifferenceSets.KleinTomographyRows.N40511
import SignedDifferenceSets.KleinTomographyRows.N40512
import SignedDifferenceSets.KleinTomographyRows.N40513
import SignedDifferenceSets.KleinTomographyRows.N41211
import SignedDifferenceSets.KleinTomographyRows.N41213
import SignedDifferenceSets.KleinTomographyRows.N41214
import SignedDifferenceSets.KleinTomographyRows.N41216
import SignedDifferenceSets.KleinTomographyRows.N41217
import SignedDifferenceSets.KleinTomographyRows.N41218
import SignedDifferenceSets.KleinTomographyRows.N49387
import SignedDifferenceSets.KleinTomographyRows.N51965
import SignedDifferenceSets.KleinTomographyRows.N51966
import SignedDifferenceSets.KleinTomographyRows.N51967
import SignedDifferenceSets.KleinTomographyRows.N51968
import SignedDifferenceSets.KleinTomographyRows.N51969
import SignedDifferenceSets.KleinTomographyRows.N51972
import SignedDifferenceSets.KleinTomographyRows.N51973
import SignedDifferenceSets.KleinTomographyRows.N51975
import SignedDifferenceSets.KleinTomographyRows.N51976
import SignedDifferenceSets.KleinTomographyRows.N51977
import SignedDifferenceSets.KleinTomographyRows.N51978
import SignedDifferenceSets.KleinTomographyRows.N61808
import SignedDifferenceSets.KleinTomographyRows.N61810
import SignedDifferenceSets.KleinTomographyRows.N61828
import SignedDifferenceSets.KleinTomographyRows.N61830
import SignedDifferenceSets.KleinTomographyRows.N64703
import SignedDifferenceSets.KleinTomographyRows.N64704
import SignedDifferenceSets.KleinTomographyRows.N64960
import SignedDifferenceSets.KleinTomographyRows.N64961
import SignedDifferenceSets.KleinTomographyRows.N64962
import SignedDifferenceSets.KleinTomographyRows.N64963

open SignedDifferenceSets

example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 54) 189 20 := SignedDifferenceSets.KleinTomographyRows.N11534.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 6 × ZMod 18) 189 20 := SignedDifferenceSets.KleinTomographyRows.N11535.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 6 × ZMod 12) 189 20 := SignedDifferenceSets.KleinTomographyRows.N11538.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 6 × ZMod 6) 189 20 := SignedDifferenceSets.KleinTomographyRows.N11540.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 36) 189 20 := SignedDifferenceSets.KleinTomographyRows.N11541.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 120) 187 18 := SignedDifferenceSets.KleinTomographyRows.N14164.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 60) 187 18 := SignedDifferenceSets.KleinTomographyRows.N14165.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 36) 189 20 := SignedDifferenceSets.KleinTomographyRows.N22020.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 6 × ZMod 12) 189 20 := SignedDifferenceSets.KleinTomographyRows.N22021.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 72) 189 20 := SignedDifferenceSets.KleinTomographyRows.N22022.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 36) 189 20 := SignedDifferenceSets.KleinTomographyRows.N22023.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 6 × ZMod 24) 189 20 := SignedDifferenceSets.KleinTomographyRows.N22024.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 12 × ZMod 12) 189 20 := SignedDifferenceSets.KleinTomographyRows.N22025.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 72) 189 20 := SignedDifferenceSets.KleinTomographyRows.N22028.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 48) 189 20 := SignedDifferenceSets.KleinTomographyRows.N22029.not_hasSDS
example : ¬ HasSDS (ZMod 12 × ZMod 24) 189 20 := SignedDifferenceSets.KleinTomographyRows.N22030.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 6 × ZMod 6) 237 68 := SignedDifferenceSets.KleinTomographyRows.N28407.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 6 × ZMod 18) 237 68 := SignedDifferenceSets.KleinTomographyRows.N28409.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 54) 237 68 := SignedDifferenceSets.KleinTomographyRows.N28411.not_hasSDS
example : ¬ HasSDS (ZMod 18 × ZMod 18) 237 68 := SignedDifferenceSets.KleinTomographyRows.N28413.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 6 × ZMod 6) 263 94 := SignedDifferenceSets.KleinTomographyRows.N28497.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 6 × ZMod 18) 263 94 := SignedDifferenceSets.KleinTomographyRows.N28499.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 54) 263 94 := SignedDifferenceSets.KleinTomographyRows.N28501.not_hasSDS
example : ¬ HasSDS (ZMod 18 × ZMod 18) 263 94 := SignedDifferenceSets.KleinTomographyRows.N28503.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 168) 301 132 := SignedDifferenceSets.KleinTomographyRows.N30796.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 84) 301 132 := SignedDifferenceSets.KleinTomographyRows.N30797.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 180) 181 12 := SignedDifferenceSets.KleinTomographyRows.N35300.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 60) 181 12 := SignedDifferenceSets.KleinTomographyRows.N35302.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 24) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40502.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 4 × ZMod 12) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40503.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 48) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40504.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 4 × ZMod 24) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40505.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 96) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40506.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 4 × ZMod 12) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40507.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 48) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40508.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 8 × ZMod 24) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40509.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 4 × ZMod 24) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40511.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 96) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40512.not_hasSDS
example : ¬ HasSDS (ZMod 8 × ZMod 48) 203 34 := SignedDifferenceSets.KleinTomographyRows.N40513.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 96) 357 188 := SignedDifferenceSets.KleinTomographyRows.N41211.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 48) 357 188 := SignedDifferenceSets.KleinTomographyRows.N41213.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 8 × ZMod 24) 357 188 := SignedDifferenceSets.KleinTomographyRows.N41214.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 4 × ZMod 24) 357 188 := SignedDifferenceSets.KleinTomographyRows.N41216.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 96) 357 188 := SignedDifferenceSets.KleinTomographyRows.N41217.not_hasSDS
example : ¬ HasSDS (ZMod 8 × ZMod 48) 357 188 := SignedDifferenceSets.KleinTomographyRows.N41218.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 210) 207 38 := SignedDifferenceSets.KleinTomographyRows.N49387.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 54) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51965.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 6 × ZMod 18) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51966.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 108) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51967.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 6 × ZMod 6 × ZMod 6) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51968.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 6 × ZMod 36) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51969.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 6 × ZMod 24) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51972.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 12 × ZMod 12) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51973.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 108) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51975.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 6 × ZMod 12) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51976.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 72) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51977.not_hasSDS
example : ¬ HasSDS (ZMod 12 × ZMod 36) 179 10 := SignedDifferenceSets.KleinTomographyRows.N51978.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 234) 273 104 := SignedDifferenceSets.KleinTomographyRows.N61808.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 78) 273 104 := SignedDifferenceSets.KleinTomographyRows.N61810.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 234) 299 130 := SignedDifferenceSets.KleinTomographyRows.N61828.not_hasSDS
example : ¬ HasSDS (ZMod 6 × ZMod 78) 299 130 := SignedDifferenceSets.KleinTomographyRows.N61830.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 240) 231 62 := SignedDifferenceSets.KleinTomographyRows.N64703.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 120) 231 62 := SignedDifferenceSets.KleinTomographyRows.N64704.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 120) 365 196 := SignedDifferenceSets.KleinTomographyRows.N64960.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 60) 365 196 := SignedDifferenceSets.KleinTomographyRows.N64961.not_hasSDS
example : ¬ HasSDS (ZMod 2 × ZMod 240) 365 196 := SignedDifferenceSets.KleinTomographyRows.N64962.not_hasSDS
example : ¬ HasSDS (ZMod 4 × ZMod 120) 365 196 := SignedDifferenceSets.KleinTomographyRows.N64963.not_hasSDS

#print axioms SignedDifferenceSets.KleinTomography.twist_autocorr_of_isSDS
#print axioms SignedDifferenceSets.KleinTomography.four_dvd_sum_twists
#print axioms SignedDifferenceSets.KleinTomography.two_dvd_twist_sub
#print axioms SignedDifferenceSets.KleinTomography.klein_demands
#print axioms SignedDifferenceSets.KleinTomography.false_of_kleinKill
#print axioms SignedDifferenceSets.KleinTomography.not_hasSDS_of_kleinKills
#print axioms SignedDifferenceSets.KleinTomography.KleinCert.not_hasSDS
#print axioms SignedDifferenceSets.Tests.KleinTomography.not_kleinKills_N170
#print axioms SignedDifferenceSets.Tests.KleinTomography.not_kleinKills_N931
#print axioms SignedDifferenceSets.Tests.KleinTomography.not_kleinKills_N934
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_216_189_20
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_240_187_18
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_288_189_20
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_324_237_68
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_324_263_94
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_336_301_132
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_360_181_12
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_384_203_34
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_384_357_188
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_420_207_38
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_432_179_10
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_468_273_104
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_468_299_130
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_480_231_62
#print axioms SignedDifferenceSets.KleinTomographyRows.Params.kills_480_365_196

/-- every row at once: collect axioms of a conjunction of all 67 statements -/
theorem all67 : (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 54) 189 20) ∧ (¬ HasSDS (ZMod 2 × ZMod 6 × ZMod 18) 189 20) ∧ (¬ HasSDS (ZMod 3 × ZMod 6 × ZMod 12) 189 20) ∧ (¬ HasSDS (ZMod 6 × ZMod 6 × ZMod 6) 189 20) ∧ (¬ HasSDS (ZMod 6 × ZMod 36) 189 20) ∧ (¬ HasSDS (ZMod 2 × ZMod 120) 187 18) ∧ (¬ HasSDS (ZMod 4 × ZMod 60) 187 18) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 36) 189 20) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 6 × ZMod 12) 189 20) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 72) 189 20) ∧ (¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 36) 189 20) ∧ (¬ HasSDS (ZMod 2 × ZMod 6 × ZMod 24) 189 20) ∧ (¬ HasSDS (ZMod 2 × ZMod 12 × ZMod 12) 189 20) ∧ (¬ HasSDS (ZMod 4 × ZMod 72) 189 20) ∧ (¬ HasSDS (ZMod 6 × ZMod 48) 189 20) ∧ (¬ HasSDS (ZMod 12 × ZMod 24) 189 20) ∧ (¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 6 × ZMod 6) 237 68) ∧ (¬ HasSDS (ZMod 3 × ZMod 6 × ZMod 18) 237 68) ∧ (¬ HasSDS (ZMod 6 × ZMod 54) 237 68) ∧ (¬ HasSDS (ZMod 18 × ZMod 18) 237 68) ∧ (¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 6 × ZMod 6) 263 94) ∧ (¬ HasSDS (ZMod 3 × ZMod 6 × ZMod 18) 263 94) ∧ (¬ HasSDS (ZMod 6 × ZMod 54) 263 94) ∧ (¬ HasSDS (ZMod 18 × ZMod 18) 263 94) ∧ (¬ HasSDS (ZMod 2 × ZMod 168) 301 132) ∧ (¬ HasSDS (ZMod 4 × ZMod 84) 301 132) ∧ (¬ HasSDS (ZMod 2 × ZMod 180) 181 12) ∧ (¬ HasSDS (ZMod 6 × ZMod 60) 181 12) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 24) 203 34) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 4 × ZMod 12) 203 34) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 48) 203 34) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 4 × ZMod 24) 203 34) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 96) 203 34) ∧ (¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 4 × ZMod 12) 203 34) ∧ (¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 48) 203 34) ∧ (¬ HasSDS (ZMod 2 × ZMod 8 × ZMod 24) 203 34) ∧ (¬ HasSDS (ZMod 4 × ZMod 4 × ZMod 24) 203 34) ∧ (¬ HasSDS (ZMod 4 × ZMod 96) 203 34) ∧ (¬ HasSDS (ZMod 8 × ZMod 48) 203 34) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 96) 357 188) ∧ (¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 48) 357 188) ∧ (¬ HasSDS (ZMod 2 × ZMod 8 × ZMod 24) 357 188) ∧ (¬ HasSDS (ZMod 4 × ZMod 4 × ZMod 24) 357 188) ∧ (¬ HasSDS (ZMod 4 × ZMod 96) 357 188) ∧ (¬ HasSDS (ZMod 8 × ZMod 48) 357 188) ∧ (¬ HasSDS (ZMod 2 × ZMod 210) 207 38) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 54) 179 10) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 6 × ZMod 18) 179 10) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 108) 179 10) ∧ (¬ HasSDS (ZMod 2 × ZMod 6 × ZMod 6 × ZMod 6) 179 10) ∧ (¬ HasSDS (ZMod 2 × ZMod 6 × ZMod 36) 179 10) ∧ (¬ HasSDS (ZMod 3 × ZMod 6 × ZMod 24) 179 10) ∧ (¬ HasSDS (ZMod 3 × ZMod 12 × ZMod 12) 179 10) ∧ (¬ HasSDS (ZMod 4 × ZMod 108) 179 10) ∧ (¬ HasSDS (ZMod 6 × ZMod 6 × ZMod 12) 179 10) ∧ (¬ HasSDS (ZMod 6 × ZMod 72) 179 10) ∧ (¬ HasSDS (ZMod 12 × ZMod 36) 179 10) ∧ (¬ HasSDS (ZMod 2 × ZMod 234) 273 104) ∧ (¬ HasSDS (ZMod 6 × ZMod 78) 273 104) ∧ (¬ HasSDS (ZMod 2 × ZMod 234) 299 130) ∧ (¬ HasSDS (ZMod 6 × ZMod 78) 299 130) ∧ (¬ HasSDS (ZMod 2 × ZMod 240) 231 62) ∧ (¬ HasSDS (ZMod 4 × ZMod 120) 231 62) ∧ (¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 120) 365 196) ∧ (¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 60) 365 196) ∧ (¬ HasSDS (ZMod 2 × ZMod 240) 365 196) ∧ (¬ HasSDS (ZMod 4 × ZMod 120) 365 196) :=
  ⟨SignedDifferenceSets.KleinTomographyRows.N11534.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N11535.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N11538.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N11540.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N11541.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N14164.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N14165.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N22020.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N22021.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N22022.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N22023.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N22024.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N22025.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N22028.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N22029.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N22030.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N28407.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N28409.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N28411.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N28413.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N28497.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N28499.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N28501.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N28503.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N30796.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N30797.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N35300.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N35302.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40502.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40503.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40504.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40505.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40506.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40507.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40508.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40509.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40511.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40512.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N40513.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N41211.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N41213.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N41214.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N41216.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N41217.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N41218.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N49387.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51965.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51966.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51967.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51968.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51969.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51972.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51973.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51975.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51976.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51977.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N51978.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N61808.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N61810.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N61828.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N61830.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N64703.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N64704.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N64960.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N64961.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N64962.not_hasSDS, SignedDifferenceSets.KleinTomographyRows.N64963.not_hasSDS⟩
#print axioms all67
