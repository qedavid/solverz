import SignedDifferenceSets.MaDividedCounts
import SignedDifferenceSets.MaDividedRes
import SignedDifferenceSets.Tests.MaDividedCounts
import SignedDifferenceSets.Tests.MaDividedRes
import SignedDifferenceSets.MaCountRows.N11250
import SignedDifferenceSets.MaCountRows.N11259
import SignedDifferenceSets.MaCountRows.N11493
import SignedDifferenceSets.MaCountRows.N11565
import SignedDifferenceSets.MaCountRows.N27066
import SignedDifferenceSets.MaCountRows.N33767
import SignedDifferenceSets.MaCountRows.N33769
import SignedDifferenceSets.MaCountRows.N33770
import SignedDifferenceSets.MaCountRows.N33881
import SignedDifferenceSets.MaCountRows.N33895
import SignedDifferenceSets.MaCountRows.N34201
import SignedDifferenceSets.MaCountRows.N34203
import SignedDifferenceSets.MaCountRows.N34204
import SignedDifferenceSets.MaCountRows.N34231
import SignedDifferenceSets.MaCountRows.N40375
import SignedDifferenceSets.MaCountRows.N41125
import SignedDifferenceSets.MaCountRows.N41305
import SignedDifferenceSets.MaCountRows.N48360
import SignedDifferenceSets.MaCountRows.N48374
import SignedDifferenceSets.MaCountRows.N48752
import SignedDifferenceSets.MaCountRows.N48850
import SignedDifferenceSets.MaCountRows.N51792
import SignedDifferenceSets.MaCountRows.N51793
import SignedDifferenceSets.MaCountRows.N51796
import SignedDifferenceSets.MaCountRows.N51882
import SignedDifferenceSets.MaCountRows.N51887
import SignedDifferenceSets.MaCountRows.N51912
import SignedDifferenceSets.MaCountRows.N51917
import SignedDifferenceSets.MaCountRows.N51987
import SignedDifferenceSets.MaCountRows.N51992
import SignedDifferenceSets.MaCountRows.N52002
import SignedDifferenceSets.MaCountRows.N52007
import SignedDifferenceSets.MaCountRows.N52452
import SignedDifferenceSets.MaCountRows.N52457
import SignedDifferenceSets.MaCountRows.N52587
import SignedDifferenceSets.MaCountRows.N52592
import SignedDifferenceSets.MaCountRows.N52902
import SignedDifferenceSets.MaCountRows.N52903
import SignedDifferenceSets.MaCountRows.N52906
import SignedDifferenceSets.MaCountRows.N52962
import SignedDifferenceSets.MaCountRows.N52967
import SignedDifferenceSets.MaCountRows.N58698
import SignedDifferenceSets.MaCountRows.N58699
import SignedDifferenceSets.MaCountRows.N58707
import SignedDifferenceSets.MaCountRows.N58708
import SignedDifferenceSets.MaCountRows.N58827
import SignedDifferenceSets.MaCountRows.N58828
import SignedDifferenceSets.MaCountRows.N5887
import SignedDifferenceSets.MaCountRows.N6055
import SignedDifferenceSets.MaCountRows.N60667
import SignedDifferenceSets.MaCountRows.N7340
import SignedDifferenceSets.MaCountRows.N7450
import SignedDifferenceSets.MaDividedResRows.N22390
import SignedDifferenceSets.MaDividedResRows.N22392
import SignedDifferenceSets.MaDividedResRows.N25970
import SignedDifferenceSets.MaDividedResRows.N26009
import SignedDifferenceSets.MaDividedResRows.N31317
import SignedDifferenceSets.MaDividedResRows.N43597
import SignedDifferenceSets.MaDividedResRows.N43641
import SignedDifferenceSets.MaDividedResRows.N43697
import SignedDifferenceSets.MaDividedResRows.N43761
import SignedDifferenceSets.MaDividedResRows.N46887
import SignedDifferenceSets.MaDividedResRows.N46914
import SignedDifferenceSets.MaDividedResRows.N61800
import SignedDifferenceSets.MaDividedResRows.N61885
import SignedDifferenceSets.MaDividedResRows.N61887

/-! Refuter probe (c38): the axioms of the core theorems, the C21/C5 steps they use and all 66 rows, summarised. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let core : List Name := [``SignedDifferenceSets.Ma.dvd_contract_sub, ``SignedDifferenceSets.Ma.dvd_contract_quot,
    ``SignedDifferenceSets.Ma.dvd_contract_quot_sub, ``SignedDifferenceSets.IsSDS.contract_congr_pow,
    ``SignedDifferenceSets.IsSDS.exists_divided_of_dvd, ``SignedDifferenceSets.IsSDS.exists_divided,
    ``SignedDifferenceSets.IsSDS.exists_divided2, ``SignedDifferenceSets.countsGo_of,
    ``SignedDifferenceSets.anyCountsMag_of, ``SignedDifferenceSets.DividedDemands.false_of_anyCountsMag,
    ``SignedDifferenceSets.MaCountCert.not_hasSDS, ``SignedDifferenceSets.goRes_sound,
    ``SignedDifferenceSets.noVectorRes_sound, ``SignedDifferenceSets.false_of_noVectorResQ',
    ``SignedDifferenceSets.IsSDS.prod_dvd_divided_sub, ``SignedDifferenceSets.IsSDS.false_of_maDividedRes,
    ``SignedDifferenceSets.MaDivResCert.not_hasSDS]
  let rows : List Name := [
    `SignedDifferenceSets.MaCountRows.N11250.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N11259.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N11493.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N11565.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N27066.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N33767.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N33769.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N33770.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N33881.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N33895.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N34201.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N34203.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N34204.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N34231.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N40375.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N41125.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N41305.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N48360.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N48374.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N48752.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N48850.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N51792.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N51793.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N51796.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N51882.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N51887.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N51912.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N51917.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N51987.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N51992.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52002.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52007.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52452.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52457.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52587.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52592.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52902.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52903.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52906.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52962.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N52967.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N58698.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N58699.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N58707.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N58708.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N58827.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N58828.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N5887.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N6055.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N60667.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N7340.not_hasSDS,
    `SignedDifferenceSets.MaCountRows.N7450.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N22390.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N22392.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N25970.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N26009.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N31317.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N43597.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N43641.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N43697.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N43761.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N46887.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N46914.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N61800.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N61885.not_hasSDS,
    `SignedDifferenceSets.MaDividedResRows.N61887.not_hasSDS]
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array String := #[]
  let mut n : Nat := 0
  for c in core ++ rows do
    unless (← getEnv).contains c do bad := bad.push s!"missing {c}"
    let axs ← Lean.collectAxioms c
    n := n + 1
    for a in axs do
      unless std.contains a do bad := bad.push s!"{c}: {a}"
  logInfo (s!"checked {n} constants ({core.length} core, {rows.length} rows); non-standard: {bad}")

#check @SignedDifferenceSets.MaCountRows.N40375.not_hasSDS
#check @SignedDifferenceSets.MaDividedResRows.N61887.not_hasSDS
#print axioms SignedDifferenceSets.MaCountRows.N5887.not_hasSDS
#print axioms SignedDifferenceSets.MaDividedResRows.N22390.not_hasSDS
