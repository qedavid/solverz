import SignedDifferenceSets.TomographyQuotNC
import SignedDifferenceSets.TomographySplit
import SignedDifferenceSets.TomographyQuotRows.N1028
import SignedDifferenceSets.TomographyQuotRows.N15398
import SignedDifferenceSets.TomographyQuotRows.N15460
import SignedDifferenceSets.TomographyQuotRows.N15510
import SignedDifferenceSets.TomographyQuotRows.N23172
import SignedDifferenceSets.TomographyQuotRows.N31754
import SignedDifferenceSets.TomographyQuotRows.N31775
import SignedDifferenceSets.TomographyQuotRows.N31788
import SignedDifferenceSets.TomographyQuotRows.N31814
import SignedDifferenceSets.TomographyQuotRows.N31940
import SignedDifferenceSets.TomographyQuotRows.N31950
import SignedDifferenceSets.TomographyQuotRows.N32024
import SignedDifferenceSets.TomographyQuotRows.N32039
import SignedDifferenceSets.TomographyQuotRows.N32072
import SignedDifferenceSets.TomographyQuotRows.N32123
import SignedDifferenceSets.TomographyQuotRows.N32153
import SignedDifferenceSets.TomographyQuotRows.N32192
import SignedDifferenceSets.TomographyQuotRows.N35640
import SignedDifferenceSets.TomographyQuotRows.N4985
import SignedDifferenceSets.TomographyQuotRows.N5043
import SignedDifferenceSets.TomographyQuotRows.N5057
import SignedDifferenceSets.TomographyQuotRows.N54801
import SignedDifferenceSets.TomographyQuotRows.N54878
import SignedDifferenceSets.TomographyQuotRows.N8571

open SignedDifferenceSets

#print axioms Tomography.not_hasSDS_quot
#print axioms Tomography.not_hasSDS_quot_nc
#print axioms Tomography.not_hasSDS_grp
#print axioms Tomography.not_hasSDS_grp_nc
#print axioms Tomography.fixed_lineQ
#print axioms Tomography.sum_contract_linesQ
#print axioms Tomography.exists_centeredQ
#print axioms Tomography.demands_lineQ
#print axioms Tomography.lists_of_orbSearch
#print axioms Tomography.lists_of_inSearch
#print axioms Tomography.lists_all_of_inSearch
#print axioms Tomography.closes_of_ptOK
#print axioms Tomography.closes_of_tomoGoL
#print axioms Tomography.inPart_of_top
#print axioms Tomography.tomoGoL_of_top
#print axioms Tomography.no_choiceL
#print axioms IsSDS.exists_translate_fixed_contract'
#print axioms TomographyQuotRows.N1028.not_hasSDS
example : ¬ HasSDS (ZMod 5 × ZMod 15) 46 15 := TomographyQuotRows.N1028.not_hasSDS
#print axioms TomographyQuotRows.N15398.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 35) 108 9 := TomographyQuotRows.N15398.not_hasSDS
#print axioms TomographyQuotRows.N15460.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 35) 169 48 := TomographyQuotRows.N15460.not_hasSDS
#print axioms TomographyQuotRows.N15510.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 35) 208 17 := TomographyQuotRows.N15510.not_hasSDS
#print axioms TomographyQuotRows.N23172.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 42) 161 40 := TomographyQuotRows.N23172.not_hasSDS
#print axioms TomographyQuotRows.N31754.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 99 25 := TomographyQuotRows.N31754.not_hasSDS
#print axioms TomographyQuotRows.N31775.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 121 12 := TomographyQuotRows.N31775.not_hasSDS
#print axioms TomographyQuotRows.N31788.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 49) 139 5 := TomographyQuotRows.N31788.not_hasSDS
#print axioms TomographyQuotRows.N31814.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 157 6 := TomographyQuotRows.N31814.not_hasSDS
#print axioms TomographyQuotRows.N31940.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 229 38 := TomographyQuotRows.N31940.not_hasSDS
#print axioms TomographyQuotRows.N31950.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 49) 229 150 := TomographyQuotRows.N31950.not_hasSDS
#print axioms TomographyQuotRows.N32024.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 256 182 := TomographyQuotRows.N32024.not_hasSDS
#print axioms TomographyQuotRows.N32039.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 270 203 := TomographyQuotRows.N32039.not_hasSDS
#print axioms TomographyQuotRows.N32072.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 286 9 := TomographyQuotRows.N32072.not_hasSDS
#print axioms TomographyQuotRows.N32123.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 310 47 := TomographyQuotRows.N32123.not_hasSDS
#print axioms TomographyQuotRows.N32153.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 315 97 := TomographyQuotRows.N32153.not_hasSDS
#print axioms TomographyQuotRows.N32192.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 334 225 := TomographyQuotRows.N32192.not_hasSDS
#print axioms TomographyQuotRows.N35640.not_hasSDS
example : ¬ HasSDS (ZMod 19 × ZMod 19) 136 5 := TomographyQuotRows.N35640.not_hasSDS
#print axioms TomographyQuotRows.N4985.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 21) 41 4 := TomographyQuotRows.N4985.not_hasSDS
#print axioms TomographyQuotRows.N5043.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 21) 98 31 := TomographyQuotRows.N5043.not_hasSDS
#print axioms TomographyQuotRows.N5057.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 21) 110 1 := TomographyQuotRows.N5057.not_hasSDS
#print axioms TomographyQuotRows.N54801.not_hasSDS
example : ¬ HasSDS (ZMod 7 × ZMod 63) 324 8 := TomographyQuotRows.N54801.not_hasSDS
#print axioms TomographyQuotRows.N54878.not_hasSDS
example : ¬ HasSDS (ZMod 21 × ZMod 21) 356 40 := TomographyQuotRows.N54878.not_hasSDS
#print axioms TomographyQuotRows.N8571.not_hasSDS
example : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 21) 168 89 := TomographyQuotRows.N8571.not_hasSDS
