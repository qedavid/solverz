import SignedDifferenceSets.MarkedCountsInt

/-! Refuter checks for C6x: axioms, literal statement, search values. -/

open SignedDifferenceSets

#print axioms SignedDifferenceSets.not_hasSDS_of_counts
#print axioms SignedDifferenceSets.ScCert.not_hasSDS_of_countsKill
#print axioms SignedDifferenceSets.n27692_not_hasSDS
#print axioms SignedDifferenceSets.IsSDS.countsOk
#print axioms SignedDifferenceSets.anyCounts_of
#check @SignedDifferenceSets.n27692_not_hasSDS
#check @SignedDifferenceSets.not_hasSDS_of_counts

-- The statement's group is literally C₂ × C₄ × C₄₀ with the standard instances.
example : (¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 40) 306 162) = (¬ HasSDS (Grp [2, 4, 40]) 306 162) := rfl

#eval (classVals 3 0 10, classVals 3 1 10, classVals 3 2 10)
#eval (List.range 21).map fun n => maxMarked 10 ((n : ℤ) - 10)
#eval [(228 : ℤ), -228].map fun s => (List.range 3).map fun t =>
  anyCounts 10 (orderVals s (classVals 3 t 10)) 32 s 1764 306
#eval [(228 : ℤ), -228].map fun s => (List.range 3).map fun t =>
  anyCounts 10 (orderVals s (classVals 3 t 10)) 32 s 1764 304
#eval [(228 : ℤ), -228].map fun s => (List.range 3).map fun t =>
  anyCounts 10 (orderVals s (classVals 3 t 10)) 32 s 1764 305
-- Without orderVals (other order) the answer must not change.
#eval [(228 : ℤ), -228].map fun s => [anyCounts 10 (classVals 3 0 10) 32 s 1764 304,
  anyCounts 10 (classVals 3 0 10).reverse 32 s 1764 304,
  anyCounts 10 (classVals 3 0 10) 32 s 1764 305, anyCounts 10 (classVals 3 0 10).reverse 32 s 1764 305]
-- The kill's ingredients as the kernel sees them.
#eval ((⟨27692, [2, 4, 40], 306, 162⟩ : Row).ms.prod / (⟨3, 1, 1, [2, 4, 4], 228⟩ : ScCert).ds.prod,
  (306 : ℤ) + 162 * ((10 : ℤ) - 1), (228 : ℤ) ^ 2, (306 : ℤ) + 162 * (320 - 1))
example : (⟨3, 1, 1, [2, 4, 4], 228⟩ : ScCert).Valid ⟨27692, [2, 4, 40], 306, 162⟩ := by
  unfold ScCert.Valid; decide +kernel
