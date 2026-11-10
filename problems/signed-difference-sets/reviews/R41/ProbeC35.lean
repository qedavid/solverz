import SignedDifferenceSets.FieldDescentChainRows
import SignedDifferenceSets.Check

/-! Refuter probe for C35: statements, axioms, literal row theorems. -/

open SignedDifferenceSets

#check @IsSDS.totient_mul_le_of_chain
#check @FieldDescentChainCert.not_hasSDS
#check @fieldDescentChainRows_not_hasSDS
#print DescentStep
#print DescentChain
#print DescentStepCert.Ok
#print FieldDescentChainCert.Kills
#print axioms FieldDescent.fixedMod_of_smul_eq
#print axioms FieldDescent.exists_fixedMod_step
#print axioms FieldDescent.exists_fixedMod_next
#print axioms FieldDescent.exists_fixedMod_chain
#print axioms FieldDescent.totient_mul_le_of_chain_aux
#print axioms IsSDS.totient_mul_le_of_chain
#print axioms StepsOk.descentChain
#print axioms FieldDescentChainCert.not_hasSDS
#print axioms fieldDescentChainRows_kill
#print axioms fieldDescentChainRows_not_hasSDS
#print axioms fieldDescentChainKill_N1289
#print axioms fieldDescentChainKill_N3804
#print axioms fieldDescentChainKill_N56988
#print axioms fieldDescentChainKill_N67174

/-- Literal `¬ HasSDS` on the row's group: cyclic p = 2 row, C₂ × C₆₄, C₃ × C₁₆₂. -/
example : ¬ HasSDS (ZMod 448) 412 12 := FieldDescentChainCert.not_hasSDS fieldDescentChainKill_N56988 _
example : ¬ HasSDS (ZMod 2 × ZMod 64) 122 22 := FieldDescentChainCert.not_hasSDS fieldDescentChainKill_N3804 _
example : ¬ HasSDS (ZMod 3 × ZMod 162) 481 40 := FieldDescentChainCert.not_hasSDS fieldDescentChainKill_N67174 _
example : ¬ HasSDS (ZMod 3 × ZMod 81) 69 6 := FieldDescentChainCert.not_hasSDS fieldDescentChainKill_N14454 _

/-- Through the list theorem the researcher cites in `settle-m2.tsv`. -/
example : ¬ HasSDS (ZMod 3 × ZMod 27) 64 1 := by
  have h := @fieldDescentChainRows_not_hasSDS
    (⟨⟨1289, [3, 27], 64, 1⟩,
      ⟨27, [0, 1], [0, 1],
       [⟨3, [⟨3, 10, 3, 0⟩, ⟨7, 10, 0, 6⟩]⟩, ⟨3, [⟨3, 4, 3, 0⟩, ⟨7, 4, 0, 8⟩]⟩]⟩⟩)
    (by decide +kernel) inferInstance
  exact h

/-- A `p = 2` step with only `4 ∣ d` is not a `DescentStep` (d = 12, m = 12). -/
example : ¬ DescentStep 12 1 12 2 := by
  rintro ⟨-, -, h, -⟩
  rcases h with h | ⟨-, h⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
