module

public import SignedDifferenceSets.KleinTomographyRows.Params
public import SignedDifferenceSets.Answer.N170
public import SignedDifferenceSets.Answer.N931
public import SignedDifferenceSets.Answer.N934

/-!
# Tests: Klein tomography (I23)

The kill must not fire on an `exists` row with a quotient `ZMod 2 × ZMod 2 × ZMod 3`: N170
(36, 11, 2) on `ZMod 6 × ZMod 6`, N931 and N934 (72, 40, 4) on `ZMod 2 × ZMod 6 × ZMod 6` and
`ZMod 6 × ZMod 12`. With the complete residue lists the twisted sums pass, and some contraction
to `ZMod 3` escapes the clash, so `kleinKill` is `false`; their objects give `¬ KleinKills`.
Broken inputs are refused: forms that are not onto, a form that is not a homomorphism, a residue
list missing a residue, a wrong `t`, bounds too small. Data from `solver/kleinrows.py --tests`.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.KleinTomography

open SignedDifferenceSets.KleinTomography SignedDifferenceSets.KleinTomographyRows

set_option maxRecDepth 100000

/-- The residues mod 4 of every twisted sum for `n = 9` (sum `±3`). -/
def R9 : List Triple :=
  [(0, 0, 1), (0, 0, 3), (0, 1, 0), (0, 3, 0), (1, 0, 0), (1, 2, 2), (2, 1, 2), (2, 2, 1),
    (2, 2, 3), (2, 3, 2), (3, 0, 0), (3, 2, 2)]

/-- The residues mod 4 of every twisted sum for `n = 36` (sum `±6`). -/
def R36 : List Triple := [(0, 0, 2), (0, 2, 0), (2, 0, 0)]

/-! N170 (36, 11, 2): `s = 9`, contraction square sum 33. -/

example : triplesOK 9 3 3 (fun d => decide (res4 d ∈ R9)) = true := by decide +kernel
example : triplesOK 9 (-3) 3 (fun d => decide (res4 d ∈ R9)) = true := by decide +kernel
example : triplesOK 33 9 5 (clash R9) = false := by decide +kernel
example : triplesOK 33 (-9) 5 (clash R9) = false := by decide +kernel
example : kleinKill 9 3 33 9 3 5 R9 = false := by decide +kernel

/-! N931, N934 (72, 40, 4): `s = 18`, contraction square sum 132. -/

example : triplesOK 36 6 6 (fun d => decide (res4 d ∈ R36)) = true := by decide +kernel
example : triplesOK 36 (-6) 6 (fun d => decide (res4 d ∈ R36)) = true := by decide +kernel
example : triplesOK 132 18 11 (clash R36) = false := by decide +kernel
example : triplesOK 132 (-18) 11 (clash R36) = false := by decide +kernel
example : kleinKill 36 6 132 18 6 11 R36 = false := by decide +kernel

/-! The objects: their rows have valid quotients, so their parameters are not killed. -/

theorem not_kleinKills_N170 : ¬ KleinKills 36 11 2 := fun h =>
  KleinCert.not_hasSDS (w := ⟨170, [6, 6], 11, 2⟩)
    (c := ⟨[[1], [0, 1], [1]], [[3, 0], [0, 1], [4, 0]]⟩)
    (by decide +kernel) (by decide) h _ Answer.N170.hasSDS

theorem not_kleinKills_N931 : ¬ KleinKills 72 40 4 := fun h =>
  KleinCert.not_hasSDS (w := ⟨931, [2, 6, 6], 40, 4⟩)
    (c := ⟨[[1], [0, 1], [0, 1]], [[1, 0, 0], [0, 3, 0], [0, 4, 0]]⟩)
    (by decide +kernel) (by decide) h _ Answer.N931.hasSDS

theorem not_kleinKills_N934 : ¬ KleinKills 72 40 4 := fun h =>
  KleinCert.not_hasSDS (w := ⟨934, [6, 12], 40, 4⟩)
    (c := ⟨[[1], [0, 1], [1]], [[3, 0], [0, 1], [4, 0]]⟩)
    (by decide +kernel) (by decide) h _ Answer.N934.hasSDS

/-! Broken certificates. -/

/-- Both characters the same: not onto `ZMod 2 × ZMod 2 × ZMod 3`. -/
example : ¬ KleinCert.Valid ⟨11534, [2, 2, 54], 189, 20⟩
    ⟨[[1], [1], [0, 0, 1]], [[1], [0, 1], [0, 0, 1]]⟩ := by decide +kernel

/-- `x ↦ x₂ mod 3` on `ZMod 2`: not a homomorphism. -/
example : ¬ KleinCert.Valid ⟨11534, [2, 2, 54], 189, 20⟩
    ⟨[[1], [0, 1], [0, 1]], [[1], [0, 1], [0, 0, 1]]⟩ := by decide +kernel

/-- A preimage that misses its unit vector. -/
example : ¬ KleinCert.Valid ⟨11534, [2, 2, 54], 189, 20⟩
    ⟨[[1], [0, 1], [0, 0, 1]], [[1], [0, 1], [0, 0, 2]]⟩ := by decide +kernel

/-- The row's own certificate. -/
example : KleinCert.Valid ⟨11534, [2, 2, 54], 189, 20⟩
    ⟨[[1], [0, 1], [0, 0, 1]], [[1], [0, 1], [0, 0, 1]]⟩ := by decide +kernel

/-- A residue list missing `(0, 0, 1)` (that of `(12, 4, −3)`). -/
example : kleinKill 169 13 1609 67 13 40 (Params.R169.erase (0, 0, 1)) = false := by
  decide +kernel

/-- `t² ≠ n`. -/
example : kleinKill 169 12 1609 67 13 40 Params.R169 = false := by decide +kernel

/-- Bounds too small: `169 < 13²` and `1609 < 40²` fail. -/
example : kleinKill 169 13 1609 67 12 40 Params.R169 = false := by decide +kernel
example : kleinKill 169 13 1609 67 13 39 Params.R169 = false := by decide +kernel

/-- The same data with the right bounds kills (216, 189, 20). -/
example : kleinKill 169 13 1609 67 13 40 Params.R169 = true := by decide +kernel

end SignedDifferenceSets.Tests.KleinTomography
