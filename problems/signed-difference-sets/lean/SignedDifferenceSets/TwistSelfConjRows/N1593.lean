module

public import SignedDifferenceSets.TwistSelfConj

/-!
# N1593: no SDS (90, 72, 8) in ZMod 3 × ZMod 30 (I23, self-conjugacy on the twist)

The forms `(b mod 2, a mod 3, b mod 3)` map `ZMod 3 × ZMod 30` onto `ZMod 2 × ZMod 3 × ZMod 3`
(fibres of 5); `k − λ = 64`, so the contraction to `ZMod 3 × ZMod 3` and its twist are constant
mod 8 (`TwistBox.not_hasSDS_grp_90_72_8`).
-/

@[expose] public section

namespace SignedDifferenceSets.TwistSelfConjRows.N1593

/-- N1593: `ZMod 3 × ZMod 30` has no signed difference set with parameters (90, 72, 8). -/
theorem not_hasSDS : ¬ HasSDS (ZMod 3 × ZMod 30) 72 8 :=
  TwistBox.not_hasSDS_grp_90_72_8 (ms := [3, 30]) (A := [[0, 1], [1, 0], [0, 1]])
    (P := [[0, 3], [1, 0], [0, 4]]) (by decide) (by decide) (by decide) _

end SignedDifferenceSets.TwistSelfConjRows.N1593
