module

public import SignedDifferenceSets.TomographyQuot
public import SignedDifferenceSets.TomographyLast

/-!
# Tests for `TomographyLast`

N49 `(25, 12, 1)` on `C₅ × C₅` (an `exists` row): its line contractions (fibres of 5) are listed by
`inPartL` over every first coordinate, and `inPart_of_inPartL` turns that into `inSearch`; the same
list missing one vector is refused. `inPartL`'s last level is solved from the sum, so its leaves
are exactly `inPart`'s.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.TomographyLast

open Tomography

/-- N49's vectors with `|w₀|` largest (as in `Tests/TomographyQuot.lean`). -/
def v0N49 : List (List ℤ) :=
  [[3, -1, 1, 1, 2], [3, 1, -1, 2, 1], [3, 1, 2, -1, 1], [3, 2, 1, 1, -1]]

theorem hL : inPartL (Indexed.size (ZMod 5)) (Indexed.addIdx (ZMod 5)) (1 * 5 : ℕ)
    ((12 : ℕ) + (1 : ℤ) * ((1 * 5 : ℕ) - 1)) ((1 : ℤ) * (1 * 5 : ℕ)) (12 : ℕ) 6
    v0N49 (-5) 11 = true := by
  decide +kernel

example : inSearch (Indexed.size (ZMod 5)) (Indexed.addIdx (ZMod 5)) (1 * 5 : ℕ)
    ((12 : ℕ) + (1 : ℤ) * ((1 * 5 : ℕ) - 1)) ((1 : ℤ) * (1 * 5 : ℕ)) (12 : ℕ) 6
    v0N49 = true :=
  inSearch_of_inPart (inPart_of_inPartL hL) (by decide) (by decide)

/-- A list missing a vector is refused. -/
example : inPartL (Indexed.size (ZMod 5)) (Indexed.addIdx (ZMod 5)) (1 * 5 : ℕ)
    ((12 : ℕ) + (1 : ℤ) * ((1 * 5 : ℕ) - 1)) ((1 : ℤ) * (1 * 5 : ℕ)) (12 : ℕ) 6
    (v0N49.take 3) (-5) 11 = false := by
  decide +kernel

end SignedDifferenceSets.Tests.TomographyLast
