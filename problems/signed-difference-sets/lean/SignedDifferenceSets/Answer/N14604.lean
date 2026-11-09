module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N14604: a (243, 122, 59) SDS in C₃ × C₃ × C₃ × C₃ × C₃

Open in Gordon's table (`SDS(243,122,59,[3,3,3,3,3])`, 2026-11-05). The set is object O105
(`objects/O105.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 2 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N14604

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O105's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x2f08a8e0b26a9cf0b961136f9d0fd03b993195f9b55f4b7e0ce448203bfc2

set_option linter.style.longLine false in
/-- Object O105's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O105: the sign of each element. -/
def sds : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count :
    countOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 122 plus minus = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 120. -/
theorem shifts1 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 59 plus minus) 0 121 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 121 to 242. -/
theorem shifts2 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 59 plus minus) 121 122 =
      true := by
  decide +kernel

theorem isSDS : IsSDS 122 59 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  exact isSDS_of_checkSplit count h

/-- N14604: C₃ × C₃ × C₃ × C₃ × C₃ has a signed difference set with
parameters (243, 122, 59). -/
theorem hasSDS :
    HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 122 59 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N14604
