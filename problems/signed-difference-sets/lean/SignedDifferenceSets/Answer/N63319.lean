module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N63319: a (475, 241, 120) SDS in C₅ × C₉₅

Open in Gordon's table (`SDS(475,241,120,[5,95])`, 2026-11-05). The set is object O107
(`objects/O107.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 6 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N63319

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O107's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x961558903fb72ebcb7c333dd4f327711f30d4dbf5f0a04b6fd7c2812ea7993b88f986a6199e8961558903fb72ebcb7b08e3615e6429cd0158b0ad2

set_option linter.style.longLine false in
/-- Object O107's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O107: the sign of each element. -/
def sds : ZMod 5 × ZMod 95 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count :
    countOk (ZMod 5 × ZMod 95) 241 plus minus = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 78. -/
theorem shifts1 :
    allFrom (shiftOk (ZMod 5 × ZMod 95) 120 plus minus) 0 79 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 79 to 157. -/
theorem shifts2 :
    allFrom (shiftOk (ZMod 5 × ZMod 95) 120 plus minus) 79 79 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 158 to 236. -/
theorem shifts3 :
    allFrom (shiftOk (ZMod 5 × ZMod 95) 120 plus minus) 158 79 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 237 to 315. -/
theorem shifts4 :
    allFrom (shiftOk (ZMod 5 × ZMod 95) 120 plus minus) 237 79 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 316 to 394. -/
theorem shifts5 :
    allFrom (shiftOk (ZMod 5 × ZMod 95) 120 plus minus) 316 79 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 395 to 474. -/
theorem shifts6 :
    allFrom (shiftOk (ZMod 5 × ZMod 95) 120 plus minus) 395 80 =
      true := by
  decide +kernel

theorem isSDS : IsSDS 241 120 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  exact isSDS_of_checkSplit count h

/-- N63319: C₅ × C₉₅ has a signed difference set with
parameters (475, 241, 120). -/
theorem hasSDS :
    HasSDS (ZMod 5 × ZMod 95) 241 120 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N63319
