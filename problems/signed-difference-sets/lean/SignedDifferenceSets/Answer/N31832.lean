module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N31832: a (343, 172, 84) SDS in C₇ × C₇ × C₇

Open in Gordon's table (`SDS(343,172,84,[7,7,7])`, 2026-11-05). The set is object O106
(`objects/O106.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N31832

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O106's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x43670f3901ac1ea5043e8a5157f3667492a5dab6d199321225ae839fda84be77730f193ce6148be07daf16

set_option linter.style.longLine false in
/-- Object O106's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O106: the sign of each element. -/
def sds : ZMod 7 × ZMod 7 × ZMod 7 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count :
    countOk (ZMod 7 × ZMod 7 × ZMod 7) 172 plus minus = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 84. -/
theorem shifts1 :
    allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 84 plus minus) 0 85 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 85 to 170. -/
theorem shifts2 :
    allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 84 plus minus) 85 86 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 171 to 256. -/
theorem shifts3 :
    allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 84 plus minus) 171 86 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 257 to 342. -/
theorem shifts4 :
    allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 84 plus minus) 257 86 =
      true := by
  decide +kernel

theorem isSDS : IsSDS 172 84 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N31832: C₇ × C₇ × C₇ has a signed difference set with
parameters (343, 172, 84). -/
theorem hasSDS :
    HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 172 84 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N31832
