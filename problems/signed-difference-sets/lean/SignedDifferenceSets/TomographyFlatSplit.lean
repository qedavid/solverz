module

public import SignedDifferenceSets.TomographyFlat

/-!
# Splitting `flatKill` below its top levels (I23)

`flatTop` runs `flatGo`'s top `d` levels and leaves each node there (its sums `P`) to the list
`F`, checked in separate declarations; `flatKill_of_top` joins them (as `tomoGoL_of_top` does
for `tomoGoL`).
-/

@[expose] public section

namespace SignedDifferenceSets.TomographyFlat

/-- `flatGo`'s top `d` levels; a node `d` levels down, with sums `P`, is left to `F`. -/
def flatTop (k m : ℕ) (cs : List (ℤ × ℤ × ℤ)) (U W : List (List ℤ)) (F : List (List ℤ)) :
    ℕ → ℕ → List Level → List ℤ → Bool
  | 0, _, _, P => F.contains P
  | _ + 1, _, [], P => !decide (absSumOf m P cs ≤ k)
  | d + 1, u, (ix, L, H) :: rest, P => (optsAt U W u).all fun y =>
    !okAll (addVec P ix y) L H cs || flatTop k m cs U W F d (u - 1) rest (addVec P ix y)

/-- `flatGo` from its top `d` levels and the checks of the nodes they leave to `F`. -/
theorem flatGo_of_top {k m : ℕ} {cs : List (ℤ × ℤ × ℤ)} {U W : List (List ℤ)}
    {F : List (List ℤ)} : ∀ (d u : ℕ) (lv : List Level) (P : List ℤ),
      flatTop k m cs U W F d u lv P = true →
      (∀ P' ∈ F, flatGo k m cs U W (u - d) (lv.drop d) P' = true) →
      flatGo k m cs U W u lv P = true
  | 0, u, lv, P, h, hF => by
    simp only [flatTop, List.contains_iff_mem] at h
    simpa using hF P h
  | _ + 1, _, [], P, h, _ => by simpa only [flatTop, flatGo] using h
  | d + 1, u, (ix, L, H) :: rest, P, h, hF => by
    simp only [flatTop, List.all_eq_true] at h
    simp only [flatGo, List.all_eq_true]
    intro y hy
    rcases Bool.or_eq_true _ _ ▸ h y hy with h1 | h1
    · simp [h1]
    · simp only [Bool.or_eq_true]
      refine Or.inr (flatGo_of_top d (u - 1) rest _ h1 fun P' hP' => ?_)
      have := hF P' hP'
      rwa [List.drop_succ_cons, show u - (d + 1) = u - 1 - d by omega] at this

/-- `flatKill` from `flatTop` at the root and the checks of the nodes it leaves to `F`. -/
theorem flatKill_of_top {k m : ℕ} {cs : List (ℤ × ℤ × ℤ)} {U W : List (List ℤ)} {u d : ℕ}
    {L H : List ℤ} {lv : List Level} {F : List (List ℤ)}
    (h : flatTop k m cs U W F d u lv (List.replicate cs.length 0) = true)
    (hF : ∀ P' ∈ F, flatGo k m cs U W (u - d) (lv.drop d) P' = true) :
    flatKill k m cs U W u L H lv = true := by
  rw [flatKill, flatGo_of_top d u lv _ h hF, Bool.or_true]

end SignedDifferenceSets.TomographyFlat
