module

public import SignedDifferenceSets.MaDividedRes

/-!
# Tests for C38 (the divided search with Turyn's residue class)

Controls where an SDS exists, so `MaDivResCert.Valid` holds and only the residue search can tell:
N449 (`SDS(54,38,2)` in `C₃ × C₁₈`) at `p = 3` with `M = 2` on `ZMod 3`, N286 (`SDS(45,37,1)` in
`C₃ × C₁₅`) at `p = 3` with `M = 2` on `ZMod 1 × ZMod 5`: the search finds a vector. At `p = 2`
(N449, `M = 3`) the bound list `[19, 18]` matters: bound 19 finds no vector, bound 18 does, and
`Valid` refuses `[19]` alone. Wrong certificates for N25970 are refused: one bound at `p = 2`,
`q^(2j) ∤ k − λ`, `q = p`, `q` not self-conjugate mod 13, `q` listed twice.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

-- N449 exists, `p = 3`, `H' = ZMod 3 × Grp [1]`, `M = 2`: valid; the search finds a vector.
example : (⟨3, 3, 1, 2, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], [12], 8, 4, 4,
    [(2, 1, 1)]⟩ : MaDivResCert).Valid ⟨449, [3, 18], 38, 2⟩ := by decide +kernel
example : noVectorRes (@Indexed.size (Grp [3, 1]) _ (Grp.indexed _ (by decide)))
    (@Indexed.addIdx (Grp [3, 1]) _ (Grp.indexed _ (by decide))) 6 8 4 12 4 2 = false := by
  decide +kernel

-- N286 exists, `p = 3`, `H' = Grp [1, 5]`, `M = 2`: valid; the search finds a vector.
example : (⟨3, 1, 2, 2, 1, [5], [[1], [0, 1]], [[1], [0, 1]], [11], 5, 1, 3, [(2, 2, 1)]⟩ :
    MaDivResCert).Valid ⟨286, [3, 15], 37, 1⟩ := by decide +kernel
example : noVectorRes (@Indexed.size (Grp [1, 5]) _ (Grp.indexed _ (by decide)))
    (@Indexed.addIdx (Grp [1, 5]) _ (Grp.indexed _ (by decide))) 3 5 1 11 3 2 = false := by
  decide +kernel

-- N449 exists, `p = 2`, `H' = Grp [1, 1]`, `M = 3`: bound 19 alone would kill it, so `Valid`
-- needs both bounds, and bound 18 finds the vector.
example : (⟨2, 1, 1, 2, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], [19, 18], 36, 27, 6,
    [(3, 1, 1)]⟩ : MaDivResCert).Valid ⟨449, [3, 18], 38, 2⟩ := by decide +kernel
example : ¬ (⟨2, 1, 1, 2, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], [19], 36, 27, 6,
    [(3, 1, 1)]⟩ : MaDivResCert).Valid ⟨449, [3, 18], 38, 2⟩ := by decide +kernel
example : noVectorRes (@Indexed.size (Grp [1, 1]) _ (Grp.indexed _ (by decide)))
    (@Indexed.addIdx (Grp [1, 1]) _ (Grp.indexed _ (by decide))) 27 36 27 19 6 3 = true := by
  decide +kernel
example : noVectorRes (@Indexed.size (Grp [1, 1]) _ (Grp.indexed _ (by decide)))
    (@Indexed.addIdx (Grp [1, 1]) _ (Grp.indexed _ (by decide))) 27 36 27 18 6 3 = false := by
  decide +kernel

-- N25970: its certificate is valid; one bound, `5⁴ ∤ 100`, `q = p`, `5¹ ≢ −1 mod 13`, a repeated
-- `q` are refused.
example : (⟨2, 2, 6, 2, 1, [13], [[1], [1]], [[13], [40]], [94, 93], 289, 264, 83,
    [(5, 2, 1)]⟩ : MaDivResCert).Valid ⟨25970, [312], 188, 88⟩ := by decide +kernel
example : ¬ (⟨2, 2, 6, 2, 1, [13], [[1], [1]], [[13], [40]], [94], 289, 264, 83,
    [(5, 2, 1)]⟩ : MaDivResCert).Valid ⟨25970, [312], 188, 88⟩ := by decide +kernel
example : ¬ (⟨2, 2, 6, 2, 1, [13], [[1], [1]], [[13], [40]], [94, 93], 289, 264, 83,
    [(5, 2, 2)]⟩ : MaDivResCert).Valid ⟨25970, [312], 188, 88⟩ := by decide +kernel
example : ¬ (⟨2, 2, 6, 2, 1, [13], [[1], [1]], [[13], [40]], [94, 93], 289, 264, 83,
    [(2, 1, 1)]⟩ : MaDivResCert).Valid ⟨25970, [312], 188, 88⟩ := by decide +kernel
example : ¬ (⟨2, 2, 6, 2, 1, [13], [[1], [1]], [[13], [40]], [94, 93], 289, 264, 83,
    [(5, 1, 1)]⟩ : MaDivResCert).Valid ⟨25970, [312], 188, 88⟩ := by decide +kernel
example : ¬ (⟨2, 2, 6, 2, 1, [13], [[1], [1]], [[13], [40]], [94, 93], 289, 264, 83,
    [(5, 2, 1), (5, 2, 1)]⟩ : MaDivResCert).Valid ⟨25970, [312], 188, 88⟩ := by decide +kernel

end SignedDifferenceSets.Tests
