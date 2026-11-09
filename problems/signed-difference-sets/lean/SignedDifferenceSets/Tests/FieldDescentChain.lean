module

public import SignedDifferenceSets.Check
public import SignedDifferenceSets.FieldDescentChain

/-!
# Tests for P18 M2 (field descent along a chain)

Kills: N1289 (81, 64, 1) on `C₃ × C₂₇`, chain `27 → 9 → 3`; N3804 (128, 122, 22) on `C₂ × C₆₄`,
chain `64 → 32 → 16 → 8` at `p = 2`. Refused: a witness `t ≢ 1 + d / p (mod d)`, a prime of `n`
without a witness, a step with `p² ∤ d`, and a `p = 2` step with only `4 ∣ d`: N12202's chain
`224 → 112 → 56 → 28 → 14` would kill (Schmidt's case `(p, b) = (2, 1)`); its first three steps
are valid and the fourth is refused. Not killed: rows with known sets whose chains are valid but
whose bound fails: N131 (32, 20, 4) on `C₂ × C₁₆`, chain `16 → 8 → 4`; N129 (32, 20, 4) on
`C₂ × C₂ × C₈`; N1181 (80, 44, 8) and N26075 (312, 300, 200), two primes in `n`. On O13, N131's
known set, every hypothesis of `IsSDS.totient_mul_le_of_chain` holds (non-vacuity).
-/

@[expose] public section

namespace SignedDifferenceSets

/-- N1289: `m = 27`, `n = 63 = 3² · 7`; step `27 → 9`: `t = 10 ≡ 7⁶ (mod 27)`; step `9 → 3`:
`t = 4 ≡ 7⁸ (mod 27)`; `27 · 3 · 3² = 729 < φ(27) · 63 = 1134`. -/
example : ¬ HasSDS (ZMod 3 × ZMod 27) 64 1 :=
  FieldDescentChainCert.not_hasSDS (w := ⟨1289, [3, 27], 64, 1⟩)
    (c := ⟨27, [0, 1], [0, 1],
      [⟨3, [⟨3, 10, 3, 0⟩, ⟨7, 10, 0, 6⟩]⟩, ⟨3, [⟨3, 4, 3, 0⟩, ⟨7, 4, 0, 8⟩]⟩]⟩)
    (by decide +kernel) _

/-- N3804: `m = 64`, `n = 100 = 2² · 5`, three steps at `p = 2` (`8 ∣ 64, 32, 16`);
`64 · 8 · 2² = 2048 < φ(64) · 100 = 3200`. -/
example : ¬ HasSDS (ZMod 2 × ZMod 64) 122 22 :=
  FieldDescentChainCert.not_hasSDS (w := ⟨3804, [2, 64], 122, 22⟩)
    (c := ⟨64, [0, 1], [0, 1],
      [⟨2, [⟨2, 33, 6, 0⟩, ⟨5, 33, 0, 8⟩]⟩, ⟨2, [⟨2, 17, 6, 0⟩, ⟨5, 17, 0, 12⟩]⟩,
        ⟨2, [⟨2, 9, 6, 0⟩, ⟨5, 9, 0, 6⟩]⟩]⟩)
    (by decide +kernel) _

/-- N1289's chain with `t = 7 = 7¹` for `q = 7` at the first step: `7 ≢ 10 (mod 27)`. -/
example : ¬ FieldDescentChainCert.Kills ⟨1289, [3, 27], 64, 1⟩
    ⟨27, [0, 1], [0, 1],
      [⟨3, [⟨3, 10, 3, 0⟩, ⟨7, 7, 0, 1⟩]⟩, ⟨3, [⟨3, 4, 3, 0⟩, ⟨7, 4, 0, 8⟩]⟩]⟩ := by
  decide +kernel

/-- N1289's chain without a witness for `q = 7` at the first step. -/
example : ¬ FieldDescentChainCert.Kills ⟨1289, [3, 27], 64, 1⟩
    ⟨27, [0, 1], [0, 1], [⟨3, [⟨3, 10, 3, 0⟩]⟩, ⟨3, [⟨3, 4, 3, 0⟩, ⟨7, 4, 0, 8⟩]⟩]⟩ := by
  decide +kernel

/-- A third step `3 → 1` at `p = 3` is refused: `9 ∤ 3`. -/
example : ¬ DescentStepCert.Ok 27 63 3 ⟨3, [⟨3, 2, 3, 0⟩, ⟨7, 2, 0, 1⟩]⟩ := by decide +kernel

/-- N12202 (224, 112, 48), `n = 2⁶`: the steps `224 → 112 → 56 → 28` are valid. -/
example : StepsOk 224 64 224
    [⟨2, [⟨2, 113, 5, 0⟩]⟩, ⟨2, [⟨2, 57, 5, 0⟩]⟩, ⟨2, [⟨2, 29, 5, 0⟩]⟩] := by
  decide +kernel

/-- … but end too high: `224 · 28 = 6272 ≥ φ(224) · 64 = 6144`. -/
example : ¬ FieldDescentChainCert.Kills ⟨12202, [224], 112, 48⟩
    ⟨224, [1], [1], [⟨2, [⟨2, 113, 5, 0⟩]⟩, ⟨2, [⟨2, 57, 5, 0⟩]⟩, ⟨2, [⟨2, 29, 5, 0⟩]⟩]⟩ := by
  decide +kernel

/-- The step `28 → 14` would kill (`224 · 14 = 3136 < 6144`) and has its witness
`t = 15 ≡ 1 + 14 (mod 28)`, `15 ≡ 2⁰ (mod 7)`, but only `4 ∣ 28`. -/
example : 224 * 14 * 1 ^ 2 < Nat.totient 224 * 64 := by decide +kernel

example : ¬ DescentStepCert.Ok 224 64 28 ⟨2, [⟨2, 15, 5, 0⟩]⟩ := by decide +kernel

example : ¬ FieldDescentChainCert.Kills ⟨12202, [224], 112, 48⟩
    ⟨224, [1], [1], [⟨2, [⟨2, 113, 5, 0⟩]⟩, ⟨2, [⟨2, 57, 5, 0⟩]⟩, ⟨2, [⟨2, 29, 5, 0⟩]⟩,
      ⟨2, [⟨2, 15, 5, 0⟩]⟩]⟩ := by
  decide +kernel

/-- N131 exists: on `C₁₆`, `n = 16`, the chain `16 → 8 → 4` is valid, but `c = 2` and
`16 · 4 · 2² = 256 ≥ φ(16) · 16 = 128`. -/
example : StepsOk 16 16 16 [⟨2, [⟨2, 9, 4, 0⟩]⟩, ⟨2, [⟨2, 5, 4, 0⟩]⟩] := by decide +kernel

example : ¬ FieldDescentChainCert.Kills ⟨131, [2, 16], 20, 4⟩
    ⟨16, [0, 1], [0, 1], [⟨2, [⟨2, 9, 4, 0⟩]⟩, ⟨2, [⟨2, 5, 4, 0⟩]⟩]⟩ := by
  decide +kernel

/-- O13, a (32, 20, 4) SDS in `C₂ × C₁₆` (N131). -/
def sds32 : ZMod 2 × ZMod 16 → SignType := fun x =>
  if x.1 = 0 then ![1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, -1, 0, 1, -1] x.2
  else ![1, 1, 1, 0, 1, 1, 0, -1, 1, 1, 1, 0, -1, 1, 0, 1] x.2

/-- The chain theorem's hypotheses hold on O13 (non-vacuity): the quotient `C₁₆`, `c = 2`, the
chain `16 → 8 → 4`; its bound `φ(16) · 16 = 128 ≤ 16 · 4 · 2² = 256` holds. -/
example : (Nat.totient 16 : ℤ) * ((20 : ℕ) - (4 : ℤ)) ≤
    ((16 : ℕ) : ℤ) * (([2, 2].foldl (· / ·) 16 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) ^ 2 :=
  IsSDS.totient_mul_le_of_chain (show IsSDS 20 4 sds32 by decide +kernel) (m := 16)
    (by norm_num) (AddMonoidHom.snd _ _) Prod.snd_surjective
    (by rw [Fintype.card_prod, ZMod.card, ZMod.card]) (by norm_num) [2, 2]
    (StepsOk.descentChain (by decide) 16 [⟨2, [⟨2, 9, 4, 0⟩]⟩, ⟨2, [⟨2, 5, 4, 0⟩]⟩]
      (by decide +kernel))

/-- N129 exists: on `C₈`, `8 → 4` is valid, but `8 · 4 · 4² ≥ φ(8) · 16`. -/
example : ¬ FieldDescentChainCert.Kills ⟨129, [2, 2, 8], 20, 4⟩
    ⟨8, [0, 0, 1], [0, 0, 1], [⟨2, [⟨2, 5, 3, 0⟩]⟩]⟩ := by
  decide +kernel

/-- N1181 exists: on `C₁₆`, `n = 36`, `16 → 8` is valid (`9 = 3²`), but
`16 · 8 · 5² ≥ φ(16) · 36`. -/
example : StepsOk 16 36 16 [⟨2, [⟨2, 9, 4, 0⟩, ⟨3, 9, 0, 2⟩]⟩] := by decide +kernel

example : ¬ FieldDescentChainCert.Kills ⟨1181, [80], 44, 8⟩
    ⟨16, [1], [1], [⟨2, [⟨2, 9, 4, 0⟩, ⟨3, 9, 0, 2⟩]⟩]⟩ := by
  decide +kernel

/-- N26075 exists: on `C₈`, `n = 100`, `8 → 4` is valid (`5 = 5¹`), but
`8 · 4 · 39² ≥ φ(8) · 100`. -/
example : ¬ FieldDescentChainCert.Kills ⟨26075, [312], 300, 200⟩
    ⟨8, [1], [1], [⟨2, [⟨2, 5, 3, 0⟩, ⟨5, 5, 0, 1⟩]⟩]⟩ := by
  decide +kernel

end SignedDifferenceSets
