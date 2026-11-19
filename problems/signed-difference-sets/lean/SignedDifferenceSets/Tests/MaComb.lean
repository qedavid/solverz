module

public import SignedDifferenceSets.MaCombRows
public import SignedDifferenceSets.Answer.N449

/-!
# Tests for C29's rule and row checks (`MaComb`, `MaCombRows`)

`maCombRule` without extra primes is `MaRule`. Row N9200 (`SDS(195, 115, 15)` in `ℤ₁₉₅`) is
killed (`p^b Q = 5 · 2 > 6 = 2c`), but not by C21 alone (`p^b = 5 ≤ 6`); certificates that
repeat a prime, overstate `j_q` or are not self-conjugate are refused. The existing sets
`SDS(54, 38, 2)` in `ℤ₃ × ℤ₁₈` (N449, checked in Lean) and `SDS(80, 44, 8)` in `ℤ₈₀` (N1181,
Gordon's table) meet every hypothesis but the bound (`6 ≤ 12`, `6 ≤ 16`) and are not killed.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

/-- C29 with no extra prime is C21. -/
example : MaRule := by
  intro G K _ _ _ _ _ p r i e b c k lam _ _ φ hφ hcard hr hi hc hn hk hb hpb hcert
  exact maCombRule G K p r i e b c k lam [] φ hφ hcard hr hi hc hn hk hb (by simp) (by simp)
    (by simpa using hpb) hcert

/-! Row N9200: `ℤ₁₉₅ → ℤ₅ × ℤ₁₃`, `p = 5` (`5² ≡ −1 mod 13`), `k − λ = 100`, `b = 1`, `c = 3`;
`q = 2` (`2⁶ ≡ −1 mod 65`, `2² ∣ 100`), `Q = 2`. -/

/-- Row N9200. -/
def rowN9200 : Row := ⟨9200, [195], 115, 15⟩

/-- Its certificate. -/
def certN9200 : MaCombCert := ⟨5, 1, 2, 2, 1, [13], [[1], [1]], [[26], [40]], [(2, 6, 1)]⟩

example : certN9200.Kills rowN9200 := by decide +kernel

example : ¬ HasSDS (ZMod 195) 115 15 :=
  MaCombCert.not_hasSDS (w := ⟨9200, [195], 115, 15⟩) (c := certN9200) (by decide +kernel) _

example : ¬ HasSDS (ZMod 195) 115 15 := MaCombRows.n9200_not_hasSDS

/-- Without `q = 2` the hypotheses hold but `p^b = 5 ≤ 6 = 2c`: C21 alone does not kill it. -/
example : ({ certN9200 with qs := [] } : MaCombCert).Valid rowN9200 ∧
    ¬ ({ certN9200 with qs := [] } : MaCombCert).Kills rowN9200 := by decide +kernel

/-- `q = 2` twice (`Q = 4` would pass the bound) is refused. -/
example : ¬ ({ certN9200 with qs := [(2, 6, 1), (2, 6, 1)] } : MaCombCert).Kills rowN9200 := by
  decide +kernel

/-- `2⁴ ∤ 100`: `j_q = 2` is refused. -/
example : ¬ ({ certN9200 with qs := [(2, 6, 2)] } : MaCombCert).Kills rowN9200 := by
  decide +kernel

/-- `2³ ≢ −1 mod 65`: a wrong `i_q` is refused. -/
example : ¬ ({ certN9200 with qs := [(2, 3, 1)] } : MaCombCert).Kills rowN9200 := by
  decide +kernel

/-- `q = 5` divides `|H|`: refused. -/
example : ¬ ({ certN9200 with qs := [(5, 2, 1)] } : MaCombCert).Kills rowN9200 := by
  decide +kernel

/-! Existing sets: every hypothesis holds, the bound fails. -/

/-- `SDS(54, 38, 2)` in `ℤ₃ × ℤ₁₈` (N449): `ℤ₃ × ℤ₁₈ → ℤ₉`, `p = 3`, `b = 1`, `c = 6`, `q = 2`
(`2³ ≡ −1 mod 9`), `p^b Q = 6 ≤ 12 = 2c`. -/
def certN449 : MaCombCert := ⟨3, 3, 1, 2, 1, [1], [[0, 1], [0, 1]], [[0, 1], [0, 0]], [(2, 3, 1)]⟩

example : HasSDS (ZMod 3 × ZMod 18) 38 2 ∧ certN449.Valid ⟨449, [3, 18], 38, 2⟩ ∧
    ¬ certN449.Kills ⟨449, [3, 18], 38, 2⟩ :=
  ⟨Answer.N449.hasSDS, by decide +kernel, by decide +kernel⟩

/-- `SDS(80, 44, 8)` in `ℤ₈₀` (N1181): `ℤ₈₀ → ℤ₂ × ℤ₅`, `p = 2`, `b = 1`, `c = 8`, `q = 3`
(`3² ≡ −1 mod 10`), `p^b Q = 6 ≤ 16 = 2c`. -/
def certN1181 : MaCombCert := ⟨2, 1, 2, 2, 1, [5], [[1], [1]], [[5], [6]], [(3, 2, 1)]⟩

example : certN1181.Valid ⟨1181, [80], 44, 8⟩ ∧ ¬ certN1181.Kills ⟨1181, [80], 44, 8⟩ := by
  decide +kernel

end SignedDifferenceSets.Tests
