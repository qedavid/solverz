module

public import SignedDifferenceSets.ContractionCheck
public import SignedDifferenceSets.LinearMaps
public import SignedDifferenceSets.SelfConjugacyCheck

/-!
# Klein tomography: quotients `ZMod 2 × ZMod 2 × K` (I23)

For `ε : G →+ ZMod 2` and `ψ : G →+ K`, the twisted coset sums
`twist ε ψ D h = Σ_{ψ x = h} (−1)^{ε x} D(x)` of an SDS have autocorrelation `k − λ` at `0` and
`0` elsewhere when `ε` is nontrivial on `ker ψ` (`twist_autocorr_of_isSDS`): square sum and
squared sum `n = k − λ`. On a quotient `φ : G →+ ZMod 2 × ZMod 2 × K`, with `z` the contraction
to `K` and `d₁, d₂, d₃` its twists by the three nontrivial characters of `ZMod 2 × ZMod 2`,
each `dᵢ ≡ z (mod 2)` and `z + d₁ + d₂ + d₃ = 4 W(0, 0, ·) ≡ 0 (mod 4)` (Fourier inversion;
`klein_demands`). For `K = ZMod 3`, `kleinKill` lists the residues mod 4 of every `d` (complete
by a bounded search) and checks that every `z` meeting C3's demands clashes with them
(`not_hasSDS_of_kleinKills`). `KleinCert` states it for the table's groups, `φ` given by forms
onto `Grp [2, 2, 3]`.
-/

@[expose] public section

namespace SignedDifferenceSets.KleinTomography

/-! ### Twisted contractions -/

/-- The character of `ZMod 2`: `1` at `0`, `−1` at `1`. -/
def bitSign (e : ZMod 2) : ℤ := if e = 0 then 1 else -1

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  revert a b; decide

theorem bitSign_mul_self (a : ZMod 2) : bitSign a * bitSign a = 1 := by
  revert a; decide

theorem two_dvd_bitSign_sub_one (a : ZMod 2) : (2 : ℤ) ∣ bitSign a - 1 := by
  revert a; decide

/-- Fourier inversion on `ZMod 2 × ZMod 2` at `0`: the four characters sum to `4` or `0`. -/
theorem four_dvd_bitSign_sum (a b : ZMod 2) :
    (4 : ℤ) ∣ 1 + bitSign a + bitSign b + bitSign (a + b) := by
  revert a b; decide

section Twist

variable {G K : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- The coset sums of `D` along `ψ` twisted by `ε`: `Σ_{ψ x = h} (−1)^{ε x} D(x)`. -/
def twist (ε : G →+ ZMod 2) (ψ : G →+ K) (D : G → SignType) (h : K) : ℤ :=
  ∑ x ∈ fibre ψ h, bitSign (ε x) * (D x : ℤ)

/-- The autocorrelation of the coset sums of any `f` at `g'` sums `f`'s autocorrelation over the
fibre of `g'` (`contract_autocorr_eq` for integer weights). -/
theorem sum_fibre_autocorr (f : G → ℤ) (ψ : G →+ K) (g' : K) :
    ∑ h, (∑ x ∈ fibre ψ h, f x) * (∑ y ∈ fibre ψ (h + g'), f y) =
      ∑ g ∈ fibre ψ g', ∑ x, f x * f (x + g) := by
  simp only [Finset.sum_mul_sum, fibre]
  calc ∑ h, ∑ x ∈ Finset.univ.filter (fun x => ψ x = h),
        ∑ y ∈ Finset.univ.filter (fun y => ψ y = h + g'), f x * f y
      = ∑ x, ∑ y ∈ Finset.univ.filter (fun y => ψ y = ψ x + g'), f x * f y := by
        rw [← Finset.sum_fiberwise Finset.univ (fun x => ψ x)
          (fun x => ∑ y ∈ Finset.univ.filter (fun y => ψ y = ψ x + g'), f x * f y)]
        refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x hx => ?_
        rw [(Finset.mem_filter.1 hx).2]
    _ = ∑ x, ∑ g ∈ Finset.univ.filter (fun g => ψ g = g'), f x * f (x + g) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        refine Finset.sum_nbij' (fun y => y - x) (fun g => x + g) ?_ ?_ ?_ ?_ ?_ <;>
          intro a ha <;> simp_all [map_sub, add_sub_cancel_left]
    _ = ∑ g ∈ Finset.univ.filter (fun g => ψ g = g'), ∑ x, f x * f (x + g) :=
        Finset.sum_comm

/-- The twisted autocorrelation weighs `D`'s autocorrelation at `g` by `(−1)^{ε g}`. -/
theorem twist_autocorr (ε : G →+ ZMod 2) (ψ : G →+ K) (D : G → SignType) (g' : K) :
    ∑ h, twist ε ψ D h * twist ε ψ D (h + g') =
      ∑ g ∈ fibre ψ g', bitSign (ε g) * ∑ x, (D x : ℤ) * D (x + g) := by
  refine (sum_fibre_autocorr (fun x => bitSign (ε x) * (D x : ℤ)) ψ g').trans
    (Finset.sum_congr rfl fun g _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  change bitSign (ε x) * (D x : ℤ) * (bitSign (ε (x + g)) * (D (x + g) : ℤ)) =
    bitSign (ε g) * ((D x : ℤ) * D (x + g))
  rw [map_add, bitSign_add]
  linear_combination (bitSign (ε g) * (D x : ℤ) * D (x + g)) * bitSign_mul_self (ε x)

omit [Fintype K] in
/-- A character of order 2 that is nontrivial on `ker ψ` sums to `0` over each fibre of `ψ`. -/
theorem sum_bitSign_fibre (ε : G →+ ZMod 2) (ψ : G →+ K) {u : G} (hu : ψ u = 0)
    (hεu : ε u = 1) (g' : K) : ∑ g ∈ fibre ψ g', bitSign (ε g) = 0 := by
  have hS : ∑ g ∈ fibre ψ g', bitSign (ε (g + u)) = ∑ g ∈ fibre ψ g', bitSign (ε g) :=
    Finset.sum_equiv (Equiv.addRight u) (fun g => by simp [fibre, hu]) (fun _ _ => rfl)
  have h1 : bitSign 1 = -1 := by decide
  simp only [map_add, hεu, bitSign_add, h1, mul_neg, mul_one, Finset.sum_neg_distrib] at hS
  linarith

theorem sum_mul_self_of_isSDS {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D) :
    ∑ x, (D x : ℤ) * D x = k := by
  rw [← hD.sum_abs]
  exact Finset.sum_congr rfl fun x _ => by cases D x <;> simp

/-- The twisted coset sums of an SDS have autocorrelation `k − λ` at `0` and `0` elsewhere,
when `ε` is nontrivial on `ker ψ`. -/
theorem twist_autocorr_of_isSDS {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (ε : G →+ ZMod 2) (ψ : G →+ K) {u : G} (hu : ψ u = 0) (hεu : ε u = 1) (g' : K) :
    ∑ h, twist ε ψ D h * twist ε ψ D (h + g') = if g' = 0 then (k : ℤ) - lam else 0 := by
  classical
  have hA : ∀ g : G, ∑ x, (D x : ℤ) * D (x + g) = lam + if g = 0 then (k : ℤ) - lam else 0 := by
    intro g
    split_ifs with hg
    · subst hg
      simp only [add_zero, sum_mul_self_of_isSDS hD]
      ring
    · rw [hD.2 g hg, add_zero]
  rw [twist_autocorr]
  simp only [hA, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_bitSign_fibre ε ψ hu hεu, zero_mul, zero_add]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hg' : g' = 0
  · subst hg'
    simp [fibre, bitSign]
  · have : (0 : G) ∉ fibre ψ g' := by simp [fibre, Ne.symm hg']
    simp [this, hg']

theorem twist_sq_of_isSDS {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (ε : G →+ ZMod 2) (ψ : G →+ K) {u : G} (hu : ψ u = 0) (hεu : ε u = 1) :
    ∑ h, twist ε ψ D h * twist ε ψ D h = (k : ℤ) - lam := by
  simpa using twist_autocorr_of_isSDS hD ε ψ hu hεu 0

theorem twist_sum_sq_of_isSDS {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (ε : G →+ ZMod 2) (ψ : G →+ K) {u : G} (hu : ψ u = 0) (hεu : ε u = 1) :
    (∑ h, twist ε ψ D h) * (∑ h, twist ε ψ D h) = (k : ℤ) - lam := by
  rw [sum_mul_sum_eq]
  simp only [twist_autocorr_of_isSDS hD ε ψ hu hεu]
  simp

omit [Fintype K] in
/-- A twisted sum has the parity of the contraction it twists. -/
theorem two_dvd_twist_sub (ε : G →+ ZMod 2) (ψ : G →+ K) (D : G → SignType) (h : K) :
    (2 : ℤ) ∣ twist ε ψ D h - contract ψ D h := by
  have e : twist ε ψ D h - contract ψ D h =
      ∑ x ∈ fibre ψ h, (bitSign (ε x) - 1) * (D x : ℤ) := by
    simp only [twist, contract, fibre, sub_mul, one_mul, Finset.sum_sub_distrib]
  rw [e]
  exact Finset.dvd_sum fun x _ => (two_dvd_bitSign_sub_one _).mul_right _

omit [Fintype K] in
/-- Fourier inversion on `ZMod 2 × ZMod 2`: the contraction and its three twists add up to four
times a coset sum. -/
theorem four_dvd_sum_twists (ε₁ ε₂ : G →+ ZMod 2) (ψ : G →+ K) (D : G → SignType) (h : K) :
    (4 : ℤ) ∣ contract ψ D h + twist ε₁ ψ D h + twist ε₂ ψ D h + twist (ε₁ + ε₂) ψ D h := by
  have e : contract ψ D h + twist ε₁ ψ D h + twist ε₂ ψ D h + twist (ε₁ + ε₂) ψ D h =
      ∑ x ∈ fibre ψ h,
        (1 + bitSign (ε₁ x) + bitSign (ε₂ x) + bitSign (ε₁ x + ε₂ x)) * (D x : ℤ) := by
    simp only [twist, contract, fibre, AddMonoidHom.add_apply, add_mul, one_mul,
      Finset.sum_add_distrib]
  rw [e]
  exact Finset.dvd_sum fun x _ => (four_dvd_bitSign_sum _ _).mul_right _

end Twist

/-! ### The Klein quotient -/

section Klein

variable {G K : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- The first character of `φ`'s `ZMod 2 × ZMod 2` part. -/
def eps₁ (φ : G →+ ZMod 2 × ZMod 2 × K) : G →+ ZMod 2 := (AddMonoidHom.fst _ _).comp φ

/-- The second character of `φ`'s `ZMod 2 × ZMod 2` part. -/
def eps₂ (φ : G →+ ZMod 2 × ZMod 2 × K) : G →+ ZMod 2 :=
  (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp φ)

/-- `φ`'s `K` part. -/
def base (φ : G →+ ZMod 2 × ZMod 2 × K) : G →+ K :=
  (AddMonoidHom.snd _ _).comp ((AddMonoidHom.snd _ _).comp φ)

/-- What a twisted sum `d` of the contraction `z` demands: square sum and squared sum `n`, and
`d ≡ z (mod 2)`. -/
structure TwistDemands (n : ℤ) (z d : K → ℤ) : Prop where
  sq : ∑ h, d h * d h = n
  sum_sq : (∑ h, d h) * (∑ h, d h) = n
  parity : ∀ h, (2 : ℤ) ∣ d h - z h

/-- The three twists of the contraction to `K` meet `TwistDemands (k − λ)`, and with the
contraction they add up to a multiple of `4`. -/
theorem klein_demands {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ ZMod 2 × ZMod 2 × K) (hφ : Function.Surjective φ) :
    TwistDemands ((k : ℤ) - lam) (contract (base φ) D) (twist (eps₁ φ) (base φ) D) ∧
      TwistDemands ((k : ℤ) - lam) (contract (base φ) D) (twist (eps₂ φ) (base φ) D) ∧
      TwistDemands ((k : ℤ) - lam) (contract (base φ) D)
        (twist (eps₁ φ + eps₂ φ) (base φ) D) ∧
      ∀ h, (4 : ℤ) ∣ contract (base φ) D h + twist (eps₁ φ) (base φ) D h +
        twist (eps₂ φ) (base φ) D h + twist (eps₁ φ + eps₂ φ) (base φ) D h := by
  obtain ⟨u₁, hu₁⟩ := hφ (1, 0, 0)
  obtain ⟨u₂, hu₂⟩ := hφ (0, 1, 0)
  have key : ∀ (ε : G →+ ZMod 2) (u : G), base φ u = 0 → ε u = 1 →
      TwistDemands ((k : ℤ) - lam) (contract (base φ) D) (twist ε (base φ) D) :=
    fun ε u hu hεu => ⟨twist_sq_of_isSDS hD ε _ hu hεu, twist_sum_sq_of_isSDS hD ε _ hu hεu,
      two_dvd_twist_sub ε _ D⟩
  have hb₁ : base φ u₁ = 0 := by simp [base, hu₁]
  have hb₂ : base φ u₂ = 0 := by simp [base, hu₂]
  refine ⟨key _ u₁ hb₁ (by simp [eps₁, hu₁]), key _ u₂ hb₂ (by simp [eps₂, hu₂]),
    key _ u₁ hb₁ (by simp [eps₁, eps₂, hu₁]), four_dvd_sum_twists _ _ _ D⟩

end Klein

/-! ### The kill on `K = ZMod 3` -/

theorem sum_zmod_three (f : ZMod 3 → ℤ) : ∑ h, f h = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

/-- A vector on `ZMod 3` as its three values, or their residues mod 4. -/
abbrev Triple := ℤ × ℤ × ℤ

/-- One coordinate `z` of the contraction takes residues `r₁, r₂, r₃` (mod 4) for the three
twisted sums: each of `z`'s parity, and `z + r₁ + r₂ + r₃ ≡ 0 (mod 4)`. -/
def coordOK (z r₁ r₂ r₃ : ℤ) : Bool :=
  (r₁ - z) % 2 == 0 && (r₂ - z) % 2 == 0 && (r₃ - z) % 2 == 0 && (z + r₁ + r₂ + r₃) % 4 == 0

/-- No choice of residue triples from `R` for the three twisted sums fits `z`. -/
def clash (R : List Triple) (z : Triple) : Bool :=
  R.all fun r₁ => R.all fun r₂ => R.all fun r₃ =>
    !(coordOK z.1 r₁.1 r₂.1 r₃.1 && coordOK z.2.1 r₁.2.1 r₂.2.1 r₃.2.1 &&
      coordOK z.2.2 r₁.2.2 r₂.2.2 r₃.2.2)

/-- The residues mod 4. -/
def res4 (d : Triple) : Triple := (d.1 % 4, d.2.1 % 4, d.2.2 % 4)

/-- `⌊√n⌋` by bisection on `[lo, hi)` in `f` steps (`rowCheck` checks the result). -/
def sqrtGo : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, lo, _ => lo
  | f + 1, n, lo, hi =>
    if hi ≤ lo + 1 then lo
    else if (lo + hi) / 2 * ((lo + hi) / 2) ≤ n then sqrtGo f n ((lo + hi) / 2) hi
    else sqrtGo f n lo ((lo + hi) / 2)

/-- `⌊√n⌋` for `n < 2^128`. -/
def isqrt (n : ℕ) : ℕ := sqrtGo 128 n 0 (n + 1)

/-- For `a` and `m = σ − a`, the `b` with `a² + b² + (m − b)² = Q` solve `(2b − m)² = Δ`. -/
def delta (Q σ a : ℤ) : ℤ := 2 * (Q - a * a) - (σ - a) * (σ - a)

/-- With `e² ≤ Δ < (e + 1)²`: if `Δ = e²`, both triples `b = (m ± e)/2` pass `p`. -/
def rowCheck (Q σ : ℤ) (p : Triple → Bool) (a e : ℤ) : Bool :=
  decide (e * e ≤ delta Q σ a) && decide (delta Q σ a < (e + 1) * (e + 1)) &&
    (!(e * e == delta Q σ a) || !((σ - a + e) % 2 == 0) ||
      (p (a, (σ - a + e) / 2, σ - a - (σ - a + e) / 2) &&
        p (a, (σ - a - e) / 2, σ - a - (σ - a - e) / 2)))

/-- Every triple `(a, b, σ − a − b)` with square sum `Q` passes `p`. -/
def rowOK (Q σ : ℤ) (p : Triple → Bool) (a : ℤ) : Bool :=
  decide (delta Q σ a < 0) || rowCheck Q σ p a (isqrt (delta Q σ a).toNat)

/-- Every triple with `|a| ≤ B`, sum `σ` and square sum `Q` passes `p`. -/
def triplesOK (Q σ : ℤ) (B : ℕ) (p : Triple → Bool) : Bool :=
  allRange (rowOK Q σ p) (-(B : ℤ)) (2 * B + 1)

/-- The kill: `t² = n`; every triple with sum `±t` and square sum `n` (a twisted sum) has its
residues mod 4 in `R`; every triple with sum `±s` and square sum `Qz` (the contraction) clashes
with `R`. The bounds cover them: `n < (Bd + 1)²`, `Qz < (Bz + 1)²`. -/
def kleinKill (n t Qz s : ℤ) (Bd Bz : ℕ) (R : List Triple) : Bool :=
  t * t == n && decide (n < ((Bd : ℤ) + 1) * ((Bd : ℤ) + 1)) &&
    decide (Qz < ((Bz : ℤ) + 1) * ((Bz : ℤ) + 1)) &&
    triplesOK n t Bd (fun d => decide (res4 d ∈ R)) &&
    triplesOK n (-t) Bd (fun d => decide (res4 d ∈ R)) &&
    triplesOK Qz s Bz (clash R) && triplesOK Qz (-s) Bz (clash R)

theorem bounds_of_mul_self_le {a Q : ℤ} {B : ℕ} (ha : a * a ≤ Q)
    (hB : Q < ((B : ℤ) + 1) * ((B : ℤ) + 1)) : -(B : ℤ) ≤ a ∧ a ≤ B := by
  have h0 : (0 : ℤ) ≤ B := Nat.cast_nonneg B
  constructor <;> nlinarith

theorem rowCheck_spec {Q σ : ℤ} {p : Triple → Bool} {a e b : ℤ} (he : 0 ≤ e)
    (h : rowCheck Q σ p a e = true)
    (hΔ : delta Q σ a = (2 * b - (σ - a)) * (2 * b - (σ - a))) :
    p (a, b, σ - a - b) = true := by
  simp only [rowCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [hΔ] at h1 h2 h3
  have hy := abs_mul_abs_self (2 * b - (σ - a))
  have hx : |2 * b - (σ - a)| = e := by
    have h0 := abs_nonneg (2 * b - (σ - a))
    exact le_antisymm (le_of_not_gt fun hlt => by nlinarith)
      (le_of_not_gt fun hlt => by nlinarith)
  rcases h3 with (h3 | h3) | ⟨h3, h4⟩
  · exact absurd (by rw [← hy, hx]) h3
  · rcases abs_choice (2 * b - (σ - a)) with h5 | h5 <;> omega
  · rcases abs_choice (2 * b - (σ - a)) with h5 | h5
    · have hb : (σ - a + e) / 2 = b := by omega
      rw [hb] at h3
      exact h3
    · have hb : (σ - a - e) / 2 = b := by omega
      rw [hb] at h4
      exact h4

theorem rowOK_spec {Q σ : ℤ} {p : Triple → Bool} {a b c : ℤ} (h : rowOK Q σ p a = true)
    (hs : a + b + c = σ) (hq : a * a + b * b + c * c = Q) : p (a, b, c) = true := by
  have hc : c = σ - a - b := by linarith
  subst hc
  have hΔ : delta Q σ a = (2 * b - (σ - a)) * (2 * b - (σ - a)) := by
    rw [delta, ← hq]
    ring
  simp only [rowOK, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · rw [hΔ] at h
    nlinarith [mul_self_nonneg (2 * b - (σ - a))]
  · exact rowCheck_spec (Nat.cast_nonneg _) h hΔ

theorem triplesOK_spec {Q σ : ℤ} {B : ℕ} {p : Triple → Bool} (h : triplesOK Q σ B p = true)
    (hB : Q < ((B : ℤ) + 1) * ((B : ℤ) + 1)) {a b c : ℤ} (hs : a + b + c = σ)
    (hq : a * a + b * b + c * c = Q) : p (a, b, c) = true := by
  have ha := bounds_of_mul_self_le (a := a) (by nlinarith [mul_self_nonneg b, mul_self_nonneg c]) hB
  exact rowOK_spec ((allRange_iff _ _ _).1 h a ha.1 (by push_cast; omega)) hs hq

theorem coordOK_of {z d₁ d₂ d₃ : ℤ} (h₁ : (2 : ℤ) ∣ d₁ - z) (h₂ : (2 : ℤ) ∣ d₂ - z)
    (h₃ : (2 : ℤ) ∣ d₃ - z) (h4 : (4 : ℤ) ∣ z + d₁ + d₂ + d₃) :
    coordOK z (d₁ % 4) (d₂ % 4) (d₃ % 4) = true := by
  simp only [coordOK, Bool.and_eq_true, beq_iff_eq]
  omega

theorem clash_spec {R : List Triple} {z r₁ r₂ r₃ : Triple} (h : clash R z = true)
    (h₁ : r₁ ∈ R) (h₂ : r₂ ∈ R) (h₃ : r₃ ∈ R) (c₁ : coordOK z.1 r₁.1 r₂.1 r₃.1 = true)
    (c₂ : coordOK z.2.1 r₁.2.1 r₂.2.1 r₃.2.1 = true)
    (c₃ : coordOK z.2.2 r₁.2.2 r₂.2.2 r₃.2.2 = true) : False := by
  simp only [clash, List.all_eq_true] at h
  have := h r₁ h₁ r₂ h₂ r₃ h₃
  rw [c₁, c₂, c₃] at this
  simp at this

/-- A contraction `z` to `ZMod 3` with square sum `Qz` and squared sum `s²`, and three twisted
sums meeting `TwistDemands n z` that add up with `z` to multiples of `4`, contradict
`kleinKill`. -/
theorem false_of_kleinKill {n t Qz s : ℤ} {Bd Bz : ℕ} {R : List Triple}
    (h : kleinKill n t Qz s Bd Bz R = true) {z d₁ d₂ d₃ : ZMod 3 → ℤ}
    (hz : ∑ h, z h * z h = Qz) (hzs : (∑ h, z h) * (∑ h, z h) = s * s)
    (h₁ : TwistDemands n z d₁) (h₂ : TwistDemands n z d₂) (h₃ : TwistDemands n z d₃)
    (h4 : ∀ h, (4 : ℤ) ∣ z h + d₁ h + d₂ h + d₃ h) : False := by
  simp only [kleinKill, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨ht, hBd⟩, hBz⟩, hdP⟩, hdN⟩, hzP⟩, hzN⟩ := h
  have hres : ∀ d : ZMod 3 → ℤ, TwistDemands n z d → res4 (d 0, d 1, d 2) ∈ R := by
    intro d hd
    have hsq := hd.sq
    have hss := hd.sum_sq
    rw [sum_zmod_three] at hsq hss
    rcases mul_self_eq_mul_self_iff.1 (hss.trans ht.symm) with e | e
    · exact of_decide_eq_true (triplesOK_spec hdP hBd e hsq)
    · exact of_decide_eq_true (triplesOK_spec hdN hBd e hsq)
  have hcl : clash R (z 0, z 1, z 2) = true := by
    rw [sum_zmod_three] at hz hzs
    rcases mul_self_eq_mul_self_iff.1 hzs with e | e
    · exact triplesOK_spec hzP hBz e hz
    · exact triplesOK_spec hzN hBz e hz
  have hc (i : ZMod 3) : coordOK (z i) (d₁ i % 4) (d₂ i % 4) (d₃ i % 4) = true :=
    coordOK_of (h₁.parity i) (h₂.parity i) (h₃.parity i) (h4 i)
  exact clash_spec hcl (hres d₁ h₁) (hres d₂ h₂) (hres d₃ h₃) (hc 0) (hc 1) (hc 2)

/-- `(v, k, λ)` dies on every group of order `v` onto `ZMod 2 × ZMod 2 × ZMod 3`: `3 ∣ v`,
`s² = k + λ (v − 1)`, and `kleinKill` for `n = k − λ` and the contraction to `ZMod 3` (fibres
`v / 3`: square sum `k + λ (v / 3 − 1)`, sum `±s`). -/
def KleinKills (v k : ℕ) (lam : ℤ) : Prop :=
  ∃ s t : ℤ, ∃ Bd Bz : ℕ, ∃ R : List Triple, 3 ∣ v ∧ s * s = k + lam * ((v : ℤ) - 1) ∧
    kleinKill (k - lam) t (k + lam * (((v / 3 : ℕ) : ℤ) - 1)) s Bd Bz R = true

/-- No SDS on a group onto `ZMod 2 × ZMod 2 × ZMod 3` with parameters that `KleinKills` rules
out. -/
theorem not_hasSDS_of_kleinKills {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ} {lam : ℤ}
    (φ : G →+ ZMod 2 × ZMod 2 × ZMod 3) (hφ : Function.Surjective φ)
    (h : KleinKills (Fintype.card G) k lam) : ¬ HasSDS G k lam := by
  rintro ⟨D, hD⟩
  obtain ⟨s, t, Bd, Bz, R, h3, hs, hk⟩ := h
  obtain ⟨c, hc⟩ : ∃ c, Fintype.card G = c * Fintype.card (ZMod 3) :=
    ⟨Fintype.card G / 3, by rw [ZMod.card]; exact (Nat.div_mul_cancel h3).symm⟩
  have hc3 : Fintype.card G / 3 = c := by
    rw [hc, ZMod.card, Nat.mul_div_cancel _ (by norm_num)]
  rw [hc3] at hk
  have hψ : Function.Surjective (base φ) := fun h => by
    obtain ⟨x, hx⟩ := hφ (0, 0, h)
    exact ⟨x, by simp [base, hx]⟩
  have hfib := card_fibre_eq hψ hc
  have hc1 : 1 ≤ c := by
    have := (Fintype.card_pos : 0 < Fintype.card G)
    rw [hc, ZMod.card] at this
    omega
  have hH1 : 1 ≤ Fintype.card (ZMod 3) := Fintype.card_pos
  have hsq : ∑ h, contract (base φ) D h * contract (base φ) D h = k + lam * ((c : ℤ) - 1) := by
    rw [hD.contract_sq (base φ), hfib 0, Nat.cast_sub hc1, Nat.cast_one]
  have hcorr : ∀ g, g ≠ 0 →
      ∑ h, contract (base φ) D h * contract (base φ) D (h + g) = lam * c := fun g hg => by
    rw [hD.contract_autocorr (base φ) g hg, hfib]
  have hsum : (∑ h, contract (base φ) D h) * (∑ h, contract (base φ) D h) = s * s := by
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hsq, Finset.sum_congr rfl fun g hg => hcorr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hs, hc,
      nsmul_eq_mul, Nat.cast_sub hH1]
    push_cast
    ring
  obtain ⟨h₁, h₂, h₃, h4⟩ := klein_demands hD φ hφ
  exact false_of_kleinKill hk hsq hsum h₁ h₂ h₃ h4

/-! ### Rows -/

/-- A row's quotient onto `Grp [2, 2, 3] = ZMod 2 × ZMod 2 × ZMod 3`: forms `A` and preimages `P`
of the unit vectors. -/
structure KleinCert where
  A : List (List ℕ)
  P : List (List ℕ)
  deriving DecidableEq

/-- The forms map the row's group onto `Grp [2, 2, 3]`. -/
def KleinCert.Valid (w : Row) (c : KleinCert) : Prop :=
  MapOk w.ms [2, 2, 3] c.A ∧ SurjCert w.ms [2, 2, 3] c.A c.P

instance KleinCert.instDecidableValid (w : Row) (c : KleinCert) : Decidable (c.Valid w) := by
  unfold KleinCert.Valid; infer_instance

/-- A row with a valid quotient onto `Grp [2, 2, 3]` whose parameters `KleinKills` rules out has
no SDS, whatever `Fintype` instance its group carries. -/
theorem KleinCert.not_hasSDS {w : Row} {c : KleinCert} {v : ℕ} (h : c.Valid w)
    (hv : w.ms.prod = v) (hk : KleinKills v w.k w.lam) (inst : Fintype (Grp w.ms)) :
    ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨hmap, hsurj⟩ := h
  let φ : Grp w.ms →+ ZMod 2 × ZMod 2 × ZMod 3 := linMap w.ms [2, 2, 3] c.A hmap
  refine not_hasSDS_of_kleinKills φ (linMap_surjective hmap hsurj) ?_
  rw [Grp.card_eq, hv]
  exact hk

end SignedDifferenceSets.KleinTomography
