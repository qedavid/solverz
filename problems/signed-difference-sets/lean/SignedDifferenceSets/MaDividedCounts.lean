module

public import SignedDifferenceSets.MaDivided2
public import SignedDifferenceSets.MarkedCountsInt

/-!
# The divided contraction below a Ma quotient, by value counts

On a C21 quotient `ZMod (r p^l) × K` (`l = 1` with `b ≥ 1`, C34's step `Ma.dvd_contract_quot`;
`l = 2` with `b ≥ 2`, C36's `Ma.dvd_contract_quot_sub` twice; any prime `p`), the coset sums `W`
along `G → ZMod r × K` (fibres `q c`, `q = p^l`) are divisible by `q`, so `Z = W / q` has entries
in `[−c, c]`, `q² Σ Z² = k + λ (q c − 1)`, `q² (Σ Z)² = k + λ (v − 1)` and `q Σ |Z| ≤ k`
(`DividedDemands`; `IsSDS.exists_divided`, `IsSDS.exists_divided2`). The sum, square sum and
absolute sum depend only on the counts of `Z`'s values: `countsGo` searches every count vector on
`±c, …, ±2` (largest magnitude first, each node pruned by `magOk` with the head's magnitude),
with `±1` and `0` in closed form, and `anyCountsMag` adds `Σ Z² ≡ Σ Z (mod 2)`. When it finds
none for `Σ Z = s'` (negation covers `−s'`), no SDS (`DividedDemands.false_of_anyCountsMag`):
no vector search, no autocorrelation. `MaCountCert.Kills` (`Valid` and no counts) checks a row by
`decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets

open Ma

section Divided

variable {H : Type*} [AddCommGroup H] [Fintype H]

/-- What `Z = W / q` meets when `q` divides the coset sums `W` (fibres `q c`) of an SDS
`(v, k, λ)`. -/
structure DividedDemands (q c k : ℕ) (lam : ℤ) (v : ℕ) (Z : H → ℤ) : Prop where
  bound : ∀ y, |Z y| ≤ c
  sq : (q : ℤ) ^ 2 * ∑ y, Z y * Z y = k + lam * ((q * c : ℕ) - 1)
  corr : ∀ g, g ≠ 0 → (q : ℤ) ^ 2 * ∑ y, Z y * Z (y + g) = lam * (q * c : ℕ)
  sum : (q : ℤ) ^ 2 * ((∑ y, Z y) * ∑ y, Z y) = k + lam * ((v : ℤ) - 1)
  abs : (q : ℤ) * ∑ y, |Z y| ≤ k
  parity : ((k : ℤ) - q * ∑ y, |Z y|) % 2 = 0

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq H]

/-- If `q` divides every coset sum `W` along `χ` (fibres `q c`), then `Z = W / q` meets
`DividedDemands`. -/
theorem IsSDS.exists_divided_of_dvd {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    {χ : G →+ H} (hχ : Function.Surjective χ) {q c : ℕ} (hq : 0 < q)
    (hcard : Fintype.card G = q * c * Fintype.card H) (hdiv : ∀ y, (q : ℤ) ∣ contract χ D y) :
    ∃ Z : H → ℤ, (∀ y, contract χ D y = q * Z y) ∧
      DividedDemands q c k lam (Fintype.card G) Z := by
  have hfib := card_fibre_eq hχ hcard
  set W := contract χ D with hWdef
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  set Z : H → ℤ := fun y => W y / q
  have hWZ : ∀ y, W y = q * Z y := fun y => (Int.mul_ediv_cancel' (hdiv y)).symm
  have hqc1 : 1 ≤ q * c := by
    rcases Nat.eq_zero_or_pos (q * c) with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card G)
      rw [hcard, h0, zero_mul] at this
      omega
    · exact h0
  have hsqW := hD.contract_sq χ
  rw [← hWdef, hfib 0, Nat.cast_sub hqc1, Nat.cast_one] at hsqW
  have hcorrW : ∀ g, g ≠ 0 → ∑ y, W y * W (y + g) = lam * ((q * c : ℕ) : ℤ) := fun g hg => by
    rw [hD.contract_autocorr χ g hg, hfib]
  have habsW : ∑ y, |W y| = q * ∑ y, |Z y| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hWZ y, abs_mul, abs_of_pos hq0]
  refine ⟨Z, hWZ, ⟨fun y => ?_, ?_, fun g hg => ?_, ?_, ?_, ?_⟩⟩
  · have h1 := abs_contract_le χ D y
    rw [hfib y, ← hWdef, hWZ y, abs_mul, abs_of_pos hq0] at h1
    push_cast at h1
    have : (q : ℤ) * |Z y| ≤ (q : ℤ) * c := by linarith
    exact le_of_mul_le_mul_left this hq0
  · rw [← hsqW, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hWZ y]
    ring
  · rw [← hcorrW g hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hWZ y, hWZ (y + g)]
    ring
  · have hH1 : 1 ≤ Fintype.card H := Fintype.card_pos
    have hW2 : (∑ y, W y) * (∑ y, W y) = k + lam * ((Fintype.card G : ℤ) - 1) := by
      rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
      simp only [add_zero]
      rw [hsqW, Finset.sum_congr rfl fun g hg => hcorrW g (Finset.ne_of_mem_erase hg),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        nsmul_eq_mul, Nat.cast_sub hH1, hcard]
      push_cast
      ring
    have hsumW : ∑ y, W y = q * ∑ y, Z y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => hWZ y
    rw [hsumW] at hW2
    linear_combination hW2
  · have h1 := hD.sum_abs_contract_le χ
    rwa [← hWdef, habsW] at h1
  · have h2 := hD.sum_abs_contract_parity χ
    rwa [← hWdef, habsW] at h2

end Divided

/-- `ZMod (r p) × K → ZMod r × K` is onto. -/
theorem maQuot_surjective (K : Type) [AddCommGroup K] (r p : ℕ) :
    Function.Surjective (maQuot K r p) := by
  rintro ⟨a, b⟩
  obtain ⟨a', ha'⟩ := ZMod.ringHom_surjective (ZMod.castHom (dvd_mul_right r p) (ZMod r)) a
  exact ⟨(a', b), by simp [maQuot, ha']⟩

/-- One level below a C21 quotient `ZMod (r p) × K` with `b ≥ 1` (any prime `p`): `p` divides the
coset sums `W` on `ZMod r × K` (C34's step) and `Z = W / p` meets `DividedDemands p c`. -/
theorem IsSDS.exists_divided {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K]
    [Fintype K] [DecidableEq K] {p r i e b c k : ℕ} {lam : ℤ} [hp : Fact p.Prime]
    [NeZero (r * p)] [NeZero r] {φ : G →+ ZMod (r * p) × K} (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * Fintype.card (ZMod (r * p) × K)) (hr : 0 < r) (hi : 0 < i)
    (hc : ∀ x : K, p ^ i • x = -x) (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam) (hb : 2 * b ≤ e)
    (hb1 : 0 < b) (hcert : CycloFacts p r) {D : G → SignType} (hD : IsSDS k lam D) :
    ∃ Z : ZMod r × K → ℤ, (∀ y, contract ((maQuot K r p).comp φ) D y = p * Z y) ∧
      DividedDemands p c k lam (Fintype.card G) Z := by
  have hcardp : Fintype.card G = p * c * Fintype.card (ZMod r × K) := by
    rw [hcard, Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hχ : Function.Surjective ((maQuot K r p).comp φ) := (maQuot_surjective K r p).comp hφ
  exact hD.exists_divided_of_dvd hχ hp.out.pos hcardp
    fun y => Ma.dvd_contract_quot hφ hcard hr hi hc hn hb hb1 hcert hD y

/-- Two levels below a C21 quotient `ZMod (r p p) × K` with `b ≥ 2` (any prime `p`): `p²`
divides the coset sums `W` on `ZMod r × K` (C36's step) and `Z = W / p²` meets
`DividedDemands (p p) c`. -/
theorem IsSDS.exists_divided2 {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K]
    [Fintype K] {p r i e b c k : ℕ} {lam : ℤ} [hp : Fact p.Prime]
    [NeZero (r * p * p)] [NeZero (r * p)] [NeZero r] {φ : G →+ ZMod (r * p * p) × K}
    (hφ : Function.Surjective φ) (hcard : Fintype.card G = c * Fintype.card (ZMod (r * p * p) × K))
    (hr : 0 < r) (hi : 0 < i) (hc : ∀ x : K, p ^ i • x = -x) (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam)
    (hb : 2 * b ≤ e) (hb2 : 2 ≤ b) (hcert1 : CycloFacts p (r * p)) (hcert2 : CycloFacts p r)
    {D : G → SignType} (hD : IsSDS k lam D) :
    ∃ Z : ZMod r × K → ℤ, DividedDemands (p * p) c k lam (Fintype.card G) Z := by
  classical
  have hrp : 0 < r * p := Nat.mul_pos hr hp.out.pos
  set ψ1 := maQuot K (r * p) p with hψ1def
  set ψ2 := maQuot K r p with hψ2def
  set χ1 := ψ1.comp φ with hχ1def
  set χ2 := ψ2.comp χ1 with hχ2def
  have hχ1 : Function.Surjective χ1 := (maQuot_surjective K (r * p) p).comp hφ
  have hχ2 : Function.Surjective χ2 := (maQuot_surjective K r p).comp hχ1
  have hcard1 : Fintype.card G = p * c * Fintype.card (ZMod (r * p) × K) := by
    rw [hcard, Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hcard2 : Fintype.card G = p * p * c * Fintype.card (ZMod r × K) := by
    rw [hcard, Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hb1 : 0 < b := by omega
  -- one level down: `p ∣ W₁`; two levels down: `p² ∣ W`
  have hW1 : ∀ y, (p : ℤ) ∣ contract χ1 D y := by
    intro y
    obtain ⟨h, rfl⟩ := maQuot_surjective K (r * p) p y
    have h1 := Ma.dvd_contract_quot_sub hφ hcard hrp hi hc hn hb hcert1 hD h
    have h2 := dvd_add ((dvd_pow_self (p : ℤ) hb1.ne').trans h1)
      (dvd_mul_right (p : ℤ) (contract φ D h))
    simpa [hχ1def, hψ1def] using h2
  have hdiv : ∀ y, ((p * p : ℕ) : ℤ) ∣ contract χ2 D y := by
    intro y
    obtain ⟨h1, rfl⟩ := maQuot_surjective K r p y
    have h2 := Ma.dvd_contract_quot_sub (φ := χ1) hχ1 hcard1 hr hi hc hn hb hcert2 hD h1
    have h3 : (p : ℤ) ^ 2 ∣ (p : ℤ) ^ b := pow_dvd_pow _ hb2
    have h4 : (p : ℤ) ^ 2 ∣ (p : ℤ) * contract χ1 D h1 := by
      rw [pow_two]; exact mul_dvd_mul_left _ (hW1 h1)
    have := dvd_add (h3.trans h2) h4
    rw [Nat.cast_mul, ← pow_two]
    simpa [hχ2def, hψ2def] using this
  obtain ⟨Z, -, hZ⟩ := hD.exists_divided_of_dvd hχ2 (Nat.mul_pos hp.out.pos hp.out.pos) hcard2 hdiv
  exact ⟨Z, hZ⟩

section Counts

/-- Counts on values of magnitude at most `m` give `N` values with sum `s`, square sum `Q` and
absolute sum at most `A` only if `|s| ≤ A`, `|s| ≤ Q`, `Q ≤ m A` and `Q ≤ m² N`. -/
def magOk (m : ℤ) (N : ℕ) (s Q A : ℤ) : Bool :=
  decide (|s| ≤ A) && decide (|s| ≤ Q) && decide (Q ≤ m * A) && decide (Q ≤ m * m * N)

/-- Whether counts on the values `xs`, then `±1` and `0`, give `N` values with sum `s`, square
sum `Q` and absolute sum at most `A`: each count `0 … min N (Q / x²)` of the head `x`, then the
tail; `±1`, `0` in closed form. -/
def countsGo : List ℤ → ℕ → ℤ → ℤ → ℤ → Bool
  | [], N, s, Q, A => magOk 1 N s Q A && (Q - s) % 2 == 0
  | x :: xs, N, s, Q, A => magOk |x| N s Q A &&
      (List.range (min N (Q / (x * x)).toNat + 1)).any fun i =>
        countsGo xs (N - i) (s - i * x) (Q - i * (x * x)) (A - i * |x|)

/-- The values `±a, …, ±2`, largest magnitude first. -/
def magVals : ℕ → List ℤ
  | 0 => []
  | 1 => []
  | a + 2 => ((a + 2 : ℕ) : ℤ) :: -((a + 2 : ℕ) : ℤ) :: magVals (a + 1)

/-- Whether counts of values in `[−c, c]` give `N` values with sum `s`, square sum `Q` and
absolute sum at most `A`: `Q ≡ s (mod 2)` and `countsGo` on `magVals c`. -/
def anyCountsMag (c N : ℕ) (s Q A : ℤ) : Bool :=
  (Q - s) % 2 == 0 && countsGo (magVals c) N s Q A

theorem countSum_le_of_mem {xs : List ℤ} (n : ℤ → ℕ) {f g : ℤ → ℤ} (h : ∀ x ∈ xs, f x ≤ g x) :
    countSum xs n f ≤ countSum xs n g := by
  induction xs with
  | nil => simp [countSum]
  | cons x xs ih =>
    rw [countSum_cons, countSum_cons]
    have h1 := mul_le_mul_of_nonneg_left (h x List.mem_cons_self) (Nat.cast_nonneg (α := ℤ) (n x))
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    linarith

theorem countSum_mul_left (xs : List ℤ) (n : ℤ → ℕ) (a : ℤ) (f : ℤ → ℤ) :
    countSum xs n (fun x => a * f x) = a * countSum xs n f := by
  induction xs with
  | nil => simp [countSum]
  | cons x xs ih => rw [countSum_cons, countSum_cons, ih]; ring

theorem abs_countSum_le (xs : List ℤ) (n : ℤ → ℕ) :
    |countSum xs n id| ≤ countSum xs n fun x => |x| := by
  induction xs with
  | nil => simp [countSum]
  | cons x xs ih =>
    rw [countSum_cons, countSum_cons]
    calc |(n x : ℤ) * id x + countSum xs n id|
        ≤ |(n x : ℤ) * id x| + |countSum xs n id| := abs_add_le _ _
      _ ≤ (n x : ℤ) * |x| + countSum xs n fun x => |x| := by
        rw [abs_mul, Nat.abs_cast]
        simp only [id]
        linarith

theorem abs_le_mul_self (y : ℤ) : |y| ≤ y * y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h1 := Int.one_le_abs hy
    have h2 := abs_mul_abs_self y
    nlinarith [abs_nonneg y]

/-- The search finds every count vector: counts `n` on `xs` (sorted by decreasing magnitude, none
zero) and `u`, `v`, `w` on `1`, `−1`, `0` meeting the targets make `countsGo` true. -/
theorem countsGo_of (n : ℤ → ℕ) (u v w : ℕ) : ∀ (xs : List ℤ) (N : ℕ) (s Q A : ℤ),
    xs.Pairwise (fun a b => |b| ≤ |a|) → (∀ x ∈ xs, 1 ≤ |x|) →
    countSum xs n (fun _ => 1) + u + v + w = N → countSum xs n id + u - v = s →
    countSum xs n (fun x => x * x) + u + v = Q → countSum xs n (fun x => |x|) + u + v ≤ A →
    countsGo xs N s Q A = true
  | [], N, s, Q, A, _, _, h1, h2, h3, h4 => by
    simp only [countSum, List.map_nil, List.sum_nil, zero_add] at h1 h2 h3 h4
    have hs : |s| ≤ u + v := abs_le.2 ⟨by omega, by omega⟩
    simp only [countsGo, magOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩
  | x :: xs, N, s, Q, A, hsort, hone, h1, h2, h3, h4 => by
    rw [List.pairwise_cons] at hsort
    have hx1 : 1 ≤ |x| := hone x List.mem_cons_self
    have hle : ∀ y ∈ x :: xs, |y| ≤ |x| := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_rfl
      · exact hsort.1 y hy
    have hn0 : (0 : ℤ) ≤ n x := Nat.cast_nonneg _
    have hu : (0 : ℤ) ≤ u := Nat.cast_nonneg _
    have hv : (0 : ℤ) ≤ v := Nat.cast_nonneg _
    have hw : (0 : ℤ) ≤ w := Nat.cast_nonneg _
    have hc1 := countSum_nonneg xs n (f := fun _ => 1) fun _ => zero_le_one
    have hcq := countSum_nonneg xs n (f := fun x => x * x) fun x => mul_self_nonneg x
    -- the node test
    have habs := abs_countSum_le (x :: xs) n
    have hAq : countSum (x :: xs) n (fun x => |x|) ≤ countSum (x :: xs) n (fun x => x * x) :=
      countSum_le_of_mem n fun y _ => abs_le_mul_self y
    have hQm : countSum (x :: xs) n (fun x => x * x) ≤
        countSum (x :: xs) n (fun y => |x| * |y|) := countSum_le_of_mem n fun y hy => by
      show y * y ≤ |x| * |y|
      rw [← abs_mul_abs_self y]
      exact mul_le_mul_of_nonneg_right (hle y hy) (abs_nonneg y)
    rw [countSum_mul_left] at hQm
    have hQN : countSum (x :: xs) n (fun x => x * x) ≤
        countSum (x :: xs) n (fun _ => |x| * |x| * 1) := countSum_le_of_mem n fun y hy => by
      show y * y ≤ |x| * |x| * 1
      rw [mul_one, ← abs_mul_abs_self y]
      exact mul_le_mul (hle y hy) (hle y hy) (abs_nonneg y) (abs_nonneg x)
    rw [countSum_mul_left] at hQN
    have huv : |(u : ℤ) - v| ≤ u + v := abs_le.2 ⟨by omega, by omega⟩
    have hs : |s| ≤ countSum (x :: xs) n (fun x => |x|) + u + v := by
      rw [← h2]
      calc |countSum (x :: xs) n id + u - v| = |countSum (x :: xs) n id + (u - v)| := by
            rw [add_sub_assoc]
        _ ≤ |countSum (x :: xs) n id| + |(u : ℤ) - v| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hx0 : 0 ≤ |x| := abs_nonneg x
    have hmag : magOk |x| N s Q A = true := by
      simp only [magOk, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
      · have : (u : ℤ) + v ≤ |x| * (u + v) := by
          nlinarith [mul_nonneg (sub_nonneg.2 hx1) (add_nonneg hu hv)]
        calc Q = countSum (x :: xs) n (fun x => x * x) + u + v := h3.symm
          _ ≤ |x| * (countSum (x :: xs) n (fun x => |x|) + u + v) := by linarith
          _ ≤ |x| * A := mul_le_mul_of_nonneg_left (by linarith) hx0
      · have hxx : 1 ≤ |x| * |x| := by nlinarith
        have : (u : ℤ) + v ≤ |x| * |x| * (u + v + w) := by
          nlinarith [mul_nonneg (sub_nonneg.2 hxx) (add_nonneg (add_nonneg hu hv) hw)]
        calc Q = countSum (x :: xs) n (fun x => x * x) + u + v := h3.symm
          _ ≤ |x| * |x| * (countSum (x :: xs) n (fun _ => 1) + u + v + w) := by linarith
          _ = |x| * |x| * N := by rw [h1]
    -- the head's count, then the tail
    rw [countSum_cons] at h1 h2 h3 h4
    simp only [id_eq, mul_one] at h1 h2
    have hxN : n x ≤ N := by
      have : (n x : ℤ) ≤ N := by linarith
      exact_mod_cast this
    have hxx0 : 0 < x * x := by
      have : x ≠ 0 := fun h => by rw [h, abs_zero] at hx1; omega
      exact mul_self_pos.2 this
    have hxQ : n x ≤ (Q / (x * x)).toNat := by
      have h5 : (n x : ℤ) * (x * x) ≤ Q := by linarith
      have h6 := (Int.le_ediv_of_mul_le hxx0 h5).trans (Int.self_le_toNat _)
      exact_mod_cast h6
    simp only [countsGo, hmag, Bool.true_and, List.any_eq_true, List.mem_range]
    refine ⟨n x, Nat.lt_succ_of_le (le_min hxN hxQ), ?_⟩
    refine countsGo_of n u v w xs (N - n x) (s - n x * x) (Q - n x * (x * x)) (A - n x * |x|)
      hsort.2 (fun y hy => hone y (List.mem_cons_of_mem _ hy)) ?_ ?_ ?_ ?_
    · rw [Nat.cast_sub hxN]; linarith
    · linarith
    · linarith
    · linarith

theorem mem_magVals : ∀ (a : ℕ) (y : ℤ), y ∈ magVals a ↔ 2 ≤ |y| ∧ |y| ≤ a
  | 0, y => by
    simp only [magVals, List.not_mem_nil, false_iff, not_and, not_le, Nat.cast_zero]
    intro h
    omega
  | 1, y => by
    simp only [magVals, List.not_mem_nil, false_iff, not_and, not_le, Nat.cast_one]
    intro h
    omega
  | a + 2, y => by
    simp only [magVals, List.mem_cons]
    rw [mem_magVals (a + 1) y]
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

theorem magVals_pairwise : ∀ a : ℕ, (magVals a).Pairwise (fun u v => |v| ≤ |u|)
  | 0 => List.Pairwise.nil
  | 1 => List.Pairwise.nil
  | a + 2 => by
    simp only [magVals, List.pairwise_cons]
    have hm : ∀ v ∈ magVals (a + 1), |v| ≤ ((a + 2 : ℕ) : ℤ) := fun v hv => by
      have := ((mem_magVals (a + 1) v).1 hv).2
      push_cast at this ⊢
      linarith
    refine ⟨fun v hv => ?_, fun v hv => ?_, magVals_pairwise (a + 1)⟩
    · rw [Nat.abs_cast]
      rcases List.mem_cons.1 hv with rfl | hv
      · exact le_of_eq (by rw [abs_neg, Nat.abs_cast])
      · exact hm v hv
    · rw [abs_neg, Nat.abs_cast]
      exact hm v hv

theorem magVals_nodup : ∀ a : ℕ, (magVals a).Nodup
  | 0 => List.nodup_nil
  | 1 => List.nodup_nil
  | a + 2 => by
    simp only [magVals, List.nodup_cons]
    refine ⟨fun h => ?_, fun h => ?_, magVals_nodup (a + 1)⟩
    · rcases List.mem_cons.1 h with h | h
      · omega
      · have := ((mem_magVals (a + 1) _).1 h).2
        rw [Nat.abs_cast] at this
        omega
    · have := ((mem_magVals (a + 1) _).1 h).2
      rw [abs_neg, Nat.abs_cast] at this
      omega

theorem vals_nodup (c : ℕ) : (1 :: -1 :: 0 :: magVals c).Nodup := by
  have h2 : ∀ y ∈ magVals c, 2 ≤ |y| := fun y hy => ((mem_magVals c y).1 hy).1
  refine List.nodup_cons.2 ⟨fun h => ?_, List.nodup_cons.2 ⟨fun h => ?_,
    List.nodup_cons.2 ⟨fun h => ?_, magVals_nodup c⟩⟩⟩
  · rcases List.mem_cons.1 h with h | h
    · norm_num at h
    rcases List.mem_cons.1 h with h | h
    · norm_num at h
    · have := h2 1 h
      norm_num at this
  · rcases List.mem_cons.1 h with h | h
    · norm_num at h
    · have := h2 (-1) h
      norm_num at this
  · have := h2 0 h
    norm_num at this

/-- The counts of an integer vector's values meet `anyCountsMag`. -/
theorem anyCountsMag_of {H : Type*} [Fintype H] {Z : H → ℤ} {c : ℕ} (hb : ∀ y, |Z y| ≤ c)
    {A : ℤ} (hA : ∑ y, |Z y| ≤ A) :
    anyCountsMag c (Fintype.card H) (∑ y, Z y) (∑ y, Z y * Z y) A = true := by
  have hmem : ∀ y, Z y ∈ (1 :: -1 :: 0 :: magVals c) := by
    intro y
    by_cases h2 : 2 ≤ |Z y|
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        ((mem_magVals c (Z y)).2 ⟨h2, hb y⟩)))
    · have : Z y = 1 ∨ Z y = -1 ∨ Z y = 0 := by
        rcases abs_cases (Z y) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at h2 <;> omega
      rcases this with h | h | h <;> simp [h]
  have e (f : ℤ → ℤ) : (countOf Z 1 : ℤ) * f 1 + countOf Z (-1) * f (-1) + countOf Z 0 * f 0 +
      countSum (magVals c) (countOf Z) f = ∑ y, f (Z y) := by
    rw [← countSum_countOf Z (vals_nodup c) hmem f, countSum_cons, countSum_cons, countSum_cons]
    ring
  have e1 := e fun _ => 1
  have e2 := e id
  have e3 := e fun x => x * x
  have e4 := e fun x => |x|
  simp only [id_eq, mul_one, mul_zero, mul_neg, neg_neg, abs_one, abs_neg, abs_zero,
    add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e1 e2 e3 e4
  simp only [anyCountsMag, Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, countsGo_of (countOf Z) (countOf Z 1) (countOf Z (-1)) (countOf Z 0) (magVals c)
    _ _ _ _ (magVals_pairwise c)
    (fun x hx => by have := ((mem_magVals c x).1 hx).1; linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)⟩
  have hev : Even (∑ y, Z y * (Z y - 1)) := Finset.even_sum _ fun y _ => Int.even_mul_pred_self _
  have : ∑ y, Z y * (Z y - 1) = ∑ y, Z y * Z y - ∑ y, Z y := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [this] at hev
  exact Int.even_iff.1 hev

end Counts

variable {H : Type*} [AddCommGroup H] [Fintype H]

/-- A vector meeting `DividedDemands q c` with `q² Q = k + λ (q c − 1)`, `(q s')² = k + λ (v − 1)`
and `k < q (A + 1)` has value counts with `Σ = s'`, `Σ² = Q`, absolute sum at most `A`, after a
negation if need be; when `anyCountsMag` finds none, there is no such vector. -/
theorem DividedDemands.false_of_anyCountsMag {q c k : ℕ} {lam : ℤ} {v : ℕ} {Z : H → ℤ}
    (hZ : DividedDemands q c k lam v Z) (hq : 0 < q) {Q s' : ℤ} {A : ℕ}
    (hQ : (q : ℤ) ^ 2 * Q = k + lam * ((q * c : ℕ) - 1))
    (hs : ((q : ℤ) * s') * ((q : ℤ) * s') = k + lam * ((v : ℤ) - 1)) (hA : k < q * (A + 1))
    (hnc : anyCountsMag c (Fintype.card H) s' Q A = false) : False := by
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  have hq2 : (q : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hq0.ne'
  have hQ' : ∑ y, Z y * Z y = Q := mul_left_cancel₀ hq2 (hZ.sq.trans hQ.symm)
  have hs' : (∑ y, Z y) * (∑ y, Z y) = s' * s' := by
    have h := hZ.sum.trans hs.symm
    exact mul_left_cancel₀ hq2 (by linear_combination h)
  have hA' : ∑ y, |Z y| ≤ A := by
    have h1 := hZ.abs
    have h2 : (k : ℤ) < q * ((A : ℤ) + 1) := by exact_mod_cast hA
    by_contra hlt
    have h3 : (A : ℤ) + 1 ≤ ∑ y, |Z y| := Int.add_one_le_of_lt (not_le.1 hlt)
    have := mul_le_mul_of_nonneg_left h3 hq0.le
    linarith
  rcases mul_self_eq_mul_self_iff.1 hs' with h | h
  · have := anyCountsMag_of hZ.bound hA'
    rw [h, hQ', hnc] at this
    exact Bool.noConfusion this
  · have := anyCountsMag_of (Z := fun y => -Z y)
      (fun y => by simpa only [abs_neg] using hZ.bound y) (A := A)
      (by simpa only [abs_neg] using hA')
    simp only [Finset.sum_neg_distrib, neg_mul_neg] at this
    rw [h, neg_neg, hQ', hnc] at this
    exact Bool.noConfusion this

/-! ### Rows -/

/-- A count certificate at level `l ∈ {1, 2}`: C21's fields (`p`, `r`, `i`, `e`, `b ≥ l`,
`ks ≠ []`, forms `A` onto `ZMod (r p^l) × Grp ks` with preimages `P`), the absolute-sum bound
`amax` and the divided square sum `Q` and sum `s'`. -/
structure MaCountCert where
  p : ℕ
  r : ℕ
  i : ℕ
  e : ℕ
  b : ℕ
  l : ℕ
  ks : List ℕ
  A : List (List ℕ)
  P : List (List ℕ)
  amax : ℕ
  Q : ℤ
  s' : ℤ
  deriving DecidableEq

/-- The fibre size `c = |G| / (r p^l |K|)` below the certificate's quotient. -/
def MaCountCert.fib (w : Row) (c : MaCountCert) : ℕ := w.ms.prod / (c.r * c.p ^ c.l * c.ks.prod)

/-- The row meets the hypotheses at level `l` (`(p, r)`, and `(p, r p)` at `l = 2`, among
`MaRows.maPairs`). -/
def MaCountCert.Valid (w : Row) (c : MaCountCert) : Prop :=
  IsPrimeTD c.p ∧ 0 < c.r ∧ 0 < c.i ∧ c.ks ≠ [] ∧ (∀ d ∈ c.ks, d ∣ c.p ^ c.i + 1) ∧
    MapOk w.ms (c.r * c.p ^ c.l :: c.ks) c.A ∧ SurjCert w.ms (c.r * c.p ^ c.l :: c.ks) c.A c.P ∧
    c.r * c.p ^ c.l * c.ks.prod ∣ w.ms.prod ∧ (c.p : ℤ) ^ c.e ∣ w.k - w.lam ∧ 2 * c.b ≤ c.e ∧
    (c.l = 1 ∨ c.l = 2) ∧ c.l ≤ c.b ∧
    ((c.p ^ c.l : ℕ) : ℤ) ^ 2 * c.Q = w.k + w.lam * ((c.p ^ c.l * c.fib w : ℕ) - 1) ∧
    (((c.p ^ c.l : ℕ) : ℤ) * c.s') * (((c.p ^ c.l : ℕ) : ℤ) * c.s') =
      w.k + w.lam * ((w.ms.prod : ℤ) - 1) ∧
    w.k < c.p ^ c.l * (c.amax + 1) ∧ (c.p, c.r) ∈ MaRows.maPairs ∧
    (c.l = 2 → (c.p, c.r * c.p) ∈ MaRows.maPairs)

/-- The hypotheses, and `anyCountsMag` finds no counts on `Grp (r :: ks)`'s `r ∏ ks` values. -/
def MaCountCert.Kills (w : Row) (c : MaCountCert) : Prop :=
  c.Valid w ∧ anyCountsMag (c.fib w) (c.r * c.ks.prod) c.s' c.Q c.amax = false

instance MaCountCert.instDecidableValid (w : Row) (c : MaCountCert) : Decidable (c.Valid w) := by
  unfold MaCountCert.Valid MaCountCert.fib; infer_instance

instance MaCountCert.instDecidableKills (w : Row) (c : MaCountCert) : Decidable (c.Kills w) := by
  unfold MaCountCert.Kills MaCountCert.fib; infer_instance

/-- A row a count certificate kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem MaCountCert.not_hasSDS {w : Row} {c : MaCountCert} (h : c.Kills w)
    (inst : Fintype (Grp w.ms)) : ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨p, r, i, e, b, l, ks, A, P, amax, Q, s'⟩ := c
  obtain ⟨⟨hp, hr, hi, hne, hks, hmap, hsurj, hprod, hn', hbe, hl, hlb, hQ, hs, hk, hpair, hpair2⟩,
    hnc⟩ := h
  dsimp only [MaCountCert.fib] at *
  rintro ⟨D, hD⟩
  obtain ⟨k₀, ks, rfl⟩ := List.exists_cons_of_ne_nil hne
  have : Fact p.Prime := ⟨hp.prime⟩
  have : NeZero r := ⟨hr.ne'⟩
  let _ : Fintype (Grp (k₀ :: ks)) :=
    Grp.fintype _ fun d hd => Nat.pos_of_dvd_of_pos (hks d hd) (by positivity)
  have hconj (x : Grp (k₀ :: ks)) : p ^ i • x = -x := by
    have := Grp.nsmul_eq_zero (N := p ^ i + 1) (k₀ :: ks) hks x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  have hcardH : Fintype.card (ZMod r × Grp (k₀ :: ks)) = r * (k₀ :: ks).prod := by
    rw [Fintype.card_prod, ZMod.card, Grp.card_eq]
  obtain ⟨Z, hZ⟩ : ∃ Z : ZMod r × Grp (k₀ :: ks) → ℤ, DividedDemands (p ^ l)
      (w.ms.prod / (r * p ^ l * (k₀ :: ks).prod)) w.k w.lam (Fintype.card (Grp w.ms)) Z := by
    rcases hl with rfl | rfl
    · have : NeZero (r * p) := ⟨(Nat.mul_pos hr hp.prime.pos).ne'⟩
      rw [pow_one] at hmap hsurj hprod
      let φ : Grp w.ms →+ ZMod (r * p) × Grp (k₀ :: ks) := linMap w.ms (r * p :: k₀ :: ks) A hmap
      have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
      have hcard : Fintype.card (Grp w.ms) = w.ms.prod / (r * p ^ 1 * (k₀ :: ks).prod) *
          Fintype.card (ZMod (r * p) × Grp (k₀ :: ks)) := by
        rw [Fintype.card_prod, ZMod.card, Grp.card_eq, Grp.card_eq, pow_one,
          Nat.div_mul_cancel hprod]
      obtain ⟨Z, -, hZ⟩ := hD.exists_divided hφ hcard hr hi hconj hn' hbe (by omega)
        (MaRows.cycloFacts_of_mem_maPairs hpair)
      exact ⟨Z, by rw [pow_one] at hZ ⊢; exact hZ⟩
    · have : NeZero (r * p) := ⟨(Nat.mul_pos hr hp.prime.pos).ne'⟩
      have : NeZero (r * p * p) :=
        ⟨(Nat.mul_pos (Nat.mul_pos hr hp.prime.pos) hp.prime.pos).ne'⟩
      have e2 : r * p ^ 2 = r * p * p := by ring
      rw [e2] at hmap hsurj hprod
      let φ : Grp w.ms →+ ZMod (r * p * p) × Grp (k₀ :: ks) :=
        linMap w.ms (r * p * p :: k₀ :: ks) A hmap
      have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
      have hcard : Fintype.card (Grp w.ms) = w.ms.prod / (r * p ^ 2 * (k₀ :: ks).prod) *
          Fintype.card (ZMod (r * p * p) × Grp (k₀ :: ks)) := by
        rw [Fintype.card_prod, ZMod.card, Grp.card_eq, Grp.card_eq, e2,
          Nat.div_mul_cancel hprod]
      obtain ⟨Z, hZ⟩ := hD.exists_divided2 hφ hcard hr hi hconj hn' hbe (by omega)
        (MaRows.cycloFacts_of_mem_maPairs (hpair2 rfl))
        (MaRows.cycloFacts_of_mem_maPairs hpair)
      exact ⟨Z, by rw [sq p] at hZ ⊢; exact hZ⟩
  exact hZ.false_of_anyCountsMag (pow_pos hp.prime.pos l) hQ
    (by rw [Grp.card_eq]; exact hs) hk (by rw [hcardH]; exact hnc)

end SignedDifferenceSets
