module

public import SignedDifferenceSets.MarkedCountsCheck

/-!
# Marked counts per coset with integer counts (C7)

C7's weights (`MarkedCountsCheck`) are an LP certificate: they cannot kill a row whose real
relaxation is feasible. Here the counts stay integers. Under C5's hypotheses the counts
`n_x = #{h : a_h = x}` of an SDS's coset sums on `V = classVals q t₀ c` satisfy `Σ n_x = |H|`,
`Σ n_x x = s'`, `Σ n_x x² = Q` and `Σ n_x maxMarked c x ≥ k` (`IsSDS.countsOk`). `anyCounts`
searches every such integer vector (pruned by `Q ≥ 0`, `Σ n_x (x − t)² ≥ 0` and
`maxMarked ≤ c`, `anyCounts_of`); none for both signs and every residue: no SDS
(`not_hasSDS_of_counts`, per row `ScCert.CountsKill`). N27692 dies this way: its LP optimum
is 306.4 ≥ k = 306, its two integer moment vectors reach 300 and 304.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- `Σ_{x ∈ xs} n x · f x`. -/
def countSum (xs : List ℤ) (n : ℤ → ℕ) (f : ℤ → ℤ) : ℤ := (xs.map fun x => (n x : ℤ) * f x).sum

/-- Integer counts `n` on the values `xs`: `N` values with sum `s`, square sum `Q`, and room
for at least `k` marked elements in cosets of size `c`. -/
structure CountsOk (xs : List ℤ) (n : ℤ → ℕ) (N s Q c k : ℤ) : Prop where
  card : countSum xs n (fun _ => 1) = N
  sum : countSum xs n id = s
  sq : countSum xs n (fun x => x * x) = Q
  marked : k ≤ countSum xs n (maxMarked c)

/-- The search's pruning at a node: `Q ≥ 0`, `Σ n_x (x − t)² = Nt² − 2st + Q ≥ 0` at
`t = s / N`, and at most `cN` marked elements. -/
def pruneOk (c : ℤ) (N : ℕ) (s Q m : ℤ) : Bool :=
  decide (0 ≤ Q) && decide (0 ≤ (N : ℤ) * (s / N) * (s / N) - 2 * s * (s / N) + Q) &&
    decide (m ≤ c * N)

/-- Whether counts on `xs` exist with `N` values, sum `s`, square sum `Q` and at least `m`
marked elements: each count of the head value in `0..N`, then the tail. -/
def anyCounts (c : ℤ) : List ℤ → ℕ → ℤ → ℤ → ℤ → Bool
  | [], N, s, Q, m => N == 0 && s == 0 && Q == 0 && decide (m ≤ 0)
  | x :: xs, N, s, Q, m => pruneOk c N s Q m &&
      (List.range (N + 1)).any fun i =>
        anyCounts c xs (N - i) (s - i * x) (Q - i * (x * x)) (m - i * maxMarked c x)

theorem countSum_cons (x : ℤ) (xs : List ℤ) (n : ℤ → ℕ) (f : ℤ → ℤ) :
    countSum (x :: xs) n f = n x * f x + countSum xs n f := by
  simp [countSum]

theorem countSum_le {xs : List ℤ} (n : ℤ → ℕ) {f g : ℤ → ℤ} (h : ∀ x, f x ≤ g x) :
    countSum xs n f ≤ countSum xs n g := by
  induction xs with
  | nil => simp [countSum]
  | cons x xs ih =>
    rw [countSum_cons, countSum_cons]
    have := mul_le_mul_of_nonneg_left (h x) (Nat.cast_nonneg (α := ℤ) (n x))
    linarith

theorem countSum_const (xs : List ℤ) (n : ℤ → ℕ) (b : ℤ) :
    countSum xs n (fun _ => b) = b * countSum xs n (fun _ => 1) := by
  induction xs with
  | nil => simp [countSum]
  | cons x xs ih => rw [countSum_cons, countSum_cons, ih]; ring

theorem countSum_nonneg (xs : List ℤ) (n : ℤ → ℕ) {f : ℤ → ℤ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ countSum xs n f := by
  have := countSum_le (xs := xs) n h
  rwa [countSum_const, zero_mul] at this

theorem countSum_sq_sub (xs : List ℤ) (n : ℤ → ℕ) (t : ℤ) :
    countSum xs n (fun x => (x - t) * (x - t)) = countSum xs n (fun _ => 1) * t * t -
      2 * countSum xs n id * t + countSum xs n (fun x => x * x) := by
  induction xs with
  | nil => simp [countSum]
  | cons x xs ih => simp only [countSum_cons, ih, id]; ring

/-- `Nt² − 2st + Q = Σ n_x (x − t)² ≥ 0`. -/
theorem disc_nonneg (xs : List ℤ) (n : ℤ → ℕ) (t : ℤ) :
    0 ≤ countSum xs n (fun _ => 1) * t * t - 2 * countSum xs n id * t +
      countSum xs n (fun x => x * x) := by
  rw [← countSum_sq_sub]
  exact countSum_nonneg xs n fun x => mul_self_nonneg _

theorem maxMarked_le (c x : ℤ) : maxMarked c x ≤ c := by
  unfold maxMarked; split_ifs <;> omega

/-- The search finds every count vector: counts meeting the targets make `anyCounts` true. -/
theorem anyCounts_of (c : ℤ) (n : ℤ → ℕ) : ∀ (xs : List ℤ) (N : ℕ) (s Q m : ℤ),
    countSum xs n (fun _ => 1) = N → countSum xs n id = s →
    countSum xs n (fun x => x * x) = Q → m ≤ countSum xs n (maxMarked c) →
    anyCounts c xs N s Q m = true
  | [], N, s, Q, m, h1, h2, h3, h4 => by
    simp only [countSum, List.map_nil, List.sum_nil] at h1 h2 h3 h4
    subst h2 h3
    have hN : N = 0 := by exact_mod_cast h1.symm
    simp [anyCounts, hN, h4]
  | x :: xs, N, s, Q, m, h1, h2, h3, h4 => by
    have hp : pruneOk c N s Q m = true := by
      have hQ : 0 ≤ Q := h3 ▸ countSum_nonneg _ n fun x => mul_self_nonneg x
      have hd := disc_nonneg (x :: xs) n (s / N)
      rw [h1, h2, h3] at hd
      have hm : m ≤ c * N := by
        have := countSum_le (xs := x :: xs) n (maxMarked_le c)
        rw [countSum_const, h1] at this
        linarith
      simp [pruneOk, hQ, hd, hm]
    rw [countSum_cons] at h1 h2 h3 h4
    have hr := countSum_nonneg xs n (f := fun _ => 1) fun _ => zero_le_one
    have hx : n x ≤ N := by
      have : (n x : ℤ) ≤ N := by linarith
      exact_mod_cast this
    have hrec := anyCounts_of c n xs (N - n x) (s - n x * x) (Q - n x * (x * x))
      (m - n x * maxMarked c x) (by push_cast [Nat.cast_sub hx]; linarith)
      (by simp only [id] at h2 ⊢; linarith) (by linarith) (by linarith)
    simp only [anyCounts, hp, Bool.true_and, List.any_eq_true, List.mem_range]
    exact ⟨n x, Nat.lt_succ_of_le hx, hrec⟩

theorem countSum_reverse (xs : List ℤ) (n : ℤ → ℕ) (f : ℤ → ℤ) :
    countSum xs.reverse n f = countSum xs n f := by
  simp [countSum, List.map_reverse, List.sum_reverse]

theorem CountsOk.reverse {xs : List ℤ} {n : ℤ → ℕ} {N s Q c k : ℤ}
    (h : CountsOk xs n N s Q c k) : CountsOk xs.reverse n N s Q c k :=
  ⟨by rw [countSum_reverse]; exact h.card, by rw [countSum_reverse]; exact h.sum,
    by rw [countSum_reverse]; exact h.sq, by rw [countSum_reverse]; exact h.marked⟩

/-- The values in search order: ascending for `s' ≥ 0`, descending otherwise (fewer nodes). -/
def orderVals (s' : ℤ) (xs : List ℤ) : List ℤ := if 0 ≤ s' then xs else xs.reverse

/-- No counts on the values (in either order) meet the targets when the search finds none. -/
theorem not_countsOk_of_anyCounts {xs : List ℤ} {n : ℤ → ℕ} {N : ℕ} {s Q c k : ℤ}
    (h : anyCounts c (orderVals s xs) N s Q k = false) : ¬ CountsOk xs n N s Q c k := by
  intro hc
  have hc' : CountsOk (orderVals s xs) n N s Q c k := by
    unfold orderVals; split_ifs
    · exact hc
    · exact hc.reverse
  rw [anyCounts_of c n _ N s Q k hc'.card hc'.sum hc'.sq hc'.marked] at h
  exact Bool.noConfusion h

/-- How many `h` have `a h = x`. -/
def countOf {H : Type*} [Fintype H] (a : H → ℤ) (x : ℤ) : ℕ :=
  (Finset.univ.filter fun h => a h = x).card

/-- Over values `xs` without repeats that hold every `a h`, the counts of `a` sum `f` as `a`
does. -/
theorem countSum_countOf {H : Type*} [Fintype H] (a : H → ℤ) {xs : List ℤ} (hxs : xs.Nodup)
    (ha : ∀ h, a h ∈ xs) (f : ℤ → ℤ) : countSum xs (countOf a) f = ∑ h, f (a h) := by
  unfold countSum
  rw [← List.sum_toFinset _ hxs, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := xs.toFinset) (g := a) (fun h _ => List.mem_toFinset.2 (ha h))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_congr rfl fun h hh => by rw [(Finset.mem_filter.1 hh).2], Finset.sum_const,
    nsmul_eq_mul, countOf]

theorem classVals_nodup (q t0 c : ℤ) : (classVals q t0 c).Nodup :=
  ((List.nodup_range).map fun a b h => by simpa using h).filter _

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
  [DecidableEq H]

/-- C7 with integer counts: under C5's hypotheses the coset sums of an SDS have sign sum
`s' ∈ {s, −s}`, all lie in `V = classVals q t₀ c` for a residue `0 ≤ t₀ < q`, and their counts
on `V` meet `CountsOk` with `N = |H|` and `Q = k + λ(c − 1)`. -/
theorem IsSDS.countsOk {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) {p i j : ℕ} [Fact p.Prime] (hi : 0 < i)
    (hc : ∀ h : H, p ^ i • h = -h) (hH : (Fintype.card H : ZMod p) ≠ 0) (hH1 : ∃ g : H, g ≠ 0)
    (hn : (p : ℤ) ^ (2 * j) ∣ k - lam) {s : ℤ}
    (hs : s ^ 2 = k + lam * ((c : ℤ) * Fintype.card H - 1)) :
    ∃ s' ∈ [s, -s], ∃ t0 ∈ Finset.Ico (0 : ℤ) ((p : ℤ) ^ j),
      CountsOk (classVals ((p : ℤ) ^ j) t0 c) (countOf (contract φ D)) (Fintype.card H) s'
        (k + lam * ((c : ℤ) - 1)) c k := by
  set a := contract φ D
  set q : ℤ := (p : ℤ) ^ j
  have hq : 0 < q := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) j
  have hcong (h : H) : a h ≡ a 0 [ZMOD q] :=
    hD.contract_congr_pow φ hφ hcard hi hc hH hH1 hn h 0
  have ht (h : H) : q ∣ a h - a 0 % q :=
    Int.modEq_iff_dvd.1 ((hcong h).trans (Int.mod_modEq (a 0) q).symm).symm
  have hb (h : H) : |a h| ≤ c := by
    have := abs_contract_le φ D h
    rwa [card_fibre_eq hφ hcard] at this
  have hm (h : H) : (marked φ D h : ℤ) ≤ c := by
    have := marked_le_card φ D h
    rw [card_fibre_eq hφ hcard] at this
    exact_mod_cast this
  have hQ : ∑ h, a h * a h = k + lam * ((c : ℤ) - 1) := by
    rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
      Nat.cast_one]
  have hsq := hD.sum_contract_sq φ hφ hcard
  rw [← hs] at hsq
  have hmem : ∑ h, a h ∈ [s, -s] := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact List.mem_cons.2 (Or.inl h)
    · exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 h))
  have ht0 : a 0 % q ∈ Finset.Ico (0 : ℤ) q :=
    Finset.mem_Ico.2 ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩
  have hval (h : H) : a h ∈ classVals q (a 0 % q) c := mem_classVals (hb h) (ht h)
  have hsum := countSum_countOf a (classVals_nodup q (a 0 % q) c) hval
  refine ⟨_, hmem, _, ht0, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hsum]; simp
  · rw [hsum]; rfl
  · rw [hsum, hQ]
  · rw [hsum]
    calc (k : ℤ) = ∑ h, (marked φ D h : ℤ) := (hD.sum_marked φ).symm
      _ ≤ ∑ h, maxMarked c (a h) :=
          Finset.sum_le_sum fun h _ => marked_le_maxMarked φ D h (hm h)

omit [DecidableEq H] in
/-- C7, integer form: no SDS when, under C5's hypotheses, `anyCounts` finds no counts for
either sign sum `s' = ±s` and any residue `0 ≤ t₀ < p^j`. -/
theorem not_hasSDS_of_counts (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) {p i j : ℕ} [Fact p.Prime] (hi : 0 < i)
    (hc : ∀ h : H, p ^ i • h = -h) (hH : (Fintype.card H : ZMod p) ≠ 0) (hH1 : ∃ g : H, g ≠ 0)
    {k : ℕ} {lam : ℤ} (hn : (p : ℤ) ^ (2 * j) ∣ k - lam) {s : ℤ}
    (hs : s ^ 2 = k + lam * ((c : ℤ) * Fintype.card H - 1))
    (hfail : ∀ s' ∈ [s, -s], ∀ t0 ∈ Finset.Ico (0 : ℤ) ((p : ℤ) ^ j),
      anyCounts c (orderVals s' (classVals ((p : ℤ) ^ j) t0 c)) (Fintype.card H) s'
        (k + lam * ((c : ℤ) - 1)) k = false) :
    ¬ HasSDS G k lam := by
  classical
  rintro ⟨D, hD⟩
  obtain ⟨s', hs', t0, ht0, hok⟩ := hD.countsOk φ hφ hcard hi hc hH hH1 hn hs
  exact not_countsOk_of_anyCounts (hfail s' hs' t0 ht0) hok

/-- C7's integer test kills the row: C5's data is valid, `s² = k + λ(v − 1)`, and for both
signs and every residue `anyCounts` finds no counts. -/
def ScCert.CountsKill (r : Row) (c : ScCert) : Prop :=
  c.Valid r ∧ c.s ^ 2 = r.k + r.lam * ((r.ms.prod : ℤ) - 1) ∧
    ∀ s' ∈ [c.s, -c.s], ∀ t ∈ List.range (c.p ^ c.j),
      anyCounts ((r.ms.prod / c.ds.prod : ℕ) : ℤ)
          (orderVals s' (classVals ((c.p : ℤ) ^ c.j) t ((r.ms.prod / c.ds.prod : ℕ) : ℤ)))
          c.ds.prod s' (r.k + r.lam * (((r.ms.prod / c.ds.prod : ℕ) : ℤ) - 1)) r.k = false

instance (r : Row) (c : ScCert) : Decidable (c.CountsKill r) := by
  unfold ScCert.CountsKill ScCert.Valid; infer_instance

/-- A row C7's integer test kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem ScCert.not_hasSDS_of_countsKill {r : Row} {c : ScCert} (h : c.CountsKill r)
    (inst : Fintype (Grp r.ms)) : ¬ @HasSDS (Grp r.ms) _ inst r.k r.lam := by
  obtain ⟨⟨hp, hi, hms, hdv, hds, hpH, hH1, hn, -⟩, hs, hfail⟩ := h
  have : Fact c.p.Prime := ⟨hp.prime⟩
  let _ : Fintype (Grp c.ds) := Grp.fintype c.ds (Dvds.pos _ _ hdv hms)
  have hprod := Dvds.prod_dvd _ _ hdv
  have hcard : Fintype.card (Grp r.ms) =
      (r.ms.prod / c.ds.prod) * Fintype.card (Grp c.ds) := by
    rw [Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hc (x : Grp c.ds) : c.p ^ c.i • x = -x := by
    have := Grp.nsmul_eq_zero (N := c.p ^ c.i + 1) c.ds hds x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  have hH : (Fintype.card (Grp c.ds) : ZMod c.p) ≠ 0 := by
    rw [Grp.card_eq, Ne, ZMod.natCast_eq_zero_iff]
    exact hpH
  refine not_hasSDS_of_counts _ (quot_surjective r.ms c.ds hdv) hcard hi hc hH
    (Grp.exists_ne_zero c.ds hH1) hn (s := c.s) ?_ ?_
  · rw [hs, Grp.card_eq, ← Nat.cast_mul, Nat.div_mul_cancel hprod]
  · intro s' hs' t ht
    obtain ⟨ht0, htq⟩ := Finset.mem_Ico.1 ht
    have htn : t.toNat < c.p ^ c.j := by
      have : (t.toNat : ℤ) < (c.p : ℤ) ^ c.j := by
        rw [Int.toNat_of_nonneg ht0]; exact htq
      exact_mod_cast this
    have := hfail s' hs' t.toNat (List.mem_range.2 htn)
    rw [Int.toNat_of_nonneg ht0] at this
    rwa [Grp.card_eq]

set_option maxRecDepth 100000 in
/-- N27692 (320, 306, 162) in C₂ × C₄ × C₄₀: quotient C₂ × C₄ × C₄ (`c = 10`), `p = 3`
(`3 ≡ −1` mod 4), `s = 228`, `Q = 1764`; no integer counts for `±228` and residues 0, 1, 2. -/
theorem n27692_countsKill :
    (⟨3, 1, 1, [2, 4, 4], 228⟩ : ScCert).CountsKill ⟨27692, [2, 4, 40], 306, 162⟩ := by
  decide +kernel

/-- N27692: no (320, 306, 162) SDS in C₂ × C₄ × C₄₀. -/
theorem n27692_not_hasSDS : ¬ HasSDS (ZMod 2 × ZMod 4 × ZMod 40) 306 162 :=
  ScCert.not_hasSDS_of_countsKill n27692_countsKill _

end SignedDifferenceSets
