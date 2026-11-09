module

public import SignedDifferenceSets.MaDescent

/-!
# C29: Ma's lemma with an extra self-conjugate modulus (C21 × C5)

On `H = ZMod (r p) × K` as in C21, the coset sums `Y` of an SDS satisfy
`p^b ∣ Y(h + u) − Y(h)` for `u = (r, 0)` (C21's divisibility step, `Ma.dvd_contract_sub`), and
for each prime `q ∤ |H|` with `q^(2j) ∣ k − λ` and `q^i h = −h` on `H`, `q^j ∣ Y(h') − Y(h)` (C5,
`IsSDS.contract_congr_pow`). For distinct such primes, `p^b Q ∣ Y(h + u) − Y(h)`, `Q = ∏ q^j`;
`2c < p^b Q` makes `Y` periodic along `u`, and C21's last step (`Ma.eq_zero_of_periodic`) gives
`k = λ`. `MaCombRule` is the statement (`MaRule` with `2c < p^b` relaxed), `maCombRule` its proof;
`MaCombCert` checks a row by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets

open Ma

/-- C29, stated for every group and quotient: `MaRule`'s hypotheses with `2c < p^b` relaxed to
`2c < p^b Q`, `Q = ∏ q^j` over `qs`, triples `(q, i, j)` of distinct primes `q ∤ r p |K|` with
`q^i h = −h` on `ZMod (r p) × K` (`i ≥ 1`) and `q^(2j) ∣ k − λ`. -/
def MaCombRule : Prop :=
  ∀ (G K : Type) [AddCommGroup G] [Fintype G] [AddCommGroup K] [Fintype K] [DecidableEq K]
    (p r i e b c k : ℕ) (lam : ℤ) (qs : List (ℕ × ℕ × ℕ)) [Fact p.Prime] [NeZero (r * p)]
    (φ : G →+ ZMod (r * p) × K), Function.Surjective φ →
    Fintype.card G = c * Fintype.card (ZMod (r * p) × K) → 0 < r → 0 < i →
    (∀ x : K, p ^ i • x = -x) → (p : ℤ) ^ e ∣ (k : ℤ) - lam → (k : ℤ) ≠ lam → 2 * b ≤ e →
    (qs.map Prod.fst).Nodup →
    (∀ t ∈ qs, t.1.Prime ∧ ¬ t.1 ∣ r * p * Fintype.card K ∧ 0 < t.2.1 ∧
      (∀ x : ZMod (r * p) × K, t.1 ^ t.2.1 • x = -x) ∧ (t.1 : ℤ) ^ (2 * t.2.2) ∣ (k : ℤ) - lam) →
    2 * c < p ^ b * (qs.map fun t => t.1 ^ t.2.2).prod →
    (∀ (S : Type) [CommRing S] (x : S), ∑ l ∈ Finset.range p, (x ^ r) ^ l = 0 →
      ∃ y z : S, (p : S) = (x - 1) ^ ((p - 1) * r) * y ∧ (x - 1) ^ ((p - 1) * r) = p * z) →
    ¬ HasSDS G k lam

/-- C21's last step: if `Y` is periodic along `(r, 0)` and `ψ(Y) σ(ψ(Y)) = n` in `A`, then
`p n = 0` in `A`, so `n = 0`. -/
theorem Ma.eq_zero_of_periodic {K : Type*} [AddCommGroup K] [Fintype K] {p r : ℕ}
    [NeZero (r * p)] (hp1 : 1 < p) (hr : 0 < r) {Y : ZMod (r * p) × K → ℤ} {n : ℤ}
    (hnorm : psiHom p r (ofFun Y) * conj p r (psiHom p r (ofFun Y)) = (n : A K p r))
    (hper : ∀ h, Y (h + ((r : ZMod (r * p)), 0)) = Y h) : n = 0 := by
  set y := psiHom (K := K) p r (ofFun Y)
  set g0 : ZMod (r * p) × K := ((r : ZMod (r * p)), 0)
  have hshift : ofFun Y * AddMonoidAlgebra.single g0 1 = ofFun Y := by
    rw [ofFun, Finset.sum_mul]
    simp only [AddMonoidAlgebra.single_mul_single, mul_one]
    exact Fintype.sum_equiv (Equiv.addRight g0) _ _ (fun h => by simp [hper h])
  have hrv : ((r : ℕ) : ZMod (r * p)).val = r := ZMod.val_cast_of_lt (lt_mul_of_one_lt_right hr hp1)
  have hρ : y * AdjoinRoot.root (psi (Rg K) p r) ^ r = y := by
    have := congrArg (psiHom (K := K) p r) hshift
    rw [map_mul, psiHom_single, one_smul] at this
    simp only [g0, hrv, ← AddMonoidAlgebra.one_def, map_one, mul_one] at this
    exact this
  have hl : ∀ l : ℕ, y * (AdjoinRoot.root (psi (Rg K) p r) ^ r) ^ l = y := by
    intro l
    induction l with
    | zero => rw [pow_zero, mul_one]
    | succ l ih => rw [pow_succ, ← mul_assoc, ih, hρ]
  have hpy : (p : A K p r) * y = 0 := by
    calc (p : A K p r) * y = ∑ l ∈ Finset.range p, y * (AdjoinRoot.root _ ^ r) ^ l := by
          rw [Finset.sum_congr rfl (fun l _ => hl l), Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
      _ = y * ∑ l ∈ Finset.range p, (AdjoinRoot.root _ ^ r) ^ l := by rw [Finset.mul_sum]
      _ = 0 := by rw [sum_root_pow, mul_zero]
  have hzero : (((p : ℤ) * n : ℤ) : A K p r) = 0 := by
    rw [Int.cast_mul, ← hnorm, Int.cast_natCast, ← mul_assoc, hpy, zero_mul]
  rcases mul_eq_zero.1 (intCast_eq_zero hp1 hr hzero) with h | h
  · omega
  · exact h

/-- Prime powers of distinct primes that each divide `d` divide it together. -/
theorem natCast_prod_pow_dvd {d : ℤ} :
    ∀ (qs : List (ℕ × ℕ × ℕ)), (qs.map Prod.fst).Nodup → (∀ t ∈ qs, t.1.Prime) →
      (∀ t ∈ qs, (t.1 : ℤ) ^ t.2.2 ∣ d) → (((qs.map fun t => t.1 ^ t.2.2).prod : ℕ) : ℤ) ∣ d
  | [], _, _, _ => by simp
  | t :: qs, hnd, hp, hd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hcop : Nat.Coprime (t.1 ^ t.2.2) (qs.map fun t => t.1 ^ t.2.2).prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro n hn
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hn
      have hne : t.1 ≠ s.1 := fun h => hnd.1 (List.mem_map.2 ⟨s, hs, h.symm⟩)
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hp t List.mem_cons_self)
        (hp s (List.mem_cons_of_mem _ hs))).2 hne)
    rw [List.map_cons, List.prod_cons, Nat.cast_mul]
    refine IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 hcop) ?_ ?_
    · exact_mod_cast hd t List.mem_cons_self
    · exact natCast_prod_pow_dvd qs hnd.2 (fun s hs => hp s (List.mem_cons_of_mem _ hs))
        fun s hs => hd s (List.mem_cons_of_mem _ hs)

/-- C29 (C21 × C5). -/
theorem maCombRule : MaCombRule := by
  intro G K _ _ _ _ _ p r i e b c k lam qs hp _ φ hφ hcard hr hi hc hn hk hb hnd hqs hpb hcert
    ⟨D, hD⟩
  have hp1 : 1 < p := hp.out.one_lt
  have hp0 : p ≠ 0 := by omega
  have hrp : 1 < r * p := lt_of_lt_of_le hp1 (Nat.le_mul_of_pos_left p hr)
  set Q := (qs.map fun t => t.1 ^ t.2.2).prod with hQ
  set Y := contract φ D
  have hH1 : ∃ g : ZMod (r * p) × K, g ≠ 0 :=
    ⟨((1 : ZMod (r * p)), 0), fun h => zmod_one_ne_zero hrp (congrArg Prod.fst h :)⟩
  -- C5 at each `q`, then all of them together.
  have hdq (h h' : ZMod (r * p) × K) : (Q : ℤ) ∣ Y h' - Y h := by
    refine natCast_prod_pow_dvd qs hnd (fun t ht => (hqs t ht).1) fun t ht => ?_
    obtain ⟨hq, hqH, hqi, hqc, hqn⟩ := hqs t ht
    have : Fact t.1.Prime := ⟨hq⟩
    have hH : (Fintype.card (ZMod (r * p) × K) : ZMod t.1) ≠ 0 := by
      rw [Fintype.card_prod, ZMod.card, Ne, ZMod.natCast_eq_zero_iff]
      exact hqH
    exact Int.modEq_iff_dvd.1 (hD.contract_congr_pow φ hφ hcard hqi hqc hH hH1 hqn h h')
  have hcop : Nat.Coprime (p ^ b) Q := by
    rw [hQ, Nat.coprime_list_prod_right_iff]
    intro n hn'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn'
    obtain ⟨hq, hqH, -⟩ := hqs t ht
    have hne : p ≠ t.1 := by
      intro h
      apply hqH
      rw [← h]
      exact dvd_mul_of_dvd_left (dvd_mul_left p r) _
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp.out hq).2 hne)
  -- `p^b Q` divides each difference along `(r, 0)`, which is at most `2c < p^b Q`.
  have hperY : ∀ h, Y (h + ((r : ZMod (r * p)), 0)) = Y h := by
    rintro ⟨x, kk⟩
    have hx : ((x, kk) : ZMod (r * p) × K) + ((r : ZMod (r * p)), 0) =
        (x + (r : ZMod (r * p)), kk) := by simp
    rw [hx]
    have hd : ((p ^ b * Q : ℕ) : ℤ) ∣ Y (x + (r : ZMod (r * p)), kk) - Y (x, kk) := by
      rw [Nat.cast_mul]
      refine IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 hcop) ?_ (hdq _ _)
      rw [Nat.cast_pow]
      exact Ma.dvd_contract_sub hφ hcard hr hi hc hn hb hcert hD x kk
    have hb1 := abs_contract_le φ D (x + (r : ZMod (r * p)), kk)
    have hb2 := abs_contract_le φ D (x, kk)
    rw [card_fibre_eq hφ hcard] at hb1 hb2
    have hlt : |Y (x + (r : ZMod (r * p)), kk) - Y (x, kk)| < ((p ^ b * Q : ℕ) : ℤ) := by
      have h3 := abs_sub (Y (x + (r : ZMod (r * p)), kk)) (Y (x, kk))
      have : (2 * c : ℤ) < ((p ^ b * Q : ℕ) : ℤ) := by exact_mod_cast hpb
      linarith
    have := Int.eq_zero_of_abs_lt_dvd hd hlt
    linarith
  have hY : ∀ g, ∑ h, Y h * Y (h + g) = (if g = 0 then (k : ℤ) - lam else 0) + lam * c := by
    intro g
    by_cases hg : g = 0
    · subst hg
      simp only [add_zero, ite_true]
      rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
        Nat.cast_one]
      ring
    · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcard, ite_eq_right hg, zero_add]
  have hnorm := psiHom_mul_conj (K := K) hp0 hrp hY
  have := Ma.eq_zero_of_periodic hp1 hr hnorm hperY
  exact hk (by linarith)

/-! ### Rows -/

/-- A C29 certificate: C21's fields (`MaRowCert`: `p`, `r = p^(j−1)`, `i`, `e`, `b`, `ks ≠ []`,
forms `A` onto `ZMod (r p) × Grp ks` with preimages `P`) and the extra primes `qs` as
`(q, i_q, j_q)`. -/
structure MaCombCert where
  p : ℕ
  r : ℕ
  i : ℕ
  e : ℕ
  b : ℕ
  ks : List ℕ
  A : List (List ℕ)
  P : List (List ℕ)
  qs : List (ℕ × ℕ × ℕ)
  deriving DecidableEq

/-- C29's hypotheses on the row but the bound, `(p, r)` among `MaRows.maPairs`. -/
def MaCombCert.Valid (w : Row) (c : MaCombCert) : Prop :=
  IsPrimeTD c.p ∧ 0 < c.r ∧ 0 < c.i ∧ c.ks ≠ [] ∧ (∀ d ∈ c.ks, d ∣ c.p ^ c.i + 1) ∧
    MapOk w.ms (c.r * c.p :: c.ks) c.A ∧ SurjCert w.ms (c.r * c.p :: c.ks) c.A c.P ∧
    c.r * c.p * c.ks.prod ∣ w.ms.prod ∧ (c.p : ℤ) ^ c.e ∣ w.k - w.lam ∧ (w.k : ℤ) ≠ w.lam ∧
    2 * c.b ≤ c.e ∧ (c.qs.map Prod.fst).Nodup ∧
    (∀ t ∈ c.qs, IsPrimeTD t.1 ∧ ¬ t.1 ∣ c.r * c.p * c.ks.prod ∧ 0 < t.2.1 ∧
      c.r * c.p ∣ t.1 ^ t.2.1 + 1 ∧ (∀ d ∈ c.ks, d ∣ t.1 ^ t.2.1 + 1) ∧
      (t.1 : ℤ) ^ (2 * t.2.2) ∣ w.k - w.lam) ∧
    (c.p, c.r) ∈ MaRows.maPairs

/-- The hypotheses and C29's bound `2c < p^b Q`, `c = |G| / (r p |K|)`. -/
def MaCombCert.Kills (w : Row) (c : MaCombCert) : Prop :=
  c.Valid w ∧
    2 * (w.ms.prod / (c.r * c.p * c.ks.prod)) < c.p ^ c.b * (c.qs.map fun t => t.1 ^ t.2.2).prod

instance (w : Row) (c : MaCombCert) : Decidable (c.Valid w) := by
  unfold MaCombCert.Valid; infer_instance

instance (w : Row) (c : MaCombCert) : Decidable (c.Kills w) := by
  unfold MaCombCert.Kills; infer_instance

/-- `N + 1` with every factor dividing it negates `ZMod m × Grp ds` when `m ∣ N + 1`. -/
theorem neg_of_dvd_succ {m N : ℕ} {ds : List ℕ} (hm : m ∣ N + 1) (hds : ∀ d ∈ ds, d ∣ N + 1)
    (x : ZMod m × Grp ds) : N • x = -x := by
  have h1 : (N + 1) • x = 0 := Prod.ext (zmod_nsmul_eq_zero hm x.1) (Grp.nsmul_eq_zero ds hds x.2)
  rw [add_smul, one_smul] at h1
  exact eq_neg_of_add_eq_zero_left h1

/-- C29 on a quotient `ZMod (r p) × Grp ks` given by forms. -/
theorem not_hasSDS_of_maCombRule (hrule : MaCombRule) {ms ks : List ℕ} {p r i e b k : ℕ}
    {lam : ℤ} {A P : List (List ℕ)} {qs : List (ℕ × ℕ × ℕ)} (hp : p.Prime) (hr : 0 < r)
    (hi : 0 < i) (hne : ks ≠ []) (hks : ∀ d ∈ ks, d ∣ p ^ i + 1) (hmap : MapOk ms (r * p :: ks) A)
    (hsurj : SurjCert ms (r * p :: ks) A P) (hprod : r * p * ks.prod ∣ ms.prod)
    (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam) (hk : (k : ℤ) ≠ lam) (hbe : 2 * b ≤ e)
    (hnd : (qs.map Prod.fst).Nodup)
    (hqs : ∀ t ∈ qs, IsPrimeTD t.1 ∧ ¬ t.1 ∣ r * p * ks.prod ∧ 0 < t.2.1 ∧
      r * p ∣ t.1 ^ t.2.1 + 1 ∧ (∀ d ∈ ks, d ∣ t.1 ^ t.2.1 + 1) ∧
      (t.1 : ℤ) ^ (2 * t.2.2) ∣ (k : ℤ) - lam)
    (hc : 2 * (ms.prod / (r * p * ks.prod)) < p ^ b * (qs.map fun t => t.1 ^ t.2.2).prod)
    (hcyc : CycloFacts p r) (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst k lam := by
  obtain ⟨k₀, ks, rfl⟩ := List.exists_cons_of_ne_nil hne
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (r * p) := ⟨(Nat.mul_pos hr hp.pos).ne'⟩
  let _ : Fintype (Grp (k₀ :: ks)) :=
    Grp.fintype _ fun d hd => Nat.pos_of_dvd_of_pos (hks d hd) (by positivity)
  let φ : Grp ms →+ ZMod (r * p) × Grp (k₀ :: ks) := linMap ms (r * p :: k₀ :: ks) A hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp ms) =
      ms.prod / (r * p * (k₀ :: ks).prod) * Fintype.card (ZMod (r * p) × Grp (k₀ :: ks)) := by
    rw [Fintype.card_prod, ZMod.card, Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hconj (x : Grp (k₀ :: ks)) : p ^ i • x = -x := by
    have := Grp.nsmul_eq_zero (N := p ^ i + 1) (k₀ :: ks) hks x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  refine hrule (Grp ms) (Grp (k₀ :: ks)) p r i e b _ k lam qs φ hφ hcard hr hi hconj hn hk hbe hnd
    (fun t ht => ?_) hc fun S _ x hx => hcyc S x hx
  obtain ⟨hq, hqH, hqi, hqr, hqk, hqn⟩ := hqs t ht
  exact ⟨hq.prime, by rwa [Grp.card_eq], hqi, neg_of_dvd_succ hqr hqk, hqn⟩

/-- A row C29 kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem MaCombCert.not_hasSDS {w : Row} {c : MaCombCert} (h : c.Kills w)
    (inst : Fintype (Grp w.ms)) : ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨⟨hp, hr, hi, hne, hks, hmap, hsurj, hprod, hn, hk, hbe, hnd, hqs, hpair⟩, hc⟩ := h
  exact not_hasSDS_of_maCombRule maCombRule hp.prime hr hi hne hks hmap hsurj hprod hn hk hbe hnd
    hqs hc (MaRows.cycloFacts_of_mem_maPairs hpair) inst

end SignedDifferenceSets
