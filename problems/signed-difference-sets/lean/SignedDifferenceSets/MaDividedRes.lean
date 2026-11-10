module

public import SignedDifferenceSets.MaDividedCounts
public import SignedDifferenceSets.MaComb

/-!
# C38: the divided search below a Ma quotient with Turyn's residue class

One level below a C21 quotient `ZMod (r p) × K` (`b ≥ 1`, any prime `p`), `Z = W / p` on
`H' = ZMod r × K` meets `DividedDemands p c` (`IsSDS.exists_divided`). For a prime `q ≠ p` with
`q ∤ |H'|`, `q^i h = −h` on `H'` and `q^(2j) ∣ k − λ`, C5 makes the coset sums `W` agree mod `q^j`,
and `q ∤ p` passes this to `Z`; over several such primes `Z` is constant mod `M = ∏ q^j`
(`IsSDS.prod_dvd_divided_sub`). Negation and translation keep this, so `noVectorRes`, the vector
search with every coordinate congruent to the first mod `M` (`noVectorRes_sound`), rules the SDS
out for each bound on the absolute sum (`IsSDS.false_of_maDividedRes`; a list of bounds as C36's,
so `p = 2` is allowed). `MaDivResCert` checks a row's hypotheses by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets

open Ma

/-! ### The search -/

/-- `go` with every coordinate congruent to `x0` mod `M`. -/
def goRes (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s top M x0 : ℤ) :
    ℕ → List ℤ → ℤ → ℤ → ℤ → Bool
  | 0, pre, sum, sq, abs => !leafOK n add Q t k s pre.reverse sum sq abs
  | rem + 1, pre, sum, sq, abs =>
    cut c Q s (rem + 1) sum sq ||
      allRange (fun x => decide (Q - sq < x * x) || (x - x0) % M != 0 ||
        goRes n add c Q t k s top M x0 rem (x :: pre) (sum + x) (sq + x * x) (abs + |x|))
        (-top) (2 * top + 1).toNat

/-- `noVector` with every coordinate congruent to the first mod `M`. -/
def noVectorRes (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s M : ℤ) : Bool :=
  cut c Q s n 0 0 ||
    allRange (fun x => decide (Q < x * x) ||
      goRes n add c Q t k s |x| M x (n - 1) [x] x (x * x) |x|) (-c) (2 * c + 1).toNat

theorem goRes_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s top M x0 : ℤ} :
    ∀ (w pre : List ℤ) (sum sq abs : ℤ),
      goRes n add c Q t k s top M x0 w.length pre sum sq abs = true →
      (∀ y ∈ w, |y| ≤ top) → (∀ y ∈ w, |y| ≤ c) → (∀ y ∈ w, (y - x0) % M = 0) →
      sum + w.sum = s → sq + sqSum w = Q → abs + absSum w ≤ k →
      (k - (abs + absSum w)) % 2 = 0 → shiftsOK n add t (pre.reverse ++ w) = true → False
  | [], pre, sum, sq, abs, h, _, _, _, hs, hq, ha, hp, hw => by
    simp only [List.sum_nil, add_zero, sqSum, absSum, List.map_nil, List.append_nil] at *
    simp [goRes, leafOK, hs, hq, ha, hp, hw] at h
  | x :: w, pre, sum, sq, abs, h, ht, hc, hm, hs, hq, ha, hp, hw => by
    have hcut := cut_false (x :: w) hc hs hq
    simp only [List.length_cons, goRes] at h
    rw [List.length_cons] at hcut
    rw [hcut, Bool.false_or] at h
    simp only [List.mem_cons, forall_eq_or_imp] at ht hc hm
    have hx := allRange_abs h ht.1
    simp only [sqSum, absSum, List.map_cons, List.sum_cons] at hs hq ha hp
    have hsq : ¬ Q - sq < x * x := by have := sqSum_nonneg w; simp only [sqSum] at this; linarith
    simp only [hsq, hm.1, decide_false, bne_self_eq_false, Bool.false_or] at hx
    exact goRes_sound w (x :: pre) (sum + x) (sq + x * x) (abs + |x|) hx ht.2 hc.2 hm.2
      (by linarith) (by simp only [sqSum]; linarith) (by simp only [absSum]; linarith)
      (by simp only [absSum]; rw [show abs + |x| + absSum w = abs + (|x| + absSum w) by ring]
          exact hp)
      (by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hw)

/-- `noVectorRes` is `true` only if no vector with every coordinate congruent to the first mod
`M` meets the demands. -/
theorem noVectorRes_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s M : ℤ}
    (h : noVectorRes n add c Q t k s M = true) (x : ℤ) (w : List ℤ) (hn : (x :: w).length = n)
    (hx : |x| ≤ c) (htop : ∀ y ∈ w, |y| ≤ |x|) (hc : ∀ y ∈ w, |y| ≤ c)
    (hm : ∀ y ∈ w, (y - x) % M = 0) (hs : (x :: w).sum = s) (hq : sqSum (x :: w) = Q)
    (ha : absSum (x :: w) ≤ k) (hp : (k - absSum (x :: w)) % 2 = 0)
    (hw : shiftsOK n add t (x :: w) = true) : False := by
  have hcall : ∀ y ∈ x :: w, |y| ≤ c := by
    simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨hx, hc⟩
  have hcut := cut_false (sum := 0) (sq := 0) (x :: w) hcall (by simpa using hs)
    (by simpa using hq)
  rw [hn] at hcut
  rw [noVectorRes, hcut, Bool.false_or] at h
  have hr := allRange_abs h hx
  simp only [sqSum, absSum, List.map_cons, List.sum_cons] at hs hq ha hp
  have hsq : ¬ Q < x * x := by have := sqSum_nonneg w; simp only [sqSum] at this; linarith
  simp only [hsq, decide_false, Bool.false_or] at hr
  have hlen : n - 1 = w.length := by simp at hn; omega
  rw [hlen] at hr
  exact goRes_sound w [x] x (x * x) |x| hr htop hc hm (by linarith)
    (by simp only [sqSum]; linarith) (by simp only [absSum]; linarith)
    (by simp only [absSum]; exact hp) (by simpa using hw)

section Demands

variable {H : Type*} [AddCommGroup H] [Fintype H] [Indexed H]

/-- A vector meeting `DemandsQ`, constant mod `M`, with `Σ b = s` and `|b 0|` largest,
contradicts `noVectorRes`. -/
theorem false_of_noVectorResQ {c k : ℕ} {Q t s M : ℤ} {b : H → ℤ}
    (hn : noVectorRes (Indexed.size H) (Indexed.addIdx H) c Q t k s M = true)
    (hb : DemandsQ c Q t k b) (hres : ∀ h h', M ∣ b h - b h') (hmax : ∀ h, |b h| ≤ |b 0|)
    (hs : ∑ h, b h = s) : False := by
  set n := Indexed.size H
  set e : H ≃ Fin n := Indexed.equiv
  have hpos : 0 < n := (e 0).pos
  have he0 : e.symm ⟨0, hpos⟩ = 0 := e.symm_apply_eq.2 (Fin.ext Indexed.equiv_zero.symm)
  set F : Fin n → ℤ := fun i => b (e.symm i)
  have hsum (f : ℤ → ℤ) : ((List.ofFn F).map f).sum = ∑ h, f (b h) := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact e.symm.sum_comp (fun h => f (b h))
  have hmem : ∀ y ∈ List.ofFn F, ∃ h, b h = y := by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨_, rfl⟩
  have hne : List.ofFn F ≠ [] := by
    intro h
    have := List.length_ofFn (f := F)
    rw [h] at this
    simp at this
    omega
  obtain ⟨x, w, hL⟩ := List.exists_cons_of_ne_nil hne
  have hx : x = b 0 := by
    have := getD_ofFn F hpos
    rw [hL] at this
    simpa [F, he0] using this
  have hw : ∀ y ∈ w, ∃ h, b h = y := fun y hy => hmem y (hL ▸ List.mem_cons_of_mem x hy)
  refine noVectorRes_sound hn x w (by rw [← hL, List.length_ofFn]) (hx ▸ hb.bound 0)
    (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hx ▸ hmax h
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hb.bound h
  · obtain ⟨h, rfl⟩ := hw y hy
    rw [hx]
    exact Int.emod_eq_zero_of_dvd (hres h 0)
  · rw [← hL, ← hs]
    simpa using hsum id
  · rw [← hL, ← hb.sq]
    exact hsum fun y => y * y
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.abs
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.parity
  · rw [← hL, shiftsOK, allTo_iff]
    intro g hg
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · simp
    set gH := e.symm ⟨g, hg⟩
    have hgH : (e gH : ℕ) = g := by simp [gH]
    have hgH0 : gH ≠ 0 := by
      intro h0
      have := hgH
      rw [h0, Indexed.equiv_zero] at this
      omega
    simp only [Bool.or_eq_true, beq_iff_eq]
    right
    rw [← hb.corr gH hgH0, sumTo_eq, ← sum_equiv (G := H)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hgH, ← Indexed.equiv_add, getD_ofFn F (e u).isLt, getD_ofFn F (e (u + gH)).isLt]
    simp [F]

/-- `DemandsQ`, `(Σ b)² = s²` and `b` constant mod `M` contradict `noVectorRes` (negate, then
translate the largest entry to `0`). -/
theorem false_of_noVectorResQ' {c k : ℕ} {Q t s M : ℤ} {b : H → ℤ}
    (hn : noVectorRes (Indexed.size H) (Indexed.addIdx H) c Q t k s M = true)
    (hb : DemandsQ c Q t k b) (hres : ∀ h h', M ∣ b h - b h')
    (hsq : (∑ h, b h) * (∑ h, b h) = s * s) : False := by
  have key : ∀ b : H → ℤ, DemandsQ c Q t k b → (∀ h h', M ∣ b h - b h') → ∑ h, b h = s →
      False := by
    intro b hb hres hbs
    obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => |b h|)
      Finset.univ_nonempty
    refine false_of_noVectorResQ hn (hb.translate h₀) (fun h h' => hres _ _) (fun h => ?_) ?_
    · simpa using hmax (h + h₀) (Finset.mem_univ _)
    · rw [← hbs]
      exact Fintype.sum_equiv (Equiv.addRight h₀) _ b fun _ => rfl
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key b hb hres h1
  · refine key _ hb.neg (fun h h' => ?_) (by rw [Finset.sum_neg_distrib, h1, neg_neg])
    rw [neg_sub_neg]
    exact (hres h' h)

end Demands

/-! ### Turyn's residue class on the divided vector -/

/-- C5 on the divided vector: if `W = p Z` are the coset sums along `χ`, then for primes `q ≠ p`
with `q ∤ |H|`, `q^i h = −h` on `H` and `q^(2j) ∣ k − λ`, `Z` is constant mod `∏ q^j`. -/
theorem IsSDS.prod_dvd_divided_sub {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H]
    [Fintype H] [DecidableEq H] {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    {χ : G →+ H} (hχ : Function.Surjective χ) {c : ℕ} (hcard : Fintype.card G = c * Fintype.card H)
    {p : ℕ} (hp : p.Prime) {Z : H → ℤ} (hWZ : ∀ y, contract χ D y = p * Z y)
    (qs : List (ℕ × ℕ × ℕ)) (hnd : (qs.map Prod.fst).Nodup)
    (hqs : ∀ u ∈ qs, u.1.Prime ∧ u.1 ≠ p ∧ ¬ u.1 ∣ Fintype.card H ∧ 0 < u.2.1 ∧
      (∀ x : H, u.1 ^ u.2.1 • x = -x) ∧ (u.1 : ℤ) ^ (2 * u.2.2) ∣ (k : ℤ) - lam) (y y' : H) :
    (((qs.map fun u => u.1 ^ u.2.2).prod : ℕ) : ℤ) ∣ Z y - Z y' := by
  refine natCast_prod_pow_dvd qs hnd (fun u hu => (hqs u hu).1) fun u hu => ?_
  obtain ⟨hq, hqp, hqH, hqi, hqc, hqn⟩ := hqs u hu
  have : Fact u.1.Prime := ⟨hq⟩
  by_cases hyy : y = y'
  · rw [hyy, sub_self]
    exact dvd_zero _
  have hH : (Fintype.card H : ZMod u.1) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hqH
  have hcong := hD.contract_congr_pow χ hχ hcard hqi hqc hH ⟨y - y', sub_ne_zero.2 hyy⟩ hqn y' y
  rw [Int.modEq_iff_dvd, hWZ, hWZ, ← mul_sub] at hcong
  have hcop : IsCoprime ((u.1 : ℤ) ^ u.2.2) (p : ℤ) := by
    rw [← Nat.cast_pow]
    exact Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hp).2 hqp))
  exact hcop.dvd_of_dvd_mul_left hcong

/-- C38: one level below a C21 quotient `ZMod (r p) × K` with `b ≥ 1` (any prime `p`), `Z = W / p`
on `ZMod r × K` meets `DemandsQ c Q t k'` for some bound `k'` of `bounds`, `(Σ Z)² = s'²`, and is
constant mod `M = ∏ q^j` over `qs`; a `noVectorRes` check with each bound leaves no SDS. -/
theorem IsSDS.false_of_maDividedRes {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K]
    [Fintype K] {p r i e b c k : ℕ} {lam Q t s' : ℤ} {bounds : List ℕ}
    {qs : List (ℕ × ℕ × ℕ)} [Indexed (ZMod r × K)] [hp : Fact p.Prime] [NeZero (r * p)]
    [NeZero r] {φ : G →+ ZMod (r * p) × K} (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * Fintype.card (ZMod (r * p) × K)) (hr : 0 < r) (hi : 0 < i)
    (hc : ∀ x : K, p ^ i • x = -x) (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam) (hb : 2 * b ≤ e)
    (hb1 : 0 < b) (hcert : CycloFacts p r)
    (hQ : (p : ℤ) ^ 2 * Q = k + lam * ((p * c : ℕ) - 1)) (ht : (p : ℤ) * t = lam * c)
    (hs : ((p : ℤ) * s') * ((p : ℤ) * s') = k + lam * ((Fintype.card G : ℤ) - 1))
    (hbounds : ∀ A ∈ List.range (k + 1), p * A ≤ k → (k - p * A) % 2 = 0 →
      ∃ k' ∈ bounds, A ≤ k' ∧ (k' - A) % 2 = 0)
    (hnd : (qs.map Prod.fst).Nodup)
    (hqs : ∀ u ∈ qs, u.1.Prime ∧ u.1 ≠ p ∧ ¬ u.1 ∣ Fintype.card (ZMod r × K) ∧ 0 < u.2.1 ∧
      (∀ x : ZMod r × K, u.1 ^ u.2.1 • x = -x) ∧ (u.1 : ℤ) ^ (2 * u.2.2) ∣ (k : ℤ) - lam)
    (hnv : ∀ k' ∈ bounds, noVectorRes (Indexed.size (ZMod r × K)) (Indexed.addIdx (ZMod r × K))
      c Q t k' s' (((qs.map fun u => u.1 ^ u.2.2).prod : ℕ) : ℤ) = true)
    {D : G → SignType} (hD : IsSDS k lam D) : False := by
  classical
  obtain ⟨Z, hWZ, hZ⟩ := hD.exists_divided hφ hcard hr hi hc hn hb hb1 hcert
  have hcardp : Fintype.card G = p * c * Fintype.card (ZMod r × K) := by
    rw [hcard, Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hχ : Function.Surjective ((maQuot K r p).comp φ) := (maQuot_surjective K r p).comp hφ
  have hres := hD.prod_dvd_divided_sub hχ hcardp hp.out hWZ qs hnd hqs
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hp0.ne'
  -- the bound `k'` that covers the absolute sum
  set A := ∑ y, |Z y| with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun y _ => abs_nonneg _
  have habs := hZ.abs
  have hpar := hZ.parity
  rw [← hAdef] at habs hpar
  obtain ⟨n, hnA⟩ : ∃ n : ℕ, A = n := ⟨A.toNat, (Int.toNat_of_nonneg hA0).symm⟩
  rw [hnA] at habs hpar
  have hle : p * n ≤ k := by exact_mod_cast habs
  have hpar' : (k - p * n) % 2 = 0 := by
    have hm : ((p * n : ℕ) : ℤ) = (p : ℤ) * n := by push_cast; ring
    rw [← hm] at hpar
    generalize p * n = m at *
    omega
  have hmem : n ∈ List.range (k + 1) := by
    have hn' : n ≤ p * n := Nat.le_mul_of_pos_left n hp.out.pos
    exact List.mem_range.2 (by omega)
  obtain ⟨k', hk', hAk, hpk⟩ := hbounds n hmem hle hpar'
  have hdem : DemandsQ c Q t k' Z := by
    refine ⟨hZ.bound, ?_, fun g hg => ?_, ?_, ?_⟩
    · exact mul_left_cancel₀ hp2 (hZ.sq.trans hQ.symm)
    · have h1 := hZ.corr g hg
      have h2 : (p : ℤ) ^ 2 * ∑ y, Z y * Z (y + g) = (p : ℤ) ^ 2 * t := by
        rw [h1]
        push_cast
        linear_combination -(p : ℤ) * ht
      exact mul_left_cancel₀ hp2 h2
    · rw [← hAdef, hnA]
      exact_mod_cast hAk
    · rw [← hAdef, hnA]
      have := hpk
      zify [hAk] at this
      exact this
  have hsqZ : (∑ y, Z y) * (∑ y, Z y) = s' * s' := by
    have h := hZ.sum.trans hs.symm
    exact mul_left_cancel₀ hp2 (by linear_combination h)
  exact false_of_noVectorResQ' (hnv k' hk') hdem hres hsqZ

/-! ### Rows -/

/-- A C38 certificate: C21's fields (`p`, `r = p^(j−1)`, `i`, `e`, `b ≥ 1`, `ks ≠ []`, forms `A`
onto `ZMod (r p) × Grp ks` with preimages `P`), the bounds, the divided demands and the primes `qs`
as `(q, i_q, j_q)`. -/
structure MaDivResCert where
  p : ℕ
  r : ℕ
  i : ℕ
  e : ℕ
  b : ℕ
  ks : List ℕ
  A : List (List ℕ)
  P : List (List ℕ)
  bounds : List ℕ
  Q : ℤ
  t : ℤ
  s' : ℤ
  qs : List (ℕ × ℕ × ℕ)
  deriving DecidableEq

/-- The modulus `M = ∏ q^(j_q)`. -/
def MaDivResCert.M (c : MaDivResCert) : ℕ := (c.qs.map fun u => u.1 ^ u.2.2).prod

/-- C38's hypotheses on the row, `c = |G| / (r p |K|)`, `(p, r)` among `MaRows.maPairs`, each
`q` prime, `q ∤ r p ∏ ks`, `q^(i_q) ≡ −1` mod `r` and mod each `d ∈ ks`, `q^(2 j_q) ∣ k − λ`. -/
def MaDivResCert.Valid (w : Row) (c : MaDivResCert) : Prop :=
  IsPrimeTD c.p ∧ 0 < c.r ∧ 0 < c.i ∧ c.ks ≠ [] ∧ (∀ d ∈ c.ks, d ∣ c.p ^ c.i + 1) ∧
    MapOk w.ms (c.r * c.p :: c.ks) c.A ∧ SurjCert w.ms (c.r * c.p :: c.ks) c.A c.P ∧
    c.r * c.p * c.ks.prod ∣ w.ms.prod ∧ (c.p : ℤ) ^ c.e ∣ w.k - w.lam ∧ 2 * c.b ≤ c.e ∧
    0 < c.b ∧
    (c.p : ℤ) ^ 2 * c.Q =
      w.k + w.lam * ((c.p * (w.ms.prod / (c.r * c.p * c.ks.prod)) : ℕ) - 1) ∧
    (c.p : ℤ) * c.t = w.lam * (w.ms.prod / (c.r * c.p * c.ks.prod) : ℕ) ∧
    ((c.p : ℤ) * c.s') * ((c.p : ℤ) * c.s') = w.k + w.lam * ((w.ms.prod : ℤ) - 1) ∧
    (∀ A ∈ List.range (w.k + 1), c.p * A ≤ w.k → (w.k - c.p * A) % 2 = 0 →
      ∃ k' ∈ c.bounds, A ≤ k' ∧ (k' - A) % 2 = 0) ∧
    (c.qs.map Prod.fst).Nodup ∧
    (∀ u ∈ c.qs, IsPrimeTD u.1 ∧ ¬ u.1 ∣ c.r * c.p * c.ks.prod ∧ 0 < u.2.1 ∧
      c.r ∣ u.1 ^ u.2.1 + 1 ∧ (∀ d ∈ c.ks, d ∣ u.1 ^ u.2.1 + 1) ∧
      (u.1 : ℤ) ^ (2 * u.2.2) ∣ w.k - w.lam) ∧
    (c.p, c.r) ∈ MaRows.maPairs

instance MaDivResCert.instDecidableValid (w : Row) (c : MaDivResCert) :
    Decidable (c.Valid w) := by
  unfold MaDivResCert.Valid; infer_instance

/-- A row meeting C38's hypotheses whose residue search on `Grp (r :: ks)` finds no vector for any
bound has no SDS, whatever `Fintype` instance its group carries. -/
theorem MaDivResCert.not_hasSDS {w : Row} {c : MaDivResCert} (h : c.Valid w)
    (hpos : ∀ m ∈ c.r :: c.ks, 0 < m) (inst : Fintype (Grp w.ms))
    (hn : ∀ k' ∈ c.bounds, noVectorRes (@Indexed.size (Grp (c.r :: c.ks)) _ (Grp.indexed _ hpos))
      (@Indexed.addIdx (Grp (c.r :: c.ks)) _ (Grp.indexed _ hpos))
      ((w.ms.prod / (c.r * c.p * c.ks.prod) : ℕ) : ℤ) c.Q c.t k' c.s' (c.M : ℤ) = true) :
    ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨p, r, i, e, b, ks, A, P, bounds, Q, t, s', qs⟩ := c
  obtain ⟨hp, hr, hi, hne, hks, hmap, hsurj, hprod, hn', hbe, hb1, hQ, ht, hs, hbounds, hnd, hqs,
    hpair⟩ := h
  dsimp only [MaDivResCert.M] at *
  rintro ⟨D, hD⟩
  obtain ⟨k₀, ks, rfl⟩ := List.exists_cons_of_ne_nil hne
  have : Fact p.Prime := ⟨hp.prime⟩
  have : NeZero (r * p) := ⟨(Nat.mul_pos hr hp.prime.pos).ne'⟩
  have : NeZero r := ⟨hr.ne'⟩
  let _ : Fintype (Grp (k₀ :: ks)) :=
    Grp.fintype _ fun d hd => Nat.pos_of_dvd_of_pos (hks d hd) (by positivity)
  let φ : Grp w.ms →+ ZMod (r * p) × Grp (k₀ :: ks) := linMap w.ms (r * p :: k₀ :: ks) A hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp w.ms) = w.ms.prod / (r * p * (k₀ :: ks).prod) *
      Fintype.card (ZMod (r * p) × Grp (k₀ :: ks)) := by
    rw [Fintype.card_prod, ZMod.card, Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hconj (x : Grp (k₀ :: ks)) : p ^ i • x = -x := by
    have := Grp.nsmul_eq_zero (N := p ^ i + 1) (k₀ :: ks) hks x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  have hcardH : Fintype.card (ZMod r × Grp (k₀ :: ks)) = r * (k₀ :: ks).prod := by
    rw [Fintype.card_prod, ZMod.card, Grp.card_eq]
  have hqs' : ∀ u ∈ qs, u.1.Prime ∧ u.1 ≠ p ∧ ¬ u.1 ∣ Fintype.card (ZMod r × Grp (k₀ :: ks)) ∧
      0 < u.2.1 ∧ (∀ x : ZMod r × Grp (k₀ :: ks), u.1 ^ u.2.1 • x = -x) ∧
      (u.1 : ℤ) ^ (2 * u.2.2) ∣ (w.k : ℤ) - w.lam := by
    intro u hu
    obtain ⟨hq, hqd, hqi, hqr, hqk, hqn⟩ := hqs u hu
    refine ⟨hq.prime, fun he => hqd ?_, fun hd => hqd ?_, hqi, neg_of_dvd_succ hqr hqk, hqn⟩
    · rw [he]
      exact ⟨r * (k₀ :: ks).prod, by ring⟩
    · rw [hcardH] at hd
      exact hd.trans ⟨p, by ring⟩
  let _ : Indexed (ZMod r × Grp (k₀ :: ks)) := Grp.indexed (r :: k₀ :: ks) hpos
  exact hD.false_of_maDividedRes hφ hcard hr hi hconj hn' hbe hb1
    (MaRows.cycloFacts_of_mem_maPairs hpair) hQ ht (by rw [Grp.card_eq]; exact hs) hbounds hnd
    hqs' hn

end SignedDifferenceSets
