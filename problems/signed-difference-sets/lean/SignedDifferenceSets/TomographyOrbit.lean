module

public import SignedDifferenceSets.Tomography
public import SignedDifferenceSets.Multiplier

/-!
# Line tomography with a multiplier (I23, C10)

When `n = k − λ` is a prime with `n ≢ 0, 1 (mod p)`, the coset sums `Y` of a centred SDS along
each line satisfy `Y(n h) = Y(h)` (`fixed_line`): C10 gives a translate fixed by `h ↦ n h`, its
first moment `M` satisfies `n M = M`, so `M = 0`, and `M = −b s` for the translation `b`, so
`b = 0` (`p ∤ s`). `fixSearch` lists such vectors: coordinates in order, each free (values in
`[−c, c]`) or forced to the value at an earlier element of its orbit (`fr`, checked by `frOK`:
`h ≡ nᵉ · fr h`). `not_hasSDS_prime`: tomography with these lists.
-/

@[expose] public section

namespace SignedDifferenceSets.Tomography

/-! ### The search -/

/-- The value forced at coordinate `pre.length`: the one at `fr` of it (`pre` reversed). -/
def forced (fr : List ℕ) (pre : List ℤ) : ℤ := pre.reverse.getD (fr.getD pre.length 0) 0

/-- Coordinate `pre.length` is forced to the value at `fr` of it when that is smaller, else free
in `[−c, c]`; a complete vector passes when it fails the demands or `m1ok`, or is in `W`.
`pre` is reversed; `sum`, `sq`, `abs` are its sums. -/
def fixGo (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (fr : List ℕ) (W : List (List ℤ)) :
    ℕ → List ℤ → ℤ → ℤ → ℤ → Bool
  | 0, pre, sum, sq, abs =>
    !leafOK n add Q t k s pre.reverse sum sq abs || !m1ok n pre.reverse || W.contains pre.reverse
  | rem + 1, pre, sum, sq, abs =>
    cut c Q s (rem + 1) sum sq ||
      if fr.getD pre.length 0 < pre.length then
        fixGo n add c Q t k s fr W rem (forced fr pre :: pre) (sum + forced fr pre)
          (sq + forced fr pre * forced fr pre) (abs + |forced fr pre|)
      else
        allRange (fun x => fixGo n add c Q t k s fr W rem (x :: pre) (sum + x) (sq + x * x)
          (abs + |x|)) (-c) (2 * c + 1).toNat

/-- Every vector meeting the demands, with `m1ok` and agreeing at each `h` with `fr h`, is in
`W`. -/
def fixSearch (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (fr : List ℕ) (W : List (List ℤ)) :
    Bool :=
  fixGo n add c Q t k s fr W n [] 0 0 0

/-- `fr h ≤ h` and `h ≡ tᵉ · fr h (mod p)` with `e = ex h`, for every `h < p`. -/
def frOK (p t : ℕ) (fr ex : List ℕ) : Bool :=
  allTo (fun h => decide (fr.getD h 0 ≤ h) && (t ^ ex.getD h 0 * fr.getD h 0) % p == h) p

theorem getD_append_length {α : Type*} (l : List α) (x : α) (w : List α) (d : α) :
    (l ++ x :: w).getD l.length d = x := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_lt {α : Type*} (l w : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    (l ++ w).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fixGo_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {fr : List ℕ}
    {W : List (List ℤ)} :
    ∀ (w pre : List ℤ) (sum sq abs : ℤ),
      fixGo n add c Q t k s fr W w.length pre sum sq abs = true →
      (∀ y ∈ w, |y| ≤ c) → sum + w.sum = s → sq + sqSum w = Q → abs + absSum w ≤ k →
      (k - (abs + absSum w)) % 2 = 0 → shiftsOK n add t (pre.reverse ++ w) = true →
      m1ok n (pre.reverse ++ w) = true →
      (∀ h < (pre.reverse ++ w).length, fr.getD h 0 < h →
        (pre.reverse ++ w).getD h 0 = (pre.reverse ++ w).getD (fr.getD h 0) 0) →
      pre.reverse ++ w ∈ W
  | [], pre, sum, sq, abs, h, _, hs, hq, ha, hp, hw, hm, _ => by
    simp only [List.sum_nil, add_zero, sqSum, absSum, List.map_nil, List.append_nil] at *
    simpa [fixGo, leafOK, hs, hq, ha, hp, hw, hm] using h
  | x :: w, pre, sum, sq, abs, h, hc, hs, hq, ha, hp, hw, hm, hfr => by
    have hcut := cut_false (x :: w) hc hs hq
    simp only [List.length_cons, fixGo] at h
    rw [List.length_cons] at hcut
    rw [hcut, Bool.false_or] at h
    simp only [List.mem_cons, forall_eq_or_imp] at hc
    simp only [sqSum, absSum, List.map_cons, List.sum_cons] at hs hq ha hp
    have e : (x :: pre).reverse ++ w = pre.reverse ++ x :: w := by simp
    have hlen : pre.reverse.length = pre.length := List.length_reverse
    have key : fixGo n add c Q t k s fr W w.length (x :: pre) (sum + x) (sq + x * x)
        (abs + |x|) = true := by
      split_ifs at h with hf
      · have hlt : pre.length < (pre.reverse ++ x :: w).length := by
          simp only [List.length_append, List.length_reverse, List.length_cons]; omega
        have hx := hfr pre.length hlt hf
        rw [← hlen, getD_append_length, getD_append_lt _ _ (by rw [hlen]; exact hf), hlen] at hx
        rw [hx]
        exact h
      · exact allRange_abs h hc.1
    have := fixGo_sound w (x :: pre) (sum + x) (sq + x * x) (abs + |x|) key hc.2
      (by linarith) (by simp only [sqSum]; linarith) (by simp only [absSum]; linarith)
      (by simp only [absSum]; rw [show abs + |x| + absSum w = abs + (|x| + absSum w) by ring]
          exact hp)
      (by rw [e]; exact hw) (by rw [e]; exact hm) (by rw [e]; exact hfr)
    rwa [e] at this

/-! ### Why the line contractions are fixed -/

variable {p : ℕ} [hp : Fact p.Prime]

theorem natCast_ne_zero_of_prime {n : ℕ} (hn : n.Prime) (hn0 : (n : ZMod p) ≠ 0) :
    Nat.Coprime n p := by
  refine (Nat.coprime_primes hn hp.out).2 fun h => hn0 ?_
  rw [h, ZMod.natCast_self]

/-- C10 at a prime `n = k − λ`: the line contractions of a centred SDS are fixed by `h ↦ n h`. -/
theorem fixed_line {k : ℕ} {lam s : ℤ} {D : ZMod p × ZMod p → SignType} (hD : IsSDS k lam D)
    (hsum : ∑ x, (D x : ℤ) = s) (hsp : (s : ZMod p) ≠ 0) (hcen : Centered D) {n : ℕ}
    (hn : n.Prime) (hk : (k : ℤ) - lam = n) (hn0 : (n : ZMod p) ≠ 0) (hn1 : (n : ZMod p) ≠ 1)
    (j : ℕ) (h : ZMod p) :
    contract (lineMap p j) D ((n : ZMod p) * h) = contract (lineMap p j) D h := by
  set Y := contract (lineMap p j) D with hY
  have hcp := natCast_ne_zero_of_prime hn hn0
  have hc : Fintype.card (ZMod p × ZMod p) = p * Fintype.card (ZMod p) := by
    simp [Fintype.card_prod, ZMod.card]
  obtain ⟨b, hb⟩ := hD.exists_translate_fixed_contract (lineMap p j) (lineMap_surjective p j) hc
    (by rw [hk]; exact Int.squarefree_natCast.2 hn.prime.squarefree)
    (by rw [ZMod.card, hk]; exact Nat.isCoprime_iff_coprime.2 hcp.symm)
  have hfix : ∀ h, Y ((n : ZMod p) * h + b) = Y (h + b) := by
    intro h
    have := hb n (by rw [ZMod.card]; exact hcp) (fun q hq hqn => by
      rw [hk, Int.natCast_dvd_natCast] at hqn
      exact ⟨1, fun x => by rw [(Nat.prime_dvd_prime_iff_eq hq hn).1 hqn, pow_one]⟩) h
    rwa [nsmul_eq_mul] at this
  -- the translate's first moment `M` is fixed by `n`, so vanishes
  set M := ∑ h, ((Y (h + b) : ℤ) : ZMod p) * h with hM
  have hM0 : M = 0 := by
    have e1 : ∑ x, ((Y ((n : ZMod p) * x + b) : ℤ) : ZMod p) * ((n : ZMod p) * x) = M :=
      Fintype.sum_equiv (Equiv.mulLeft₀ (n : ZMod p) hn0) _
        (fun y => ((Y (y + b) : ℤ) : ZMod p) * y) fun _ => rfl
    simp only [hfix] at e1
    have e2 : (n : ZMod p) * M = M := by
      calc (n : ZMod p) * M = ∑ x, ((Y (x + b) : ℤ) : ZMod p) * ((n : ZMod p) * x) := by
            rw [hM, Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ = M := e1
    have : ((n : ZMod p) - 1) * M = 0 := by rw [sub_mul, e2, one_mul, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hn1)
  -- and `M = −b s`
  have hMb : M = -(b * (s : ZMod p)) := by
    have e1 : M = ∑ y, ((Y y : ℤ) : ZMod p) * (y - b) :=
      Fintype.sum_equiv (Equiv.addRight b) _ _ fun x => by simp
    have hs' : ∑ y, ((Y y : ℤ) : ZMod p) = s := by
      rw [← Int.cast_sum, hY, sum_contract, hsum]
    have hm' : ∑ h, ((Y h : ℤ) : ZMod p) * h = 0 := hcen.moment_line j
    rw [e1]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs', hm']
    ring
  have hb0 : b = 0 := by
    rw [hM0, eq_comm, neg_eq_zero] at hMb
    exact (mul_eq_zero.1 hMb).resolve_right hsp
  simpa [hb0] using hfix h

/-! ### The listed vectors -/

theorem fixed_pow {b : ZMod p → ℤ} {u : ZMod p} (hb : ∀ h, b (u * h) = b h) (e : ℕ)
    (h : ZMod p) : b (u ^ e * h) = b h := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, mul_comm (u ^ e) u, mul_assoc, hb, ih]

omit hp in
theorem vecOf_length (b : ZMod p → ℤ) : (vecOf p b).length = p := List.length_ofFn

/-- `fixSearch` lists every vector meeting the demands with `Σ b = s`, `Σ t b(t) = 0` and
`b (n h) = b h`. -/
theorem mem_of_fixSearch {k : ℕ} {lam s : ℤ} {n : ℕ} {fr ex : List ℕ} {W : List (List ℤ)}
    (hV : fixSearch (Indexed.size (ZMod p)) (Indexed.addIdx (ZMod p)) p
      (k + lam * ((p : ℤ) - 1)) (lam * p) k s fr W = true)
    (hfr : frOK p n fr ex = true) {b : ZMod p → ℤ} (hb : Demands p k lam b)
    (hs : ∑ h, b h = s) (hm : ∑ x, ((b x : ℤ) : ZMod p) * x = 0)
    (hn : ∀ h, b ((n : ZMod p) * h) = b h) : vecOf p b ∈ W := by
  have hfix : ∀ h < (vecOf p b).length, fr.getD h 0 < h →
      (vecOf p b).getD h 0 = (vecOf p b).getD (fr.getD h 0) 0 := by
    intro h hh _
    rw [vecOf_length] at hh
    have hc := (allTo_iff _ _).1 hfr h hh
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    rw [vecOf_getD _ hh, vecOf_getD _ (by omega)]
    have e : (h : ZMod p) = (n : ZMod p) ^ ex.getD h 0 * (fr.getD h 0 : ℕ) := by
      have := congrArg (Nat.cast : ℕ → ZMod p) hc.2
      rw [ZMod.natCast_mod] at this
      push_cast at this
      exact this.symm
    rw [e, fixed_pow hn]
  -- the demands, as in `mem_of_inSearch`
  set e : ZMod p ≃ Fin (Indexed.size (ZMod p)) := Indexed.equiv
  set F : Fin (Indexed.size (ZMod p)) → ℤ := fun i => b (e.symm i)
  have hL : vecOf p b = List.ofFn F := rfl
  have hsum (f : ℤ → ℤ) : ((List.ofFn F).map f).sum = ∑ h, f (b h) := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact e.symm.sum_comp (fun h => f (b h))
  have hmem : ∀ y ∈ List.ofFn F, ∃ h, b h = y := by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨_, rfl⟩
  have h1 := fixGo_sound (n := Indexed.size (ZMod p)) (add := Indexed.addIdx (ZMod p))
    (c := p) (Q := k + lam * ((p : ℤ) - 1)) (t := lam * p) (k := k) (s := s) (fr := fr) (W := W)
    (vecOf p b) [] 0 0 0 (by rw [vecOf_length]; exact hV)
    (fun y hy => by obtain ⟨h, rfl⟩ := hmem y (hL ▸ hy); exact hb.bound h)
    (by rw [zero_add, hL, ← hs]; simpa using hsum id)
    (by rw [zero_add, hL, ← hb.sq]; exact hsum fun y => y * y)
    (by rw [zero_add, hL]; simp only [absSum]; rw [hsum fun y => |y|]; exact hb.abs)
    (by rw [zero_add, hL]; simp only [absSum]; rw [hsum fun y => |y|]; exact hb.parity)
    ?_ (by simpa using (show m1ok (Indexed.size (ZMod p)) (vecOf p b) = true from
      m1ok_vecOf b hm)) (by simpa using hfix)
  · simpa using h1
  · rw [List.reverse_nil, List.nil_append, hL, shiftsOK, allTo_iff]
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
    rw [← hb.corr gH hgH0, sumTo_eq, ← sum_equiv (G := ZMod p)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hgH, ← Indexed.equiv_add, getD_ofFn F (e u).isLt, getD_ofFn F (e (u + gH)).isLt]
    simp [F]

/-- Line tomography (I23) with the multiplier `n = k − λ` prime, `n ≢ 0, 1 (mod p)` (C10):
`fixSearch` lists in `W` the centred line contractions (fixed by `h ↦ n h`, orbits by `frOK`), and
`tomoGo` with the certificate `ws` finds no choice from `W`. -/
theorem not_hasSDS_prime (p : ℕ) [Fact p.Prime] {k : ℕ} {lam s : ℤ} (n : ℕ) (hn : n.Prime)
    (hk : (k : ℤ) - lam = n) (hn0 : (n : ZMod p) ≠ 0) (hn1 : (n : ZMod p) ≠ 1)
    (hs : s * s = k + lam * ((p : ℤ) * p - 1)) (hsp : (s : ZMod p) ≠ 0)
    {fr ex : List ℕ} (hfr : frOK p n fr ex = true)
    {W : List (List ℤ)} {ws : List (List (List ℤ))} {R : List (List Row)}
    (hV : fixSearch (Indexed.size (ZMod p)) (Indexed.addIdx (ZMod p)) p
      (k + lam * ((p : ℤ) - 1)) (lam * p) k s fr W = true)
    (hc : certOK p ws = true) (hR : certRows p s ws = R) (h : tomoGo p s W R [] = true) :
    ¬ HasSDS (ZMod p × ZMod p) k lam :=
  not_hasSDS_of_mem p hs hsp (fun _ hD hsum hcen j =>
    mem_of_fixSearch hV hfr (demands_line hD j) (by rw [sum_contract, hsum])
      (hcen.moment_line j) (fixed_line hD hsum hsp hcen hn hk hn0 hn1 j)) hc hR h

end SignedDifferenceSets.Tomography
