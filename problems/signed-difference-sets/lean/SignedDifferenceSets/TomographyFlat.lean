module

public import SignedDifferenceSets.TomographyQuot
public import SignedDifferenceSets.Square

/-!
# Hyperplane tomography on a quotient `G → (ZMod p)^r` (I23)

Let `φ : G →+ Q = Grp ds` (`ds` all `p`) be onto with fibres of `c`, `D` an SDS on `G` with
`Σ D = s` and `Y_f` its coset sums along `hyp f ∘ φ` (`hyp f q = Σ fᵢ qᵢ`). For a list `hs` of
functionals on `Q` vanishing together at `N = |hs|` of them or at `α < N` at every `z ∈ Q`,
`Σ_{h ∈ hs} Y_h(h q₀) = α s + (N − α) Z(q₀)` with `Z(q₀)` the sum of `D` over `φ⁻¹(q₀ + K)`,
`K` where all of `hs` vanish, so `|Z| ≤ c |K|` (`sum_contract_flat`, `card_flat`). The
`(p^r − 1)/(p − 1)` hyperplanes (`α = (p^{r−1} − 1)/(p − 1)`, `K = 0`) and each flat of them
are such lists; `incOK` checks the counts on coordinate lists (`allPts`).

A check point is a flat and a point `q`; its value is `Σ_{f ∈ flat} Y_f(f q)`. `flatGo` chooses
one listed vector per hyperplane (depth by depth) and drops a node when some check point's value,
its sum so far plus the remaining hyperplanes' range (`lo`, `hi`, checked by `boundsOK`), can no
longer be `α s` plus a multiple of `N − α` within `(N − α) c κ`; at a leaf the box values of the
first `m` check points (pairwise distinct classes of one flat) must have absolute sum `≤ k`.
`not_hasSDS_flat`: when `p ∤ s` every centred hyperplane contraction lies in `W`, and a passing
search with a sound certificate (`certOK`) rules the SDS out.
-/

@[expose] public section

namespace SignedDifferenceSets.TomographyFlat

open Tomography

/-! ### Points and hyperplanes of `Grp ds` -/

/-- Coordinate lists `xs` with `xs[i] < ds[i]`, by the recursion of `Grp`. -/
def allPts : List ℕ → List (List ℕ)
  | [] => [[]]
  | [m] => (List.range m).map fun a => [a]
  | m :: m' :: ms => (List.range m).flatMap fun a => (allPts (m' :: ms)).map (a :: ·)

/-- Every element of `Grp ds` has coordinates in `allPts ds`. -/
theorem exists_mem_allPts : (ds : List ℕ) → (∀ d ∈ ds, 0 < d) → ∀ q : Grp ds,
    ∃ xs ∈ allPts ds, Grp.ofList ds xs = q
  | [], _, q => ⟨[], by simp [allPts], Subsingleton.elim (α := ZMod 1) _ _⟩
  | [m], h, q => by
    have : NeZero m := ⟨(h m List.mem_cons_self).ne'⟩
    refine ⟨[(q : ZMod m).val], ?_, ZMod.natCast_zmod_val (q : ZMod m)⟩
    simp only [allPts, List.mem_map, List.mem_range, List.cons.injEq, and_true]
    exact ⟨_, ZMod.val_lt _, rfl⟩
  | m :: m' :: ms, h, q => by
    have : NeZero m := ⟨(h m List.mem_cons_self).ne'⟩
    obtain ⟨xs, hxs, he⟩ := exists_mem_allPts (m' :: ms)
      (fun d hd => h d (List.mem_cons_of_mem _ hd)) q.2
    refine ⟨(q.1 : ZMod m).val :: xs, ?_, Prod.ext (ZMod.natCast_zmod_val (q.1 : ZMod m)) he⟩
    simp only [allPts, List.mem_flatMap, List.mem_range, List.mem_map, List.cons.injEq]
    exact ⟨_, ZMod.val_lt _, xs, hxs, rfl, rfl⟩

theorem formOk_of_eq (p : ℕ) : (f ds : List ℕ) → (∀ d ∈ ds, d = p) → FormOk p f ds
  | _, [], _ => trivial
  | f, [d], h => by
    rw [h d List.mem_cons_self]
    exact dvd_mul_left _ _
  | f, d :: d' :: ds, h =>
    ⟨by
      rw [h d List.mem_cons_self]
      exact dvd_mul_left _ _,
    formOk_of_eq p f.tail (d' :: ds) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

/-- The hyperplane map `q ↦ Σ fᵢ qᵢ` on `Grp ds`, every factor `p`. -/
def hyp (p : ℕ) (ds : List ℕ) (hds : ∀ d ∈ ds, d = p) (f : List ℕ) : Grp ds →+ ZMod p :=
  form p f ds (formOk_of_eq p f ds hds)

theorem hyp_ofList (p : ℕ) (ds : List ℕ) (hds : ∀ d ∈ ds, d = p) (f xs : List ℕ) :
    hyp p ds hds f (Grp.ofList ds xs) = ((dotL ds f xs % p : ℕ) : ZMod p) := by
  rw [hyp, form_ofList, ZMod.natCast_mod]

theorem nsmul_eq_zero_of_eq {p : ℕ} : {ds : List ℕ} → (∀ d ∈ ds, d = p) → ∀ q : Grp ds,
    p • q = 0
  | [], _, q => Subsingleton.elim (α := ZMod 1) _ _
  | [d], h, q => by
    change p • (q : ZMod d) = 0
    rw [nsmul_eq_mul, ← h d List.mem_cons_self, ZMod.natCast_self, zero_mul]
  | d :: d' :: ds, h, q => by
    refine Prod.ext ?_ (nsmul_eq_zero_of_eq (fun x hx => h x (List.mem_cons_of_mem _ hx)) q.2)
    change p • (q.1 : ZMod d) = 0
    rw [nsmul_eq_mul, ← h d List.mem_cons_self, ZMod.natCast_self, zero_mul]

theorem sum_zsmul_const {ι M : Type*} [AddCommGroup M] (s : Finset ι) (f : ι → ℤ) (a : M) :
    (∑ i ∈ s, f i) • a = ∑ i ∈ s, f i • a := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, add_zsmul, ih]

/-! ### The incidence identity -/

section Incidence

variable {G Q : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup Q] {p : ℕ}

/-- Summed over `hs`, the coset sums along `h ∘ φ` at `h q₀` count each `x` once per `h ∈ hs`
vanishing at `φ x − q₀`. -/
theorem sum_contract_list (φ : G →+ Q) (D : G → SignType) (q₀ : Q) :
    ∀ hs : List (Q →+ ZMod p), (hs.map fun h => contract (h.comp φ) D (h q₀)).sum =
      ∑ x, (D x : ℤ) * ((hs.countP fun h => h (φ x - q₀) = 0 : ℕ) : ℤ)
  | [] => by simp
  | h :: hs => by
    rw [List.map_cons, List.sum_cons, sum_contract_list φ D q₀ hs]
    have e : contract (h.comp φ) D (h q₀) =
        ∑ x, if h (φ x - q₀) = 0 then (D x : ℤ) else 0 := by
      rw [contract, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, map_sub, sub_eq_zero]
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [List.countP_cons]
    by_cases h1 : h (φ x - q₀) = 0
    · simp only [h1, ↓reduceIte, decide_true]
      push_cast
      ring
    · simp only [h1, ↓reduceIte, decide_false, Bool.false_eq_true]
      push_cast
      ring

/-- The incidence identity: when at every `z` either all of `hs` or exactly `α < |hs|` vanish,
`Σ_{h ∈ hs} Y_h(h q₀) = α Σ D + (|hs| − α) Z(q₀)`. -/
theorem sum_contract_flat (φ : G →+ Q) (D : G → SignType) {hs : List (Q →+ ZMod p)} {α : ℕ}
    (hα : α ≤ hs.length) (hinc : ∀ z : Q, hs.countP (fun h => h z = 0) = hs.length ∨
      hs.countP (fun h => h z = 0) = α) (q₀ : Q) :
    (hs.map fun h => contract (h.comp φ) D (h q₀)).sum =
      α * ∑ x, (D x : ℤ) + ((hs.length - α : ℕ) : ℤ) *
        ∑ x ∈ Finset.univ.filter (fun x => ∀ h ∈ hs, h (φ x - q₀) = 0), (D x : ℤ) := by
  rw [sum_contract_list, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hall : ∀ h ∈ hs, h (φ x - q₀) = 0
  · have hc : hs.countP (fun h => h (φ x - q₀) = 0) = hs.length :=
      List.countP_eq_length.2 (by simpa using hall)
    rw [hc, ite_eq_left hall]
    push_cast [hα]
    ring
  · rcases hinc (φ x - q₀) with h1 | h1
    · exact absurd (by simpa using List.countP_eq_length.1 h1) hall
    · rw [h1, ite_eq_right hall]
      ring

end Incidence

/-! ### The box: how many `x` a check point sums -/

section Box

variable {G Q : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup Q] [Fintype Q] {p : ℕ}

/-- The `x` with `φ x − q₀` in the common kernel of `hs` are `c` times as many as the kernel. -/
theorem card_flat {φ : G →+ Q} (hφ : Function.Surjective φ) {c : ℕ}
    (hc : Fintype.card G = c * Fintype.card Q) (hs : List (Q →+ ZMod p)) (q₀ : Q) :
    (Finset.univ.filter fun x => ∀ h ∈ hs, h (φ x - q₀) = 0).card =
      c * (Finset.univ.filter fun z : Q => ∀ h ∈ hs, h z = 0).card := by
  classical
  set T := Finset.univ.filter fun z : Q => ∀ h ∈ hs, h (z - q₀) = 0 with hT
  rw [Finset.card_eq_sum_card_fiberwise (f := φ) (t := T) (fun x hx => by simpa [T] using hx)]
  have hfib : ∀ z ∈ T, ((Finset.univ.filter fun x => ∀ h ∈ hs, h (φ x - q₀) = 0).filter
      fun x => φ x = z).card = c := by
    intro z hz
    rw [← card_fibre_eq hφ hc z]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, fibre, T] at hz ⊢
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hz, h⟩
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  refine Finset.card_bij (fun z _ => z - q₀) (fun z hz => by simpa [T] using hz)
    (fun a _ b _ h => sub_left_injective h) (fun z hz => ⟨z + q₀, by simpa [T] using hz, by simp⟩)

end Box

section Points

variable {p : ℕ} [NeZero p] {ds : List ℕ}

theorem natCast_mod_eq_zero_iff (n : ℕ) : ((n % p : ℕ) : ZMod p) = 0 ↔ n % p = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    exact Nat.eq_zero_of_dvd_of_lt h (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p)))
  · intro h
    rw [h]
    exact dvd_zero _

theorem countP_hyp (hds : ∀ d ∈ ds, d = p) (fs : List (List ℕ)) (xs : List ℕ) :
    (fs.map (hyp p ds hds)).countP (fun h => h (Grp.ofList ds xs) = 0) =
      fs.countP (fun f => dotL ds f xs % p == 0) := by
  rw [List.countP_map]
  congr 1
  funext f
  simp only [Function.comp_apply, hyp_ofList]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, natCast_mod_eq_zero_iff]

/-- The common kernel of `fs` has at most as many elements as `allPts` has zeros of `fs`. -/
theorem card_ker_le (hds : ∀ d ∈ ds, d = p) [Fintype (Grp ds)] (fs : List (List ℕ)) :
    (Finset.univ.filter fun z : Grp ds => ∀ h ∈ fs.map (hyp p ds hds), h z = 0).card ≤
      (allPts ds).countP fun xs => fs.countP (fun f => dotL ds f xs % p == 0) == fs.length := by
  classical
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => by
    rw [hds d hd]
    exact Nat.pos_of_ne_zero (NeZero.ne p)
  set L := (allPts ds).filter fun xs =>
    fs.countP (fun f => dotL ds f xs % p == 0) == fs.length
  calc _ ≤ (L.map (Grp.ofList ds)).toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨xs, hxs, rfl⟩ := exists_mem_allPts ds hpos z
        rw [List.mem_toFinset, List.mem_map]
        refine ⟨xs, List.mem_filter.2 ⟨hxs, ?_⟩, rfl⟩
        rw [beq_iff_eq, ← countP_hyp hds, ← List.length_map (f := hyp p ds hds)]
        exact List.countP_eq_length.2 (by simpa using hz)
    _ ≤ (L.map (Grp.ofList ds)).length := List.toFinset_card_le _
    _ = _ := by rw [List.length_map, List.countP_eq_length_filter]

/-- The hyperplanes `fs` vanish together or `α` of them at every element when they do so at
every coordinate list. -/
theorem countP_hyp_eq (hds : ∀ d ∈ ds, d = p) {fs : List (List ℕ)} {α : ℕ}
    (h : (allPts ds).all fun xs => fs.countP (fun f => dotL ds f xs % p == 0) == fs.length ||
      fs.countP (fun f => dotL ds f xs % p == 0) == α) (z : Grp ds) :
    (fs.map (hyp p ds hds)).countP (fun h => h z = 0) = (fs.map (hyp p ds hds)).length ∨
      (fs.map (hyp p ds hds)).countP (fun h => h z = 0) = α := by
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => by
    rw [hds d hd]
    exact Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨xs, hxs, rfl⟩ := exists_mem_allPts ds hpos z
  have := List.all_eq_true.1 h xs hxs
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rw [countP_hyp hds, List.length_map]
  exact this

end Points

/-! ### Centring and the demands on the hyperplane contractions -/

section Centre

variable {G : Type*} [AddCommGroup G] [Fintype G] {p : ℕ} [hp : Fact p.Prime] {ds : List ℕ}

/-- A translate of `D` has `Σₓ D(x) • φ(x) = 0` when `p ∤ Σ D`. -/
theorem exists_centered_flat (hds : ∀ d ∈ ds, d = p) {φ : G →+ Grp ds}
    (hφ : Function.Surjective φ) (D : G → SignType)
    (hS : (((∑ x, (D x : ℤ) : ℤ)) : ZMod p) ≠ 0) :
    ∃ t, ∑ x, (D (x + t) : ℤ) • φ x = 0 := by
  set S := ∑ x, (D x : ℤ) with hSdef
  set m := ∑ x, (D x : ℤ) • φ x with hm
  set u : ℕ := ((S : ZMod p)⁻¹).val
  obtain ⟨t, ht⟩ := hφ (u • m)
  refine ⟨t, ?_⟩
  have e1 : ∑ x, (D (x + t) : ℤ) • φ x = ∑ y, (D y : ℤ) • φ (y - t) :=
    Fintype.sum_equiv (Equiv.addRight t) _ _ fun x => by simp
  have hdvd : (p : ℤ) ∣ 1 - S * u := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_inv_cancel₀ hS, sub_self]
  obtain ⟨j, hj⟩ := hdvd
  have e2 : ∑ y, (D y : ℤ) • φ (y - t) = m - S • φ t := by
    simp only [map_sub, zsmul_sub, Finset.sum_sub_distrib, hm, hSdef, sum_zsmul_const]
  rw [e1, e2, ht]
  have e3 : m - S • u • m = (1 - S * u) • m := by
    rw [sub_zsmul, one_zsmul, mul_zsmul, natCast_zsmul, sub_eq_add_neg]
  rw [e3, hj, mul_comm, mul_zsmul, natCast_zsmul, nsmul_eq_zero_of_eq hds, zsmul_zero]

/-- The coset sums of a centred `D` along `h ∘ φ` have first moment `0`. -/
theorem moment_hyp {φ : G →+ Grp ds} {D : G → SignType} (hcen : ∑ x, (D x : ℤ) • φ x = 0)
    (h : Grp ds →+ ZMod p) :
    ∑ u, ((contract (h.comp φ) D u : ℤ) : ZMod p) * u = 0 := by
  rw [moment_contractQ]
  have e : ∑ x, ((D x : ℤ) : ZMod p) * (h.comp φ) x = h (∑ x, (D x : ℤ) • φ x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_zsmul, zsmul_eq_mul, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [e, hcen, map_zero]

/-- A hyperplane map with a coordinate list of value `1` is onto. -/
theorem hyp_surjective (hds : ∀ d ∈ ds, d = p) {f : List ℕ}
    (h : (allPts ds).any fun xs => dotL ds f xs % p == 1) :
    Function.Surjective (hyp p ds hds f) := by
  obtain ⟨xs, -, hxs⟩ := List.any_eq_true.1 h
  rw [beq_iff_eq] at hxs
  intro u
  refine ⟨u.val • Grp.ofList ds xs, ?_⟩
  rw [map_nsmul, hyp_ofList, hxs, Nat.cast_one, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

/-- The demands on the coset sums along an onto `ψ : G →+ ZMod p` (C3, fibres of `C`). -/
theorem demands_hyp {ψ : G →+ ZMod p} (hψ : Function.Surjective ψ) {C k : ℕ} {lam : ℤ}
    (hcard : Fintype.card G = C * p) {D : G → SignType} (hD : IsSDS k lam D) :
    Demands C k lam (contract ψ D) := by
  have hc : Fintype.card G = C * Fintype.card (ZMod p) := by rw [hcard, ZMod.card]
  have hfib := card_fibre_eq hψ hc
  have hC : 1 ≤ C := by
    rcases Nat.eq_zero_or_pos C with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card G)
      rw [hc, h0, zero_mul] at this
      omega
    · exact h0
  exact
    { bound := fun h => by
        have := abs_contract_le ψ D h
        rwa [hfib] at this
      sq := by rw [hD.contract_sq, hfib 0, Nat.cast_sub hC, Nat.cast_one]
      corr := fun g hg => by rw [hD.contract_autocorr _ g hg, hfib]
      abs := hD.sum_abs_contract_le _
      parity := hD.sum_abs_contract_parity _ }

end Centre

/-! ### The search on numbers -/

/-- A check point at a node: its final value, between `t + l` and `t + h`, minus the target
`ctr`, clamped to `[−w, w]`, can still be a multiple of `g` (`cs = (ctr, g, w)`). -/
def okOne (t l h : ℤ) (cs : ℤ × ℤ × ℤ) : Bool :=
  decide (max (t + l - cs.1) (-cs.2.2) ≤ cs.2.1 * (min (t + h - cs.1) cs.2.2 / cs.2.1))

/-- `okOne` at every check point. -/
def okAll : List ℤ → List ℤ → List ℤ → List (ℤ × ℤ × ℤ) → Bool
  | t :: P, l :: L, h :: H, c :: cs => okOne t l h c && okAll P L H cs
  | _, _, _, _ => true

/-- `P` plus `y` read at the indices `ix`. -/
def addVec : List ℤ → List ℕ → List ℤ → List ℤ
  | t :: P, i :: ix, y => (t + y.getD i 0) :: addVec P ix y
  | _, _, _ => []

/-- `Σ |(t − ctr) / g|` over the first `m` check points. -/
def absSumOf : ℕ → List ℤ → List (ℤ × ℤ × ℤ) → ℤ
  | m + 1, t :: P, c :: cs => |(t - c.1) / c.2.1| + absSumOf m P cs
  | _, _, _ => 0

/-- A depth: each check point's index into the chosen vector (`p`: not in its flat), then the
bounds `lo`, `hi` of the sums of the depths after it. -/
abbrev Level := List ℕ × List ℤ × List ℤ

/-- The options at a depth: `U` for the first `u` depths, then `W`. -/
def optsAt (U W : List (List ℤ)) (u : ℕ) : List (List ℤ) := if u = 0 then W else U

/-- No choice of one option per depth passes every node check and, at the leaf, has absolute
sum at most `k` over the first `m` check points. -/
def flatGo (k m : ℕ) (cs : List (ℤ × ℤ × ℤ)) (U W : List (List ℤ)) :
    ℕ → List Level → List ℤ → Bool
  | _, [], P => !decide (absSumOf m P cs ≤ k)
  | u, (ix, L, H) :: rest, P => (optsAt U W u).all fun y =>
    !okAll (addVec P ix y) L H cs || flatGo k m cs U W (u - 1) rest (addVec P ix y)

/-- The kill: the root fails, or `flatGo` from the root. -/
def flatKill (k m : ℕ) (cs : List (ℤ × ℤ × ℤ)) (U W : List (List ℤ)) (u : ℕ) (L H : List ℤ)
    (lv : List Level) : Bool :=
  !okAll (List.replicate cs.length 0) L H cs ||
    flatGo k m cs U W u lv (List.replicate cs.length 0)

/-- A path of choices that passes every node and the leaf. -/
def Good (k m : ℕ) (cs : List (ℤ × ℤ × ℤ)) (U W : List (List ℤ)) :
    ℕ → List Level → List (List ℤ) → List ℤ → Prop
  | _, [], _, P => absSumOf m P cs ≤ k
  | u, (ix, L, H) :: rest, y :: ys, P => y ∈ optsAt U W u ∧
      okAll (addVec P ix y) L H cs = true ∧ Good k m cs U W (u - 1) rest ys (addVec P ix y)
  | _, _ :: _, [], _ => False

theorem flatGo_eq_false {k m : ℕ} {cs : List (ℤ × ℤ × ℤ)} {U W : List (List ℤ)} :
    ∀ (u : ℕ) (lv : List Level) (ys : List (List ℤ)) (P : List ℤ),
      Good k m cs U W u lv ys P → flatGo k m cs U W u lv P = false
  | _, [], _, P, h => by simpa [flatGo, Good] using h
  | u, (ix, L, H) :: rest, y :: ys, P, ⟨hy, hok, hg⟩ => by
    rw [flatGo, List.all_eq_false]
    refine ⟨y, hy, ?_⟩
    rw [hok, flatGo_eq_false (u - 1) rest ys _ hg]
    simp
  | _, _ :: _, [], _, h => h.elim

/-- `L ≤ L' + y[ix]` and `H' + y[ix] ≤ H` at every check point. -/
def stepOK : List ℤ → List ℤ → List ℤ → List ℤ → List ℕ → List ℤ → Bool
  | l :: L, h :: H, l' :: L', h' :: H', i :: ix, y =>
    decide (l ≤ l' + y.getD i 0) && decide (h' + y.getD i 0 ≤ h) && stepOK L H L' H' ix y
  | _, _, _, _, _, _ => true

/-- The bounds `L`, `H` before each depth hold for every choice of options after it. -/
def boundsOK (U W : List (List ℤ)) : ℕ → List Level → List ℤ → List ℤ → Bool
  | _, [], L, H => L.all (· ≤ 0) && H.all (0 ≤ ·)
  | u, (ix, L', H') :: rest, L, H =>
    (optsAt U W u).all (fun y => stepOK L H L' H' ix y) && boundsOK U W (u - 1) rest L' H'

/-- The sum at check point `j` of the chosen vectors read at the depths' indices. -/
def colSum (j : ℕ) : List Level → List (List ℤ) → ℤ
  | l :: lv, y :: ys => y.getD (l.1.getD j 0) 0 + colSum j lv ys
  | _, _ => 0

theorem stepOK_spec : ∀ (L H L' H' : List ℤ) (ix : List ℕ) (y : List ℤ) (j : ℕ),
    stepOK L H L' H' ix y = true → j < L.length → j < H.length → j < L'.length →
      j < H'.length → j < ix.length →
      L.getD j 0 ≤ L'.getD j 0 + y.getD (ix.getD j 0) 0 ∧
        H'.getD j 0 + y.getD (ix.getD j 0) 0 ≤ H.getD j 0
  | l :: L, h :: H, l' :: L', h' :: H', i :: ix, y, j, hs, h1, h2, h3, h4, h5 => by
    simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hs
    cases j with
    | zero => simpa using ⟨hs.1.1, hs.1.2⟩
    | succ j =>
      simpa using stepOK_spec L H L' H' ix y j hs.2 (by simpa using h1) (by simpa using h2)
        (by simpa using h3) (by simpa using h4) (by simpa using h5)
  | [], _, _, _, _, _, _, _, h1, _, _, _, _ => by simp at h1
  | _ :: _, [], _, _, _, _, _, _, _, h2, _, _, _ => by simp at h2
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, h3, _, _ => by simp at h3
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, _, _, h4, _ => by simp at h4
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, _, _, h5 => by simp at h5

/-- Every depth's lists have `J` entries. -/
def lenOK (J : ℕ) (lv : List Level) : Bool :=
  lv.all fun l => l.1.length == J && l.2.1.length == J && l.2.2.length == J

/-- Sound bounds: `L ≤ colSum ≤ H` for every choice of options. -/
theorem bounds_spec {U W : List (List ℤ)} {J : ℕ} :
    ∀ (u : ℕ) (lv : List Level) (L H : List ℤ) (ys : List (List ℤ)),
      boundsOK U W u lv L H = true → lenOK J lv = true → L.length = J → H.length = J →
      ys.length = lv.length → (∀ i < lv.length, ys.getD i [] ∈ optsAt U W (u - i)) →
      ∀ j < J, L.getD j 0 ≤ colSum j lv ys ∧ colSum j lv ys ≤ H.getD j 0
  | _, [], L, H, ys, hb, _, _, _, _, _, j, _ => by
    simp only [boundsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hb
    have h1 : L.getD j 0 ≤ 0 := by
      rcases lt_or_ge j L.length with hj | hj
      · rw [List.getD_eq_getElem _ _ hj]
        exact hb.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_default _ _ hj]
    have h2 : 0 ≤ H.getD j 0 := by
      rcases lt_or_ge j H.length with hj | hj
      · rw [List.getD_eq_getElem _ _ hj]
        exact hb.2 _ (List.getElem_mem _)
      · rw [List.getD_eq_default _ _ hj]
    cases ys <;> exact ⟨h1, h2⟩
  | _, _ :: _, _, _, [], _, _, _, _, hys, _, _, _ => by simp at hys
  | u, (ix, L', H') :: rest, L, H, y :: ys, hb, hlen, hL, hH, hys, hopt, j, hj => by
    simp only [boundsOK, Bool.and_eq_true, List.all_eq_true] at hb
    simp only [lenOK, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hlen
    have hy : y ∈ optsAt U W u := by simpa using hopt 0 (by simp)
    have ih := bounds_spec (u - 1) rest L' H' ys hb.2 hlen.2 hlen.1.1.2 hlen.1.2
      (by simpa using hys) (fun i hi => by
        have := hopt (i + 1) (by simpa using hi)
        rw [show u - 1 - i = u - (i + 1) by omega]
        simpa using this) j hj
    have hs := stepOK_spec L H L' H' ix y j (hb.1 y hy) (by omega) (by omega)
      (by rw [hlen.1.1.2]; exact hj) (by rw [hlen.1.2]; exact hj)
      (by rw [hlen.1.1.1]; exact hj)
    simp only [colSum]
    constructor <;> linarith [hs.1, hs.2, ih.1, ih.2]


theorem okOne_of {t l h v : ℤ} {c : ℤ × ℤ × ℤ} (hg : 0 < c.2.1) (hl : t + l ≤ v) (hh : v ≤ t + h)
    (hd : c.2.1 ∣ v - c.1) (hw : |v - c.1| ≤ c.2.2) : okOne t l h c = true := by
  obtain ⟨ctr, g, w⟩ := c
  simp only at hg hd hw
  obtain ⟨z, hz⟩ := hd
  unfold okOne
  rw [decide_eq_true_eq]
  have h1 : max (t + l - ctr) (-w) ≤ g * z := by
    rw [← hz]
    exact max_le (by linarith) (by linarith [neg_abs_le (v - ctr)])
  have h2 : g * z ≤ min (t + h - ctr) w := by
    rw [← hz]
    exact le_min (by linarith) (le_trans (le_abs_self _) hw)
  have h3 : z ≤ min (t + h - ctr) w / g := Int.le_ediv_of_mul_le hg (by linarith [mul_comm g z])
  exact h1.trans (mul_le_mul_of_nonneg_left h3 hg.le)

theorem okAll_of : ∀ (P L H : List ℤ) (cs : List (ℤ × ℤ × ℤ)),
    (∀ j < cs.length, okOne (P.getD j 0) (L.getD j 0) (H.getD j 0) (cs.getD j (0, 0, 0)) = true) →
      okAll P L H cs = true
  | t :: P, l :: L, h :: H, c :: cs, hj => by
    simp only [okAll, Bool.and_eq_true]
    refine ⟨by simpa using hj 0 (by simp), okAll_of P L H cs fun j hjl => ?_⟩
    simpa using hj (j + 1) (by simpa using hjl)
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _ => rfl

theorem length_addVec : ∀ (P : List ℤ) (ix : List ℕ) (y : List ℤ),
    (addVec P ix y).length = min P.length ix.length
  | [], _, _ => by simp [addVec]
  | _ :: _, [], _ => by simp [addVec]
  | _ :: P, _ :: ix, y => by simp [addVec, length_addVec P ix y, Nat.succ_min_succ]

theorem getD_addVec : ∀ (P : List ℤ) (ix : List ℕ) (y : List ℤ) (j : ℕ), j < P.length →
    j < ix.length → (addVec P ix y).getD j 0 = P.getD j 0 + y.getD (ix.getD j 0) 0
  | _ :: P, i :: ix, y, 0, _, _ => by simp [addVec]
  | _ :: P, i :: ix, y, j + 1, h1, h2 => by
    simpa [addVec] using getD_addVec P ix y j (by simpa using h1) (by simpa using h2)
  | [], _, _, _, h1, _ => by simp at h1
  | _ :: _, [], _, _, _, h2 => by simp at h2

theorem absSumOf_eq : ∀ (m : ℕ) (P : List ℤ) (cs : List (ℤ × ℤ × ℤ)), m ≤ P.length →
    m ≤ cs.length → absSumOf m P cs =
      ∑ j ∈ Finset.range m, |(P.getD j 0 - (cs.getD j (0, 0, 0)).1) / (cs.getD j (0, 0, 0)).2.1|
  | 0, _, _, _, _ => by simp [absSumOf]
  | m + 1, t :: P, c :: cs, h1, h2 => by
    rw [absSumOf, absSumOf_eq m P cs (by simpa using h1) (by simpa using h2),
      Finset.sum_range_succ']
    simp [add_comm]
  | _ + 1, [], _, h1, _ => by simp at h1
  | _ + 1, _ :: _, [], _, h2 => by simp at h2

theorem colSum_eq : ∀ (j : ℕ) (lv : List Level) (ys : List (List ℤ)), ys.length = lv.length →
    colSum j lv ys =
      ∑ d ∈ Finset.range lv.length, (ys.getD d []).getD ((lv.getD d ([], [], [])).1.getD j 0) 0
  | _, [], _, _ => by simp [colSum]
  | _, _ :: _, [], h => by simp at h
  | j, l :: lv, y :: ys, h => by
    rw [colSum, colSum_eq j lv ys (by simpa using h), List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- The true path: every node and the leaf pass when each check point's final value `V j` is
`ctr` plus a multiple of `g > 0` within `w`, the bounds are sound and the leaf's absolute sum is
at most `k`. -/
theorem good_of {k m J : ℕ} {cs : List (ℤ × ℤ × ℤ)} {U W : List (List ℤ)} (V : List ℤ)
    (hVl : V.length = J) (hcs : cs.length = J)
    (hV : ∀ j < J, 0 < (cs.getD j (0, 0, 0)).2.1 ∧
      (cs.getD j (0, 0, 0)).2.1 ∣ V.getD j 0 - (cs.getD j (0, 0, 0)).1 ∧
      |V.getD j 0 - (cs.getD j (0, 0, 0)).1| ≤ (cs.getD j (0, 0, 0)).2.2)
    (habs : absSumOf m V cs ≤ k) :
    ∀ (u : ℕ) (lv : List Level) (ys : List (List ℤ)) (P L H : List ℤ),
      boundsOK U W u lv L H = true → lenOK J lv = true → L.length = J → H.length = J →
      P.length = J → ys.length = lv.length →
      (∀ i < lv.length, ys.getD i [] ∈ optsAt U W (u - i)) →
      (∀ j < J, P.getD j 0 + colSum j lv ys = V.getD j 0) →
      okAll P L H cs = true ∧ Good k m cs U W u lv ys P := by
  intro u lv
  induction lv generalizing u with
  | nil =>
    intro ys P L H hb hlen hL hH hP hys hopt hsum
    have hbd := bounds_spec u [] L H ys hb hlen hL hH hys hopt
    refine ⟨okAll_of P L H cs fun j hj => ?_, ?_⟩
    · rw [hcs] at hj
      have h1 := hbd j hj
      have h2 := hsum j hj
      cases ys <;> simp only [colSum] at h1 h2 <;>
        exact okOne_of (hV j hj).1 (by linarith [h1.1]) (by linarith [h1.2]) (hV j hj).2.1
          (hV j hj).2.2
    · have hPV : P = V := by
        refine List.ext_getElem (by rw [hP, hVl]) fun j h1 h2 => ?_
        have := hsum j (by omega)
        cases ys <;> simp only [colSum, add_zero] at this <;>
          rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
      cases ys <;> simpa [Good, hPV] using habs
  | cons l lv ih =>
    obtain ⟨ix, L', H'⟩ := l
    intro ys P L H hb hlen hL hH hP hys hopt hsum
    cases ys with
    | nil => simp at hys
    | cons y ys =>
      have hbd := bounds_spec u ((ix, L', H') :: lv) L H (y :: ys) hb hlen hL hH hys hopt
      have hb' := hb
      simp only [boundsOK, Bool.and_eq_true, List.all_eq_true] at hb'
      have hlen' := hlen
      simp only [lenOK, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hlen'
      have hy : y ∈ optsAt U W u := by simpa using hopt 0 (by simp)
      have hP' : (addVec P ix y).length = J := by
        rw [length_addVec, hP, hlen'.1.1.1, min_self]
      have := ih (u - 1) ys (addVec P ix y) L' H' hb'.2 hlen'.2 hlen'.1.1.2 hlen'.1.2 hP'
        (by simpa using hys) (fun i hi => by
          have := hopt (i + 1) (by simpa using hi)
          rw [show u - 1 - i = u - (i + 1) by omega]
          simpa using this) (fun j hj => by
          rw [getD_addVec _ _ _ _ (by omega) (by rw [hlen'.1.1.1]; exact hj), ← hsum j hj,
            colSum]
          ring)
      refine ⟨okAll_of P L H cs fun j hj => ?_, hy, this⟩
      rw [hcs] at hj
      have h1 := hbd j hj
      have h2 := hsum j hj
      exact okOne_of (hV j hj).1 (by linarith [h1.1]) (by linarith [h1.2]) (hV j hj).2.1
        (hV j hj).2.2

/-- A passing kill leaves no path whose final values are `ctr` plus multiples within the box and
whose leaf passes. -/
theorem flatKill_false {k m J : ℕ} {cs : List (ℤ × ℤ × ℤ)} {U W : List (List ℤ)} {u : ℕ}
    {L H : List ℤ} {lv : List Level} (h : flatKill k m cs U W u L H lv = true)
    (hb : boundsOK U W u lv L H = true) (hlen : lenOK J lv = true) (hL : L.length = J)
    (hH : H.length = J) (hcs : cs.length = J) (ys : List (List ℤ)) (hys : ys.length = lv.length)
    (hopt : ∀ i < lv.length, ys.getD i [] ∈ optsAt U W (u - i))
    (hV : ∀ j < J, 0 < (cs.getD j (0, 0, 0)).2.1 ∧
      (cs.getD j (0, 0, 0)).2.1 ∣ colSum j lv ys - (cs.getD j (0, 0, 0)).1 ∧
      |colSum j lv ys - (cs.getD j (0, 0, 0)).1| ≤ (cs.getD j (0, 0, 0)).2.2)
    (habs : absSumOf m ((List.range J).map fun j => colSum j lv ys) cs ≤ k) : False := by
  set V := (List.range J).map fun j => colSum j lv ys with hVdef
  have hVj : ∀ j < J, V.getD j 0 = colSum j lv ys := fun j hj => by
    rw [hVdef, List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  have hP : (List.replicate cs.length (0 : ℤ)).length = J := by simp [hcs]
  have hg := good_of V (by simp [hVdef]) hcs (fun j hj => by rw [hVj j hj]; exact hV j hj) habs u
    lv ys _ L H hb hlen hL hH hP hys hopt (fun j hj => by
      have h0 : (List.replicate cs.length (0 : ℤ)).getD j 0 = 0 := by simp
      rw [h0, zero_add, hVj j hj])
  rw [flatKill, hg.1, flatGo_eq_false u lv ys _ hg.2] at h
  simp at h

/-! ### The certificate -/

/-- A flat: membership per depth, `α`, and a bound `κ` on its kernel's size. -/
abbrev Flat := List Bool × ℕ × ℕ

/-- The hyperplanes of `fs` at the depths `mem` marks. -/
def members : List (List ℕ) → List Bool → List (List ℕ)
  | f :: fs, b :: bs => if b then f :: members fs bs else members fs bs
  | _, _ => []

/-- How many of `fs` vanish at `xs`. -/
def zeroCount (p : ℕ) (ds : List ℕ) (fs : List (List ℕ)) (xs : List ℕ) : ℕ :=
  fs.countP fun f => dotL ds f xs % p == 0

/-- At every coordinate list all members of the flat vanish or exactly `α` of them (`α < N`),
and at most `κ` coordinate lists are zeros of all. -/
def incOK (p : ℕ) (ds : List ℕ) (fs : List (List ℕ)) (F : Flat) : Bool :=
  decide (F.2.1 < (members fs F.1).length) &&
    (allPts ds).all (fun xs => zeroCount p ds (members fs F.1) xs == (members fs F.1).length ||
      zeroCount p ds (members fs F.1) xs == F.2.1) &&
    decide ((allPts ds).countP (fun xs =>
      zeroCount p ds (members fs F.1) xs == (members fs F.1).length) ≤ F.2.2)

/-- Check point `q = (flat, coordinates)`'s index on the hyperplane `f` at depth `d`. -/
def ixOf (p : ℕ) (ds : List ℕ) (flats : List Flat) (d : ℕ) (f : List ℕ) (q : ℕ × List ℕ) :
    ℕ :=
  if (flats.getD q.1 ([], 0, 0)).1.getD d false then dotL ds f q.2 % p else p

/-- Check point `q`'s target `α s`, step `N − α` and half-width `(N − α) c κ`. -/
def csOf (s : ℤ) (c : ℕ) (fs : List (List ℕ)) (flats : List Flat) (q : ℕ × List ℕ) :
    ℤ × ℤ × ℤ :=
  ((((flats.getD q.1 ([], 0, 0)).2.1 : ℕ) : ℤ) * s,
    (((members fs (flats.getD q.1 ([], 0, 0)).1).length - (flats.getD q.1 ([], 0, 0)).2.1 : ℕ) : ℤ),
    (((members fs (flats.getD q.1 ([], 0, 0)).1).length - (flats.getD q.1 ([], 0, 0)).2.1 : ℕ) :
      ℤ) * c * (flats.getD q.1 ([], 0, 0)).2.2)

/-- Pairwise some member tells the coordinate lists apart. -/
def sepOK (p : ℕ) (ds : List ℕ) (hs : List (List ℕ)) : List (List ℕ) → Bool
  | [] => true
  | x :: xs => xs.all (fun x' => hs.any fun f => dotL ds f x % p != dotL ds f x' % p) &&
    sepOK p ds hs xs

/-- The certificate's checks: one level per hyperplane, each hyperplane onto, the flats' counts,
the check points' targets and indices, the lengths, and the first `m` check points pairwise in
distinct classes of the first check point's flat. -/
def certOK (p : ℕ) (ds : List ℕ) (s : ℤ) (c : ℕ) (fs : List (List ℕ)) (flats : List Flat)
    (cps : List (ℕ × List ℕ)) (cs : List (ℤ × ℤ × ℤ)) (lv : List Level) (L H : List ℤ)
    (m : ℕ) : Bool :=
  lv.length == fs.length &&
    fs.all (fun f => (allPts ds).any fun xs => dotL ds f xs % p == 1) &&
    flats.all (incOK p ds fs) &&
    cps.all (fun q => decide (q.1 < flats.length)) &&
    cs == cps.map (csOf s c fs flats) &&
    L.length == cps.length && H.length == cps.length && lenOK cps.length lv &&
    allTo (fun d => (lv.getD d ([], [], [])).1 == cps.map (ixOf p ds flats d (fs.getD d [])))
      fs.length &&
    decide (m ≤ cps.length) &&
    (cps.take m).all (fun q => q.1 == (cps.getD 0 (0, [])).1) &&
    sepOK p ds (members fs (flats.getD (cps.getD 0 (0, [])).1 ([], 0, 0)).1)
      ((cps.take m).map (·.2))

/-! ### Soundness -/

theorem members_sum (g : List ℕ → ℤ) : ∀ (fs : List (List ℕ)) (mem : List Bool),
    ∑ d ∈ Finset.range fs.length, (if mem.getD d false then g (fs.getD d []) else 0) =
      ((members fs mem).map g).sum
  | [], _ => by simp [members]
  | f :: fs, [] => by simp [members]
  | f :: fs, b :: bs => by
    rw [List.length_cons, Finset.sum_range_succ']
    have := members_sum g fs bs
    simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
    rw [this]
    cases b <;> simp [members, add_comm]

theorem getD_map_of_lt {α β : Type*} (f : α → β) (l : List α) (d : α) (e : β) {i : ℕ}
    (h : i < l.length) : (l.map f).getD i e = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map,
    List.getD_eq_getElem _ _ h]

theorem sum_range_getD {α : Type*} (g : α → ℤ) (d : α) : ∀ (l : List α) (m : ℕ), m ≤ l.length →
    ∑ j ∈ Finset.range m, g (l.getD j d) = ((l.take m).map g).sum
  | _, 0, _ => by simp
  | [], _ + 1, h => by simp at h
  | a :: l, m + 1, h => by
    rw [Finset.sum_range_succ', List.take_succ_cons, List.map_cons, List.sum_cons,
      ← sum_range_getD g d l m (by simpa using h)]
    simp [add_comm]

theorem abs_sum_sign_le {G : Type*} (S : Finset G) (D : G → SignType) :
    |∑ x ∈ S, (D x : ℤ)| ≤ S.card := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases D x with _ | _ | _ <;> simp

section Sound

variable {G : Type*} [AddCommGroup G] [Fintype G] {p : ℕ} [hp : Fact p.Prime] {ds : List ℕ}

/-- Coordinate lists pairwise told apart by `hs` have disjoint check-point sets, so their box
values have absolute sum at most the absolute sum of `D` over their union. -/
theorem sum_abs_flat_le (hds : ∀ d ∈ ds, d = p) (φ : G →+ Grp ds) (D : G → SignType)
    (hs : List (List ℕ)) : ∀ xss : List (List ℕ), sepOK p ds hs xss = true →
      (xss.map fun xs => |∑ x ∈ Finset.univ.filter (fun x => ∀ h ∈ hs.map (hyp p ds hds),
        h (φ x - Grp.ofList ds xs) = 0), (D x : ℤ)|).sum ≤
      ∑ x ∈ Finset.univ.filter (fun x => ∃ xs ∈ xss, ∀ h ∈ hs.map (hyp p ds hds),
        h (φ x - Grp.ofList ds xs) = 0), |(D x : ℤ)|
  | [], _ => by simp
  | xs :: xss, h => by
    classical
    simp only [sepOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, bne_iff_ne,
      ne_eq] at h
    have ih := sum_abs_flat_le hds φ D hs xss h.2
    set S := Finset.univ.filter (fun x => ∀ h ∈ hs.map (hyp p ds hds),
      h (φ x - Grp.ofList ds xs) = 0)
    set U := Finset.univ.filter (fun x => ∃ xs' ∈ xss, ∀ h ∈ hs.map (hyp p ds hds),
      h (φ x - Grp.ofList ds xs') = 0)
    have hdisj : Disjoint S U := by
      rw [Finset.disjoint_left]
      intro x hxS hxU
      simp only [S, U, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hxS hxU
      obtain ⟨xs', hxs', hx'⟩ := hxU
      obtain ⟨f, hf, hne⟩ := h.1 xs' hxs'
      have e1 := hxS f hf
      have e2 := hx' f hf
      rw [map_sub, sub_eq_zero, hyp_ofList] at e1 e2
      rw [e1, ZMod.natCast_eq_natCast_iff', Nat.mod_mod, Nat.mod_mod] at e2
      exact hne e2
    have hU : Finset.univ.filter (fun x => ∃ xs' ∈ xs :: xss, ∀ h ∈ hs.map (hyp p ds hds),
        h (φ x - Grp.ofList ds xs') = 0) = S ∪ U := by
      ext x
      simp [S, U]
    rw [hU, Finset.sum_union hdisj, List.map_cons, List.sum_cons]
    exact add_le_add (Finset.abs_sum_le_sum_abs _ _) ih

theorem natCast_sub_pos {a b : ℕ} (h : a < b) : (0 : ℤ) < ((b - a : ℕ) : ℤ) := by
  have : 0 < b - a := Nat.sub_pos_of_lt h
  exact_mod_cast this

/-- Hyperplane tomography on a quotient `φ : Grp ms → Grp ds` (`ds` all `p`, fibres `c`), the
core: no SDS when every SDS with `Σ D = s` has a translate (or other SDS with that sum) whose
hyperplane contractions are among the options at their depths, the certificate passes `certOK`
and `boundsOK`, and `flatKill` passes. -/
theorem not_hasSDS_flat_core {ms : List ℕ} (hds : ∀ d ∈ ds, d = p) {A P : List (List ℕ)}
    (hmap : MapOk ms ds A) (hsurj : SurjCert ms ds A P) (inst : Fintype (Grp ms))
    {c k : ℕ} {lam s : ℤ} (hc : ms.prod = c * ds.prod)
    (hs : s * s = k + lam * ((ms.prod : ℤ) - 1)) {U W : List (List ℤ)} {u : ℕ}
    {fs : List (List ℕ)} {flats : List Flat} {cps : List (ℕ × List ℕ)}
    {cs : List (ℤ × ℤ × ℤ)} {lv : List Level} {L H : List ℤ} {m : ℕ}
    (hlist : ∀ D : Grp ms → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s →
      ∃ D' : Grp ms → SignType, IsSDS k lam D' ∧ ∑ x, (D' x : ℤ) = s ∧ ∀ i < fs.length,
        vecOf p (contract ((hyp p ds hds (fs.getD i [])).comp (linMap ms ds A hmap)) D') ∈
          optsAt U W (u - i))
    (hcert : certOK p ds s c fs flats cps cs lv L H m = true)
    (hb : boundsOK U W u lv L H = true) (hkill : flatKill k m cs U W u L H lv = true) :
    ¬ @HasSDS (Grp ms) _ inst k lam := by
  have hp0 : 0 < p := hp.out.pos
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => by rw [hds d hd]; exact hp0
  let FQ : Fintype (Grp ds) := Grp.fintype ds hpos
  set φ : Grp ms →+ Grp ds := linMap ms ds A hmap with hφdef
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcardG : Fintype.card (Grp ms) = c * Fintype.card (Grp ds) := by
    rw [Grp.card_eq, Grp.card_eq, hc]
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcert
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlv, -⟩, hinc⟩, hcpF⟩, hcs⟩, hL⟩, hH⟩, hlen⟩, hix⟩, hm⟩, hsame⟩, hsep⟩ :=
    hcert
  rw [List.all_eq_true] at hinc hcpF hsame
  rw [allTo_iff] at hix
  have hcsl : cs.length = cps.length := by rw [hcs, List.length_map]
  have key : ∀ D : Grp ms → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s → False := by
    intro D0 hD0 hsum0
    obtain ⟨D', hD', hsum', hlistD⟩ := hlist D0 hD0 hsum0
    set Y : List ℕ → ZMod p → ℤ := fun f => contract ((hyp p ds hds f).comp φ) D' with hY
    set ys := fs.map fun f => vecOf p (Y f) with hys
    have hysl : ys.length = lv.length := by rw [hys, List.length_map, hlv]
    have hysd : ∀ d < fs.length, ys.getD d [] = vecOf p (Y (fs.getD d [])) := fun d hd =>
      getD_map_of_lt _ fs [] [] hd
    -- the value at each check point
    have hval : ∀ j < cps.length,
        colSum j lv ys = (((flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).2.1 : ℕ) : ℤ) * s +
          (((members fs (flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).1).length -
            (flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).2.1 : ℕ) : ℤ) *
          ∑ x ∈ Finset.univ.filter (fun x => ∀ h ∈ (members fs
            (flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).1).map (hyp p ds hds),
            h (φ x - Grp.ofList ds (cps.getD j (0, [])).2) = 0), (D' x : ℤ) := by
      intro j hj
      set q := cps.getD j (0, []) with hq
      set F := flats.getD q.1 ([], 0, 0) with hF
      have hFmem : F ∈ flats := by
        have hq1 : q.1 < flats.length := by
          refine of_decide_eq_true (hcpF q ?_)
          rw [hq, List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem _
        rw [hF, List.getD_eq_getElem _ _ hq1]
        exact List.getElem_mem _
      have hincF := hinc F hFmem
      simp only [incOK, Bool.and_eq_true, decide_eq_true_eq] at hincF
      rw [colSum_eq j lv ys hysl, hlv]
      have e1 : ∀ d ∈ Finset.range fs.length,
          (ys.getD d []).getD ((lv.getD d ([], [], [])).1.getD j 0) 0 =
            if F.1.getD d false then Y (fs.getD d []) (hyp p ds hds (fs.getD d [])
              (Grp.ofList ds q.2)) else 0 := by
        intro d hd
        rw [Finset.mem_range] at hd
        rw [hysd d hd, (by simpa using hix d hd : (lv.getD d ([], [], [])).1 =
          cps.map (ixOf p ds flats d (fs.getD d []))), getD_map_of_lt _ _ (0, []) _ hj, ← hq]
        unfold ixOf
        rw [← hF]
        split_ifs with hmemF
        · rw [vecOf_getD _ (Nat.mod_lt _ hp0), hyp_ofList]
        · rw [List.getD_eq_default _ _ (by simp [vecOf])]
      rw [Finset.sum_congr rfl e1, members_sum (fun f => Y f (hyp p ds hds f (Grp.ofList ds q.2)))]
      have e2 := sum_contract_flat φ D' (hs := (members fs F.1).map (hyp p ds hds)) (α := F.2.1)
        (by rw [List.length_map]; exact hincF.1.1.le)
        (countP_hyp_eq hds (by simpa [zeroCount] using hincF.1.2)) (Grp.ofList ds q.2)
      rw [List.map_map] at e2
      rw [List.length_map, hsum'] at e2
      exact e2
    -- the box
    have hbox : ∀ j < cps.length,
        |∑ x ∈ Finset.univ.filter (fun x => ∀ h ∈ (members fs
            (flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).1).map (hyp p ds hds),
            h (φ x - Grp.ofList ds (cps.getD j (0, [])).2) = 0), (D' x : ℤ)| ≤
          c * (flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).2.2 := by
      intro j hj
      set q := cps.getD j (0, []) with hq
      set F := flats.getD q.1 ([], 0, 0) with hF
      have hFmem : F ∈ flats := by
        have hq1 : q.1 < flats.length := by
          refine of_decide_eq_true (hcpF q ?_)
          rw [hq, List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem _
        rw [hF, List.getD_eq_getElem _ _ hq1]
        exact List.getElem_mem _
      have hincF := hinc F hFmem
      simp only [incOK, Bool.and_eq_true, decide_eq_true_eq] at hincF
      refine (abs_sum_sign_le _ D').trans ?_
      rw [card_flat hφ hcardG]
      have hk := card_ker_le hds (members fs F.1)
      have hk' : (Finset.univ.filter fun z : Grp ds =>
          ∀ h ∈ (members fs F.1).map (hyp p ds hds), h z = 0).card ≤ F.2.2 :=
        hk.trans (by simpa [zeroCount] using hincF.2)
      exact_mod_cast Nat.mul_le_mul_left c hk'
    have hcsj : ∀ j < cps.length,
        cs.getD j (0, 0, 0) = csOf s c fs flats (cps.getD j (0, [])) := fun j hj => by
      rw [hcs]
      exact getD_map_of_lt _ _ _ _ hj
    have hαN : ∀ j < cps.length, (flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).2.1 <
        (members fs (flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).1).length := by
      intro j hj
      have hq1 : (cps.getD j (0, [])).1 < flats.length := by
        refine of_decide_eq_true (hcpF _ ?_)
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem _
      have hincF := hinc (flats.getD (cps.getD j (0, [])).1 ([], 0, 0))
        (by rw [List.getD_eq_getElem _ _ hq1]; exact List.getElem_mem _)
      simp only [incOK, Bool.and_eq_true, decide_eq_true_eq] at hincF
      exact hincF.1.1
    -- the value minus the target is `N − α` times the box value
    have hZ : ∀ j < cps.length, colSum j lv ys - (cs.getD j (0, 0, 0)).1 =
        (cs.getD j (0, 0, 0)).2.1 *
          ∑ x ∈ Finset.univ.filter (fun x => ∀ h ∈ (members fs
            (flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).1).map (hyp p ds hds),
            h (φ x - Grp.ofList ds (cps.getD j (0, [])).2) = 0), (D' x : ℤ) := by
      intro j hj
      rw [hcsj j hj, hval j hj]
      simp only [csOf]
      ring
    refine flatKill_false (J := cps.length) hkill hb hlen hL hH hcsl ys hysl ?_ ?_ ?_
    · intro i hi
      rw [hysd i (by rw [← hlv]; exact hi)]
      exact hlistD i (by rw [← hlv]; exact hi)
    · intro j hj
      have hg : 0 < (cs.getD j (0, 0, 0)).2.1 := by
        rw [hcsj j hj]
        exact natCast_sub_pos (hαN j hj)
      refine ⟨hg, ⟨_, hZ j hj⟩, ?_⟩
      rw [hZ j hj, abs_mul, abs_of_pos hg]
      have hw : (cs.getD j (0, 0, 0)).2.2 = (cs.getD j (0, 0, 0)).2.1 *
          (c * (flats.getD (cps.getD j (0, [])).1 ([], 0, 0)).2.2) := by
        rw [hcsj j hj]
        simp only [csOf]
        ring
      rw [hw]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbox j hj) hg.le
    · have hmJ : m ≤ cps.length := hm
      rw [absSumOf_eq m _ cs (by simpa using hmJ) (by rw [hcsl]; exact hmJ)]
      set F0 := flats.getD (cps.getD 0 (0, [])).1 ([], 0, 0) with hF0
      set Zf : List ℕ → ℤ := fun xs => |∑ x ∈ Finset.univ.filter (fun x =>
        ∀ h ∈ (members fs F0.1).map (hyp p ds hds), h (φ x - Grp.ofList ds xs) = 0),
        (D' x : ℤ)| with hZf
      have e1 : ∀ j ∈ Finset.range m,
          |(((List.range cps.length).map fun j => colSum j lv ys).getD j 0 -
            (cs.getD j (0, 0, 0)).1) / (cs.getD j (0, 0, 0)).2.1| =
            (fun q : ℕ × List ℕ => Zf q.2) (cps.getD j (0, [])) := by
        intro j hj
        rw [Finset.mem_range] at hj
        have hjc : j < cps.length := by omega
        have hg : (cs.getD j (0, 0, 0)).2.1 ≠ 0 := by
          rw [hcsj j hjc]
          exact (natCast_sub_pos (hαN j hjc)).ne'
        rw [getD_map_of_lt _ _ 0 _ (by simpa using hjc),
          List.getD_eq_getElem _ _ (by simpa using hjc), List.getElem_range, hZ j hjc,
          Int.mul_ediv_cancel_left _ hg]
        have hsj : (cps.getD j (0, [])).1 = (cps.getD 0 (0, [])).1 := by
          refine beq_iff_eq.1 (hsame _ ?_)
          rw [List.getD_eq_getElem _ _ hjc]
          exact List.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩
        simp only [hZf, hF0, hsj]
      rw [Finset.sum_congr rfl e1]
      refine (sum_range_getD (fun q : ℕ × List ℕ => Zf q.2) (0, []) cps m hmJ).trans_le ?_
      have e2 := sum_abs_flat_le hds φ D' (members fs F0.1) _ hsep
      rw [List.map_map] at e2
      refine e2.trans ?_
      rw [← hD'.sum_abs]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun x _ _ => abs_nonneg _
  rintro ⟨D, hD⟩
  have hsq := hD.sum_sq
  rw [Grp.card_eq, sq, ← hs] at hsq
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key D hD h1
  · refine key _ hD.neg ?_
    simp only [SignType.coe_neg, Finset.sum_neg_distrib, h1, neg_neg]


/-- The hyperplanes of a passing certificate are onto. -/
theorem certOK_surj {s : ℤ} {c m : ℕ} {fs : List (List ℕ)} {flats : List Flat}
    {cps : List (ℕ × List ℕ)} {cs : List (ℤ × ℤ × ℤ)} {lv : List Level} {L H : List ℤ}
    (hds : ∀ d ∈ ds, d = p) (h : certOK p ds s c fs flats cps cs lv L H m = true) :
    ∀ f ∈ fs, Function.Surjective (hyp p ds hds f) := by
  simp only [certOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hsur⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact fun f hf => hyp_surjective hds (List.all_eq_true.1 hsur f hf)

theorem contract_translate {H : Type*} [AddCommGroup H] [DecidableEq H] (ψ : G →+ H)
    (D : G → SignType) (t : G) (u : H) :
    contract ψ (fun x => D (x + t)) u = contract ψ D (u + ψ t) := by
  unfold contract
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Fintype.sum_equiv (Equiv.addRight t) _ _ fun x => by simp [map_add]

theorem sum_contract_translate (ψ : G →+ ZMod p) (D : G → SignType) (h₀ : ZMod p) :
    ∑ u, contract ψ D (u + h₀) = ∑ x, (D x : ℤ) := by
  rw [← sum_contractQ ψ D]
  exact Fintype.sum_equiv (Equiv.addRight h₀) _ _ fun _ => rfl

/-- Hyperplane tomography on a quotient, centred: no SDS when `p ∤ s`, every centred hyperplane
contraction (fibres `C`, `|G| = C p`) lies in `W`, the certificate passes `certOK` and
`boundsOK`, and `flatKill` passes. -/
theorem not_hasSDS_flat {ms : List ℕ} (hds : ∀ d ∈ ds, d = p) {A P : List (List ℕ)}
    (hmap : MapOk ms ds A) (hsurj : SurjCert ms ds A P) (inst : Fintype (Grp ms))
    {c C k : ℕ} {lam s : ℤ} (hc : ms.prod = c * ds.prod) (hC : ms.prod = C * p)
    (hs : s * s = k + lam * ((ms.prod : ℤ) - 1)) (hsp : (s : ZMod p) ≠ 0) {W : List (List ℤ)}
    (hW : ∀ b : ZMod p → ℤ, Demands C k lam b → ∑ h, b h = s →
      ∑ x, ((b x : ℤ) : ZMod p) * x = 0 → vecOf p b ∈ W)
    {fs : List (List ℕ)} {flats : List Flat} {cps : List (ℕ × List ℕ)}
    {cs : List (ℤ × ℤ × ℤ)} {lv : List Level} {L H : List ℤ} {m : ℕ}
    (hcert : certOK p ds s c fs flats cps cs lv L H m = true)
    (hb : boundsOK W W 0 lv L H = true) (hkill : flatKill k m cs W W 0 L H lv = true) :
    ¬ @HasSDS (Grp ms) _ inst k lam := by
  have hφ := linMap_surjective hmap hsurj
  have hcardC : Fintype.card (Grp ms) = C * p := by rw [Grp.card_eq, hC]
  refine not_hasSDS_flat_core hds hmap hsurj inst hc hs (U := W) (u := 0)
    (fun D hD hsum => ?_) hcert hb hkill
  have hS : (((∑ x, (D x : ℤ) : ℤ)) : ZMod p) ≠ 0 := by rw [hsum]; exact hsp
  obtain ⟨t, ht⟩ := exists_centered_flat hds hφ D hS
  have hsum' : ∑ x, (D (x + t) : ℤ) = s := by
    rw [← hsum]
    exact Fintype.sum_equiv (Equiv.addRight t) _ (fun x => (D x : ℤ)) fun _ => rfl
  refine ⟨fun x => D (x + t), hD.translate t, hsum', fun i hi => ?_⟩
  have e : optsAt W W (0 - i) = W := by unfold optsAt; split_ifs <;> rfl
  rw [e]
  have hf : fs.getD i [] ∈ fs := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  have hsurjf : Function.Surjective ((hyp p ds hds (fs.getD i [])).comp
      (linMap ms ds A hmap)) := by
    rw [AddMonoidHom.coe_comp]
    exact (certOK_surj hds hcert _ hf).comp hφ
  refine hW _ (demands_hyp hsurjf hcardC (hD.translate t)) ?_ (moment_hyp ht _)
  rw [sum_contractQ, hsum']

theorem dotL_nil (ds xs : List ℕ) : dotL ds [] xs = 0 := by
  induction ds generalizing xs with
  | nil => rfl
  | cons d ds ih =>
    cases ds with
    | nil => simp [dotL]
    | cons d' ds => simp [dotL, ih]

theorem dotL_unitL : ∀ (ds : List ℕ) (j : ℕ) (xs : List ℕ), j < ds.length →
    dotL ds (unitL j) xs = xs.getD j 0
  | [], _, _, h => by simp at h
  | [_], 0, xs, _ => by cases xs <;> simp [dotL, unitL]
  | [_], _ + 1, _, h => by simp at h
  | _ :: d' :: ds, 0, xs, _ => by cases xs <;> simp [dotL, unitL, dotL_nil]
  | _ :: d' :: ds, j + 1, xs, h => by
    have := dotL_unitL (d' :: ds) j xs.tail (by simpa using h)
    cases xs <;> simp_all [dotL, unitL]

/-- Hyperplane tomography on a quotient without centring: the first `r ≤ |ds|` hyperplanes are
the coordinates (`unitL`); a translate puts the largest `|·|` of each of their contractions at
`0`, so these lie in `U`, every hyperplane contraction lies in `W`; with a passing certificate
and `flatKill` there is no SDS. -/
theorem not_hasSDS_flat_nc {ms : List ℕ} (hds : ∀ d ∈ ds, d = p) {A P : List (List ℕ)}
    (hmap : MapOk ms ds A) (hsurj : SurjCert ms ds A P) (inst : Fintype (Grp ms))
    {c C k : ℕ} {lam s : ℤ} (hc : ms.prod = c * ds.prod) (hC : ms.prod = C * p)
    (hs : s * s = k + lam * ((ms.prod : ℤ) - 1)) {U W : List (List ℤ)}
    (hU : ∀ b : ZMod p → ℤ, Demands C k lam b → ∑ h, b h = s → (∀ h, |b h| ≤ |b 0|) →
      vecOf p b ∈ U)
    (hW : ∀ b : ZMod p → ℤ, Demands C k lam b → ∑ h, b h = s → vecOf p b ∈ W)
    {fs : List (List ℕ)} {flats : List Flat} {cps : List (ℕ × List ℕ)}
    {cs : List (ℤ × ℤ × ℤ)} {lv : List Level} {L H : List ℤ} {m r : ℕ} (hr : r ≤ ds.length)
    (hunit : ∀ j < r, fs.getD j [] = unitL j)
    (hcert : certOK p ds s c fs flats cps cs lv L H m = true)
    (hb : boundsOK U W r lv L H = true) (hkill : flatKill k m cs U W r L H lv = true) :
    ¬ @HasSDS (Grp ms) _ inst k lam := by
  have hφ := linMap_surjective hmap hsurj
  have hcardC : Fintype.card (Grp ms) = C * p := by rw [Grp.card_eq, hC]
  refine not_hasSDS_flat_core hds hmap hsurj inst hc hs (U := U) (W := W) (u := r)
    (fun D hD hsum => ?_) hcert hb hkill
  set φ := linMap ms ds A hmap
  have hsurjf : ∀ i < fs.length, Function.Surjective ((hyp p ds hds (fs.getD i [])).comp φ) := by
    intro i hi
    have hf : fs.getD i [] ∈ fs := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem _
    rw [AddMonoidHom.coe_comp]
    exact (certOK_surj hds hcert _ hf).comp hφ
  have hmax : ∀ j : ℕ, ∃ h₀ : ZMod p, ∀ h,
      |contract ((hyp p ds hds (unitL j)).comp φ) D h| ≤
        |contract ((hyp p ds hds (unitL j)).comp φ) D h₀| := fun j => by
    obtain ⟨h₀, -, hm⟩ := Finset.exists_max_image Finset.univ
      (fun h => |contract ((hyp p ds hds (unitL j)).comp φ) D h|) Finset.univ_nonempty
    exact ⟨h₀, fun h => hm h (Finset.mem_univ _)⟩
  choose h₀ hh₀ using hmax
  obtain ⟨t, ht⟩ := hφ (Grp.ofList ds ((List.range r).map fun j => (h₀ j).val))
  have hsum' : ∑ x, (D (x + t) : ℤ) = s := by
    rw [← hsum]
    exact Fintype.sum_equiv (Equiv.addRight t) _ (fun x => (D x : ℤ)) fun _ => rfl
  refine ⟨fun x => D (x + t), hD.translate t, hsum', fun i hi => ?_⟩
  by_cases hir : i < r
  · have e : optsAt U W (r - i) = U := by unfold optsAt; rw [ite_eq_right (by omega)]
    rw [e, hunit i hir]
    have e2 : contract ((hyp p ds hds (unitL i)).comp φ) (fun x => D (x + t)) =
        fun u => contract ((hyp p ds hds (unitL i)).comp φ) D (u + h₀ i) := by
      funext u
      rw [contract_translate, AddMonoidHom.comp_apply, ht, hyp_ofList,
        dotL_unitL ds i _ (by omega), getD_map_of_lt _ _ 0 _ (by simpa using hir),
        List.getD_eq_getElem _ _ (by simpa using hir), List.getElem_range, ZMod.natCast_mod,
        ZMod.natCast_zmod_val]
    rw [e2]
    have hsi := hsurjf i hi
    rw [hunit i hir] at hsi
    refine hU _ ((demands_hyp hsi hcardC hD).translate (h₀ i)) ?_ fun h => ?_
    · rw [sum_contract_translate, hsum]
    · simpa using hh₀ i (h + h₀ i)
  · have e : optsAt U W (r - i) = W := by unfold optsAt; rw [ite_eq_left (by omega)]
    rw [e]
    refine hW _ (demands_hyp (hsurjf i hi) hcardC (hD.translate t)) ?_
    rw [sum_contractQ, hsum']

end Sound

end SignedDifferenceSets.TomographyFlat
