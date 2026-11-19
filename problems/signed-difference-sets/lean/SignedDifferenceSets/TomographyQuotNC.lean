module

public import SignedDifferenceSets.TomographyQuot

/-!
# Line tomography on a quotient without centring (I23)

`not_hasSDS_quot` centres `D` first, which needs `p ∤ s`. Without it the line contractions are
still valid vectors with sum `±s` and the line identity still holds, so it suffices that `W`
holds every valid vector with sum `s` (`rotAllOK`: all rotations of the vectors `inSearch` lists).
`not_hasSDS_quot_nc`, and `not_hasSDS_grp_nc` for the table's groups.
-/

@[expose] public section

namespace SignedDifferenceSets.Tomography

/-- Every rotation of a vector of `V0` is in `W`. -/
def rotAllOK (p : ℕ) (V0 W : List (List ℤ)) : Bool :=
  V0.all fun v => allTo (fun r => W.contains (rot p r v)) p

variable {p : ℕ} [hp : Fact p.Prime]

/-- `inSearch` and `rotAllOK` with fibres of `C` list every vector meeting the demands with
sum `s`. -/
theorem lists_all_of_inSearch {C k : ℕ} {lam s : ℤ} {V0 W : List (List ℤ)}
    (hV : inSearch (Indexed.size (ZMod p)) (Indexed.addIdx (ZMod p)) C
      (k + lam * ((C : ℤ) - 1)) (lam * C) k s V0 = true)
    (hW : rotAllOK p V0 W = true) (b : ZMod p → ℤ) (hb : Demands C k lam b)
    (hs : ∑ h, b h = s) : vecOf p b ∈ W := by
  obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => |b h|)
    Finset.univ_nonempty
  have hv0 : vecOf p (fun h => b (h + h₀)) ∈ V0 :=
    mem_of_inSearch (H := ZMod p) hV (hb.translate h₀)
      (fun h => by simpa using hmax (h + h₀) (Finset.mem_univ _))
      (by rw [← hs]; exact Fintype.sum_equiv (Equiv.addRight h₀) _ b fun _ => rfl)
  have hr := (allTo_iff _ _).1 (List.all_eq_true.1 hW _ hv0) (-h₀).val (ZMod.val_lt _)
  rw [rot_vecOf, List.contains_iff_mem] at hr
  exact hr

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Line tomography on a quotient, without centring: no SDS on `G` when `φ` is onto with
fibres of `c`, every vector meeting the line contractions' demands (fibres `c p`) with sum `s`
is in `W`, and no choice of one per line from `W` passes `leafQ`. -/
theorem not_hasSDS_quot_nc (p : ℕ) [Fact p.Prime] {c k : ℕ} {lam s : ℤ}
    (φ : G →+ ZMod p × ZMod p) (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * (p * p)) (hs : s * s = k + lam * ((c : ℤ) * p * p - 1))
    {W : List (List ℤ)}
    (hW : ∀ b : ZMod p → ℤ, Demands (c * p) k lam b → ∑ h, b h = s → vecOf p b ∈ W)
    (hC : ∀ ys : List (List ℤ), ys.length = p + 1 → (∀ y ∈ ys, y ∈ W) →
      leafQ p s c ys = true → False) :
    ¬ HasSDS G k lam := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have key : ∀ D : G → SignType, IsSDS k lam D → ∑ x, (D x : ℤ) = s → False := by
    intro D hD hsum
    set ys := (List.range (p + 1)).map fun j => vecOf p (contract (lineQ p j φ) D) with hys
    refine hC ys (by simp [ys]) (fun y hy => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
      exact hW _ (demands_lineQ hφ hcard hD j) (by rw [sum_contractQ, hsum])
    · rw [leafQ, allTo_iff]
      intro x _
      have e : lineSum p ys x = p * contract φ D (gOf p x) + s := by
        rw [lineSum, sumTo_eq, ← hsum, ← sum_contract_linesQ φ D (gOf p x)]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hys, getD_map_range' _ _ (Finset.mem_range.1 hj),
          vecOf_getD _ (lineIdx_lt hp0 j x), lineIdx_cast]
      have hb : |contract φ D (gOf p x)| ≤ c := by
        have := abs_contract_le φ D (gOf p x)
        rwa [card_fibre_eq hφ (by rw [hcard, Fintype.card_prod, ZMod.card])] at this
      rw [e, add_sub_cancel_right]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      refine ⟨Int.mul_emod_right _ _, ?_⟩
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p)]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
  rintro ⟨D, hD⟩
  have hdem := demands_lineQ hφ hcard hD 0
  set a := contract (lineQ p 0 φ) D
  have hsq : (∑ h, a h) * (∑ h, a h) = s * s := by
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hdem.sq, Finset.sum_congr rfl fun g hg => hdem.corr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card, hs, nsmul_eq_mul, Nat.cast_sub hp0]
    push_cast
    ring
  rw [sum_contractQ] at hsq
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key D hD h1
  · refine key _ hD.neg ?_
    simp only [SignType.coe_neg, Finset.sum_neg_distrib, h1, neg_neg]

/-- `not_hasSDS_quot_nc` on the table's group `Grp ms`, with `φ` given by the forms `A` (onto by
the preimages `P`). -/
theorem not_hasSDS_grp_nc {ms : List ℕ} (p : ℕ) [Fact p.Prime] {A P : List (List ℕ)}
    (hmap : MapOk ms [p, p] A) (hsurj : SurjCert ms [p, p] A P) (inst : Fintype (Grp ms))
    {c k : ℕ} {lam s : ℤ} (hcard : ms.prod = c * (p * p))
    (hs : s * s = k + lam * ((c : ℤ) * p * p - 1)) {W : List (List ℤ)}
    (hW : ∀ b : ZMod p → ℤ, Demands (c * p) k lam b → ∑ h, b h = s → vecOf p b ∈ W)
    (hC : ∀ ys : List (List ℤ), ys.length = p + 1 → (∀ y ∈ ys, y ∈ W) →
      leafQ p s c ys = true → False) :
    ¬ @HasSDS (Grp ms) _ inst k lam := by
  let φ : Grp ms →+ ZMod p × ZMod p := linMap ms [p, p] A hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcardG : Fintype.card (Grp ms) = c * (p * p) := by rw [Grp.card_eq, hcard]
  exact not_hasSDS_quot_nc p φ hφ hcardG hs hW hC

end SignedDifferenceSets.Tomography
