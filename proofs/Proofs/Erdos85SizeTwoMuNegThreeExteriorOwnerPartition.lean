import Proofs.Erdos85SizeTwoMuNegThreeCrossOwnerInjective

/-! # The `24 + 24` exterior-owner partition at `mu = -3` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def MuNegThreeCrossOwnerNormalForm.crossOwnerFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s) : Finset V :=
  (Finset.univ.image N.o₀ ∪ Finset.univ.image N.oσ) ∪
    Finset.univ.image N.oτ

def componentExteriorFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {D : SimpleGraph V} (c : D.ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter fun z ↦ z ∉ c.supp

/-- The 24 normalized cross owners are exactly the vertices having an
ambient neighbour of each sign inside the component. -/
theorem MuNegThreeCrossOwnerNormalForm.mem_crossOwnerFinset_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s) (z : V) :
    z ∈ N.crossOwnerFinset G c s ↔
      z ∉ c.supp ∧ ∃ x : MuNegThreePositiveShore
        (secondOrderDefectGraph G) c s,
        ∃ y : MuNegThreeNegativeShore (secondOrderDefectGraph G) c s,
          G.Adj x.1 z ∧ G.Adj y.1 z := by
  classical
  constructor
  · intro hz
    simp only [crossOwnerFinset, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and] at hz
    rcases hz with (⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩
    · exact ⟨N.o₀_out x, x, N.f x, (N.owner₀ x (N.o₀ x)).2 rfl⟩
    · exact ⟨N.oσ_out x, x, N.f (N.σ x), (N.ownerσ x (N.oσ x)).2 rfl⟩
    · exact ⟨N.oτ_out x, x, N.f (N.τ x), (N.ownerτ x (N.oτ x)).2 rfl⟩
  · rintro ⟨hzout, x, y, hxy⟩
    have hnondef :=
      (orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
        G hfree c s x x y y z hxy hxy).1
    rcases (N.exhaust x y).mp hnondef with hy | hy | hy
    · have howner : z = N.o₀ x := (N.owner₀ x z).mp (by simpa [hy] using hxy)
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, howner.symm⟩
    · have howner : z = N.oσ x := (N.ownerσ x z).mp (by simpa [hy] using hxy)
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, howner.symm⟩
    · have howner : z = N.oτ x := (N.ownerτ x z).mp (by simpa [hy] using hxy)
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, howner.symm⟩

/-- A size-16 component in an order-64 graph has 48 exterior vertices. -/
theorem orderSixtyFour_componentExteriorFinset_card_fortyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    {D : SimpleGraph V} (hcard : Fintype.card V = 8 * 8)
    (c : D.ConnectedComponent) (hc : c.supp.ncard = 8 * 2) :
    (componentExteriorFinset c).card = 48 := by
  classical
  have hsupp : ((Finset.univ : Finset V).filter fun z ↦ z ∈ c.supp).card = 16 := by
    calc
      _ = c.supp.toFinset.card := by
        congr
        ext z
        simp
      _ = c.supp.ncard := (Set.ncard_eq_toFinset_card' c.supp).symm
      _ = 16 := by omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (fun z : V ↦ z ∈ c.supp) (s := Finset.univ)
  change ((Finset.univ.filter fun z : V ↦ z ∈ c.supp).card +
    (componentExteriorFinset c).card = Finset.univ.card) at hsplit
  rw [hsupp, Finset.card_univ, hcard] at hsplit
  omega

/-- Membership in the complementary exterior half is exactly the absence of
an opposite-sign component-neighbour pair. Since every exterior vertex has
two component neighbours, this is the same-sign-owner side of the split. -/
theorem MuNegThreeCrossOwnerNormalForm.mem_exterior_sdiff_crossOwner_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s) (z : V) :
    z ∈ componentExteriorFinset c \ N.crossOwnerFinset G c s ↔
      z ∉ c.supp ∧ ¬ ∃ x : MuNegThreePositiveShore
        (secondOrderDefectGraph G) c s,
        ∃ y : MuNegThreeNegativeShore (secondOrderDefectGraph G) c s,
          G.Adj x.1 z ∧ G.Adj y.1 z := by
  classical
  rw [Finset.mem_sdiff]
  change (z ∈ Finset.univ.filter (fun z ↦ z ∉ c.supp) ∧
    z ∉ N.crossOwnerFinset G c s) ↔ _
  rw [N.mem_crossOwnerFinset_iff G hfree c s z]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
  constructor
  · rintro ⟨hzout, hno⟩
    exact ⟨hzout, hno hzout⟩
  · rintro ⟨hzout, hno⟩
    exact ⟨hzout, fun _ ↦ hno⟩

/-- Exactly 24 exterior vertices are not cross owners. These are the
remaining same-sign-owner half of the exterior. -/
theorem MuNegThreeCrossOwnerNormalForm.exterior_sdiff_crossOwner_card_twentyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s)
    (hshore : Fintype.card
      (MuNegThreePositiveShore (secondOrderDefectGraph G) c s) = 8) :
    (componentExteriorFinset c \ N.crossOwnerFinset G c s).card = 24 := by
  have hcross : (N.crossOwnerFinset G c s).card = 24 :=
    N.cross_owner_union_card_twentyFour G hfree hreg hcard c hc s hshore
  have hext : (componentExteriorFinset c).card = 48 :=
    orderSixtyFour_componentExteriorFinset_card_fortyEight hcard c hc
  have hsub : N.crossOwnerFinset G c s ⊆ componentExteriorFinset c := by
    intro z hz
    change z ∈ Finset.univ.filter (fun z ↦ z ∉ c.supp)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
      (N.mem_crossOwnerFinset_iff G hfree c s z).mp hz |>.1⟩
  rw [Finset.card_sdiff_of_subset hsub, hext, hcross]

end

end Erdos85

#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.mem_crossOwnerFinset_iff
#print axioms Erdos85.orderSixtyFour_componentExteriorFinset_card_fortyEight
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.mem_exterior_sdiff_crossOwner_iff
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.exterior_sdiff_crossOwner_card_twentyFour
