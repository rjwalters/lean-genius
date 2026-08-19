import Proofs.Erdos85SizeTwoMuNegThreeInternalStructure
import Proofs.Erdos85OrderEightTwoRegularComponentSizes

/-!
# The same-sign defect two-factors at `mu = -3`

The signed component shores are promoted to finite subtype graphs.  On each
eight-vertex shore the restricted defect relation is symmetric,
irreflexive, and two-regular, making the cycle-factor classification explicit.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

abbrev MuNegThreePositiveShore {V : Type*}
    (D : SimpleGraph V) (c : D.ConnectedComponent) (s : V → ℤ) :=
  {x : V // x ∈ c.supp ∧ s x = 1}

abbrev MuNegThreeNegativeShore {V : Type*}
    (D : SimpleGraph V) (c : D.ConnectedComponent) (s : V → ℤ) :=
  {x : V // x ∈ c.supp ∧ s x = -1}

/-- Exhaustive cycle partition proposition for an order-eight two-factor. -/
def MuNegThreeShoreCyclePartition {X : Type*} [Fintype X]
    (H : SimpleGraph X) : Prop :=
  (Nat.card H.ConnectedComponent = 1 ∧
    ∀ c : H.ConnectedComponent, c.supp.ncard = 8) ∨
  (Nat.card H.ConnectedComponent = 2 ∧
    ∀ c d : H.ConnectedComponent, c ≠ d →
      (c.supp.ncard = 3 ∧ d.supp.ncard = 5) ∨
      (c.supp.ncard = 4 ∧ d.supp.ncard = 4) ∨
      (c.supp.ncard = 5 ∧ d.supp.ncard = 3))

/-- Both same-sign restrictions of the defect graph are two-regular graphs
on eight vertices. -/
theorem orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_twoFactors
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
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegThreePositiveShore D c s
    let Xm := MuNegThreeNegativeShore D c s
    Fintype.card Xp = 8 ∧ Fintype.card Xm = 8 ∧
    (∀ x : Xp,
      ((Finset.univ : Finset Xp).filter fun y ↦ D.Adj x.1 y.1).card = 2) ∧
    (∀ x : Xm,
      ((Finset.univ : Finset Xm).filter fun y ↦ D.Adj x.1 y.1).card = 2) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  have hprofile := orderSixtyFour_sizeTwo_muNegThree_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hXpCard : Fintype.card Xp = 8 := by
    dsimp [Xp, MuNegThreePositiveShore, D]
    rw [Fintype.card_subtype]
    exact hprofile.1
  have hXmCard : Fintype.card Xm = 8 := by
    dsimp [Xm, MuNegThreeNegativeShore, D]
    rw [Fintype.card_subtype]
    exact hprofile.2.1
  have hsamePos (x : Xp) :
      ((Finset.univ : Finset Xp).filter fun y ↦ D.Adj x.1 y.1).card = 2 := by
    have himage :
        Finset.image Subtype.val
            ((Finset.univ : Finset Xp).filter fun y ↦ D.Adj x.1 y.1) =
          (D.neighborFinset x.1).filter fun y ↦ s y = 1 := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, D.mem_neighborFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.2.2⟩
      · rintro ⟨hxy, hsy⟩
        have hyc : y ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c y]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm.trans
            ((ConnectedComponent.mem_supp_iff c x.1).mp x.2.1)
        exact ⟨⟨y, hyc, hsy⟩, hxy, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Xp).filter fun y ↦ D.Adj x.1 y.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = ((D.neighborFinset x.1).filter fun y ↦ s y = 1).card :=
        congrArg Finset.card himage
      _ = 2 := (hprofile.2.2 x.1 x.2.1).1 x.2.2 |>.2.2.1
  have hsameNeg (x : Xm) :
      ((Finset.univ : Finset Xm).filter fun y ↦ D.Adj x.1 y.1).card = 2 := by
    have himage :
        Finset.image Subtype.val
            ((Finset.univ : Finset Xm).filter fun y ↦ D.Adj x.1 y.1) =
          (D.neighborFinset x.1).filter fun y ↦ s y = -1 := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, D.mem_neighborFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.2.2⟩
      · rintro ⟨hxy, hsy⟩
        have hyc : y ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c y]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm.trans
            ((ConnectedComponent.mem_supp_iff c x.1).mp x.2.1)
        exact ⟨⟨y, hyc, hsy⟩, hxy, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Xm).filter fun y ↦ D.Adj x.1 y.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = ((D.neighborFinset x.1).filter fun y ↦ s y = -1).card :=
        congrArg Finset.card himage
      _ = 2 := (hprofile.2.2 x.1 x.2.1).2 x.2.2 |>.2.2.1
  exact ⟨hXpCard, hXmCard, hsamePos, hsameNeg⟩

/-- Every connected cycle in either same-sign defect factor has one of the
only possible order-eight two-factor component sizes: `3`, `4`, `5`, or `8`. -/
theorem orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_component_size_cases
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
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegThreePositiveShore D c s
    let Xm := MuNegThreeNegativeShore D c s
    let Dp := D.comap (fun x : Xp ↦ x.1)
    let Dm := D.comap (fun x : Xm ↦ x.1)
    (∀ a : Dp.ConnectedComponent,
      a.supp.ncard = 3 ∨ a.supp.ncard = 4 ∨
        a.supp.ncard = 5 ∨ a.supp.ncard = 8) ∧
    ∀ a : Dm.ConnectedComponent,
      a.supp.ncard = 3 ∨ a.supp.ncard = 4 ∨
        a.supp.ncard = 5 ∨ a.supp.ncard = 8 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  let Dp := D.comap (fun x : Xp ↦ x.1)
  let Dm := D.comap (fun x : Xm ↦ x.1)
  have hfac := orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_twoFactors
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hDpdeg : ∀ x, Dp.degree x = 2 := by
    intro x
    rw [← Dp.card_neighborFinset_eq_degree]
    have heq : Dp.neighborFinset x =
        (Finset.univ : Finset Xp).filter (fun y ↦ D.Adj x.1 y.1) := by
      ext y
      simp [Dp]
    rw [heq]
    exact hfac.2.2.1 x
  have hDmdeg : ∀ x, Dm.degree x = 2 := by
    intro x
    rw [← Dm.card_neighborFinset_eq_degree]
    have heq : Dm.neighborFinset x =
        (Finset.univ : Finset Xm).filter (fun y ↦ D.Adj x.1 y.1) := by
      ext y
      simp [Dm]
    rw [heq]
    exact hfac.2.2.2 x
  constructor
  · intro a
    exact twoRegular_orderEight_component_size_cases
      Dp hfac.1 hDpdeg a
  · intro a
    exact twoRegular_orderEight_component_size_cases
      Dm hfac.2.1 hDmdeg a

/-- Both `mu=-3` same-sign defect factors satisfy the exact exhaustive
partition split `8`, `5+3`, or `4+4`. -/
theorem orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_partitions
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
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegThreePositiveShore D c s
    let Xm := MuNegThreeNegativeShore D c s
    let Dp := D.comap (fun x : Xp ↦ x.1)
    let Dm := D.comap (fun x : Xm ↦ x.1)
    MuNegThreeShoreCyclePartition Dp ∧
      MuNegThreeShoreCyclePartition Dm := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  let Dp := D.comap (fun x : Xp ↦ x.1)
  let Dm := D.comap (fun x : Xm ↦ x.1)
  have hfac := orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_twoFactors
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hDpdeg : ∀ x, Dp.degree x = 2 := by
    intro x
    rw [← Dp.card_neighborFinset_eq_degree]
    have heq : Dp.neighborFinset x =
        (Finset.univ : Finset Xp).filter (fun y ↦ D.Adj x.1 y.1) := by
      ext y
      simp [Dp]
    rw [heq]
    exact hfac.2.2.1 x
  have hDmdeg : ∀ x, Dm.degree x = 2 := by
    intro x
    rw [← Dm.card_neighborFinset_eq_degree]
    have heq : Dm.neighborFinset x =
        (Finset.univ : Finset Xm).filter (fun y ↦ D.Adj x.1 y.1) := by
      ext y
      simp [Dm]
    rw [heq]
    exact hfac.2.2.2 x
  change MuNegThreeShoreCyclePartition Dp ∧
    MuNegThreeShoreCyclePartition Dm
  constructor
  · simpa only [MuNegThreeShoreCyclePartition, Nat.card_eq_fintype_card] using
      (twoRegular_orderEight_component_partition Dp hfac.1 hDpdeg)
  · simpa only [MuNegThreeShoreCyclePartition, Nat.card_eq_fintype_card] using
      (twoRegular_orderEight_component_partition Dm hfac.2.1 hDmdeg)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_twoFactors
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_component_size_cases
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_partitions
