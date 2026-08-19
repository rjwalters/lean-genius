import Proofs.Erdos85SizeTwoMuNegThreeInternalStructure

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

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_twoFactors
