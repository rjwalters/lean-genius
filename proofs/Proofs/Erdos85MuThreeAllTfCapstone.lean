import Proofs.Erdos85MuThreeAllTfShapeLabelingWrappers
import Proofs.Erdos85MuThreeAllTfActualShape

/-! # Closing the order-64 all-triangle-free mu=3 sector -/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

def signedSubtypeFlattenEquiv
    {V : Type*} (S : Set V) (s : V → ℤ) (a : ℤ) :
    {x : V // x ∈ S ∧ s x = a} ≃ {x : S // s x.1 = a} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv x := by rfl
  right_inv x := by rfl

def flattenSignedInternalCoordinateModel
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (s : V → ℤ) (shape : Mu3AllTfShape)
    (model : Mu3InternalCoordinateModel (G.induce S)
      {x : S // s x.1 = 1} {x : S // s x.1 = -1}
      Subtype.val Subtype.val shape) :
    Mu3InternalCoordinateModel (G.induce S)
      {x : V // x ∈ S ∧ s x = 1} {x : V // x ∈ S ∧ s x = -1}
      (fun p => ⟨p.1, p.2.1⟩) (fun n => ⟨n.1, n.2.1⟩) shape where
  row := (signedSubtypeFlattenEquiv S s 1).trans model.row
  column := (signedSubtypeFlattenEquiv S s (-1)).trans model.column
  hole_iff p n := model.hole_iff
    (signedSubtypeFlattenEquiv S s 1 p)
    (signedSubtypeFlattenEquiv S s (-1) n)

theorem false_of_orderSixtyFour_mu3_allTriangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
      s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2)
    (hallTf : ∀ p : {z : V // z ∈ c.supp ∧ s z = 1},
      ∀ n : {z : V // z ∈ c.supp ∧ s z = -1},
        G.Adj p.1 n.1 → (triangleFreeEdgeGraph G).Adj p.1 n.1) : False := by
  classical
  let H := G.induce c.supp
  let t : c.supp → ℤ := fun x => s x.1
  have hdeg : ∀ x, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcardV c hc x
  have hsign : ∀ x, t x = -1 ∨ t x = 1 := by
    intro x
    exact hs_in x.1 x.2
  have hneighborSum : ∀ x, ∑ y ∈ H.neighborFinset x, t y = -2 * t x := by
    intro x
    rw [← SimpleGraph.adjMatrix_mulVec_apply]
    rw [← adjMatrix_mulVec_eq_induce_mulVec_of_support_int
      G c.supp s hs_out x]
    exact hA_in x.1 x.2
  have hflip : ∀ ⦃x y⦄, H.Adj x y → t x = -t y :=
    signedFlip_of_degree_two_neighborSum H hdeg t hsign hneighborSum
  have hout := orderSixtyFour_sizeTwoComponent_outside_subtype_neighborCard_six
    G hfree hreg hcardV c hc
  have hP := orderSixtyFour_signedSizeTwo_positive_subtype_card
    G c hc s hs_in hs_out hsum
  have hN := orderSixtyFour_signedSizeTwo_negative_subtype_card
    G c hc s hs_in hs_out hsum
  obtain ⟨shape, rs, hrs, hsizes⟩ :=
    orderSixtyFour_signedSizeTwo_internal_mu3AllTfShape
      G hfree hreg hcardV c hc s hs_in hs_out hA_in
  cases shape with
  | c16 =>
      simp only at hrs
      subst rs
      let label : SixteenCycleLabeling H :=
        Classical.choice (exists_sixteenCycleLabeling_of_componentSizes
          H hdeg hsizes)
      let nested := sixteenInternalCoordinateModel H label t hsign hflip
      let model := flattenSignedInternalCoordinateModel G c.supp s .c16 nested
      exact false_of_orderSixtyFour_mu3AllTf_internalModel
        G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out
        .c16 model hout hP hN hallTf
  | c10c6 =>
      simp only at hrs
      subst rs
      let label : TenSixComponentLabeling H :=
        Classical.choice (exists_tenSixComponentLabeling_of_componentSizes
          H hdeg hsizes)
      let nested := tenSixInternalCoordinateModel H label t hsign hflip
      let model := flattenSignedInternalCoordinateModel G c.supp s .c10c6 nested
      exact false_of_orderSixtyFour_mu3AllTf_internalModel
        G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out
        .c10c6 model hout hP hN hallTf
  | c8c8 =>
      simp only at hrs
      subst rs
      let label : EightEightCycleLabeling H :=
        Classical.choice (exists_eightEightCycleLabeling_of_componentSizes
          H hdeg hsizes)
      let nested := eightEightInternalCoordinateModel H label t hsign hflip
      let model := flattenSignedInternalCoordinateModel G c.supp s .c8c8 nested
      exact false_of_orderSixtyFour_mu3AllTf_internalModel
        G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out
        .c8c8 model hout hP hN hallTf

#print axioms false_of_orderSixtyFour_mu3_allTriangleFree

end

end Erdos85
