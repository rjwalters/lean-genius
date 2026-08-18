import Proofs.Erdos85MuThreeAllTfActualShape
import Proofs.Erdos85MuThreeAllTfShapeLabelingWrappers
import Proofs.Erdos85MuThreeAllTfSixteenCoordinates
import Proofs.Erdos85MuThreeAllTfEightEightCoordinates
import Proofs.Erdos85MuThreeAllTfTenSixCoordinates
import Proofs.Erdos85MuThreeAllTriangleKSymmetryEnumeration
import Proofs.Erdos85MuThreeKSymmetryCoordinateTransport
import Proofs.Erdos85OrderSixtyFourMuThreeMixedGridAssembly

/-!
# Coordinates for the order-64 signed internal two-factor

The all-triangle-free lane already classifies the internal ambient-adjacency
two-factor by its component sizes and constructs signed coordinates for each
of the three possible shapes.  This module exposes that result in the exact
normal-form disjunction required by the K-symmetry classification.
-/

namespace Erdos85

open SimpleGraph Matrix

noncomputable section

private def signedShapeSubtypeFlattenEquiv
    {V : Type*} (S : Set V) (s : V → ℤ) (a : ℤ) :
    {x : V // x ∈ S ∧ s x = a} ≃ {x : S // s x.1 = a} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def flattenSignedShapeCoordinateModel
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (s : V → ℤ) (shape : Mu3AllTfShape)
    (model : Mu3InternalCoordinateModel (G.induce S)
      {x : S // s x.1 = 1} {x : S // s x.1 = -1}
      Subtype.val Subtype.val shape) :
    Mu3InternalCoordinateModel (G.induce S)
      {x : V // x ∈ S ∧ s x = 1} {x : V // x ∈ S ∧ s x = -1}
      (fun p => ⟨p.1, p.2.1⟩) (fun n => ⟨n.1, n.2.1⟩) shape where
  row := (signedShapeSubtypeFlattenEquiv S s 1).trans model.row
  column := (signedShapeSubtypeFlattenEquiv S s (-1)).trans model.column
  hole_iff p n := model.hole_iff
    (signedShapeSubtypeFlattenEquiv S s 1 p)
    (signedShapeSubtypeFlattenEquiv S s (-1) n)

/-- The internal relation of a signed size-two `μ = 3` block has one of the
three coordinate forms used by the finite K-symmetry enumeration. -/
theorem orderSixtyFour_muThreeInternalRel_exists_nativeShapeCoordinates
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
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x) :
    (∃ (row : muThreePositiveShore c.supp s ≃ Fin 8)
        (column : muThreeNegativeShore c.supp s ≃ Fin 8),
      ∀ x y,
        mu3NormalizeRelation row column
          (orderSixtyFourMuThreeInternalRel G) x y ↔
        y.val ∈ mu3H16Row x.val) ∨
    (∃ (row : muThreePositiveShore c.supp s ≃ Fin 8)
        (column : muThreeNegativeShore c.supp s ≃ Fin 8),
      ∀ x y,
        mu3NormalizeRelation row column
          (orderSixtyFourMuThreeInternalRel G) x y ↔
        y.val ∈ mu3H88Row x.val) ∨
    (∃ (row : muThreePositiveShore c.supp s ≃ Fin 8)
        (column : muThreeNegativeShore c.supp s ≃ Fin 8),
      ∀ x y,
        mu3NormalizeRelation row column
          (orderSixtyFourMuThreeInternalRel G) x y ↔
        y.val ∈ mu3H106Row x.val) := by
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
  have hneighborSum : ∀ x,
      ∑ y ∈ H.neighborFinset x, t y = -2 * t x := by
    intro x
    rw [← SimpleGraph.adjMatrix_mulVec_apply]
    rw [← adjMatrix_mulVec_eq_induce_mulVec_of_support_int
      G c.supp s hs_out x]
    exact hA_in x.1 x.2
  have hflip : ∀ ⦃x y⦄, H.Adj x y → t x = -t y :=
    signedFlip_of_degree_two_neighborSum H hdeg t hsign hneighborSum
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
      let model := flattenSignedShapeCoordinateModel G c.supp s .c16 nested
      left
      refine ⟨model.row, model.column, ?_⟩
      intro x y
      simpa [mu3NormalizeRelation, orderSixtyFourMuThreeInternalRel,
        mu3H16Row, mu3AllTfInternal, Nat.mod_eq_of_lt x.isLt,
        Finset.mem_insert, Finset.mem_singleton] using
        model.hole_iff (model.row.symm x) (model.column.symm y)
  | c10c6 =>
      simp only at hrs
      subst rs
      let label : TenSixComponentLabeling H :=
        Classical.choice (exists_tenSixComponentLabeling_of_componentSizes
          H hdeg hsizes)
      let nested := tenSixInternalCoordinateModel H label t hsign hflip
      let model := flattenSignedShapeCoordinateModel G c.supp s .c10c6 nested
      right
      right
      refine ⟨model.row, model.column, ?_⟩
      intro x y
      by_cases hx : x.val < 5
      · simpa [mu3NormalizeRelation, orderSixtyFourMuThreeInternalRel,
          mu3H106Row, mu3AllTfInternal, hx,
          Finset.mem_insert, Finset.mem_singleton] using
          model.hole_iff (model.row.symm x) (model.column.symm y)
      · simpa [mu3NormalizeRelation, orderSixtyFourMuThreeInternalRel,
          mu3H106Row, mu3AllTfInternal, hx,
          Finset.mem_insert, Finset.mem_singleton] using
          model.hole_iff (model.row.symm x) (model.column.symm y)
  | c8c8 =>
      simp only at hrs
      subst rs
      let label : EightEightCycleLabeling H :=
        Classical.choice (exists_eightEightCycleLabeling_of_componentSizes
          H hdeg hsizes)
      let nested := eightEightInternalCoordinateModel H label t hsign hflip
      let model := flattenSignedShapeCoordinateModel G c.supp s .c8c8 nested
      right
      left
      refine ⟨model.row, model.column, ?_⟩
      intro x y
      by_cases hx : x.val < 4
      · simpa [mu3NormalizeRelation, orderSixtyFourMuThreeInternalRel,
          mu3H88Row, mu3AllTfInternal, hx,
          Finset.mem_insert, Finset.mem_singleton] using
          model.hole_iff (model.row.symm x) (model.column.symm y)
      · simpa [mu3NormalizeRelation, orderSixtyFourMuThreeInternalRel,
          mu3H88Row, mu3AllTfInternal, hx,
          Finset.mem_insert, Finset.mem_singleton] using
          model.hole_iff (model.row.symm x) (model.column.symm y)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_muThreeInternalRel_exists_nativeShapeCoordinates
