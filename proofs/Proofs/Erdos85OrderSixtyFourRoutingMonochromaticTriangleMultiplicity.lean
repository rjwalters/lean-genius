import Proofs.Erdos85OrderSixtyFourFourComponentRoutingMatrices
import Proofs.Erdos85BinarySquareRoutingColorComposition

/-! # Monochromatic triangle multiplicity in the order-64 routing design -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem routingMatrix_comp_apply_eq_card
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (k : Fin 4)
    (x : c.supp) (w : f.supp) :
    (orderSixtyFourRoutingMatrix G hfree hcount hce k *
        orderSixtyFourRoutingMatrix G hfree hcount hef k) x w =
      (((Finset.univ : Finset e.supp).filter fun z =>
        orderSixtyFourRoutingArray G hfree hcount hce x z = k ∧
          orderSixtyFourRoutingArray G hfree hcount hef z w = k).card : ℤ) := by
  rw [Matrix.mul_apply]
  simp_rw [orderSixtyFourRoutingMatrix_apply]
  calc
    (∑ z : e.supp,
      (if orderSixtyFourRoutingArray G hfree hcount hce x z = k
        then (1 : ℤ) else 0) *
      (if orderSixtyFourRoutingArray G hfree hcount hef z w = k
        then (1 : ℤ) else 0)) =
        ∑ z : e.supp,
          if orderSixtyFourRoutingArray G hfree hcount hce x z = k ∧
              orderSixtyFourRoutingArray G hfree hcount hef z w = k
          then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases h₁ : orderSixtyFourRoutingArray G hfree hcount hce x z = k <;>
        by_cases h₂ : orderSixtyFourRoutingArray G hfree hcount hef z w = k <;>
          simp [h₁, h₂]
    _ = _ := by rw [Finset.sum_boole]

/-- Through a fixed third component, at most four intermediate vertices can
complete a prescribed monochromatic routing triangle. -/
theorem orderSixtyFourRoutingArray_monochromatic_triangle_card_le_four
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f)
    (k : Fin 4) (x : c.supp) (w : f.supp) :
    ((Finset.univ : Finset e.supp).filter fun z =>
      orderSixtyFourRoutingArray G hfree hcount hce x z = k ∧
        orderSixtyFourRoutingArray G hfree hcount hef z w = k).card ≤ 4 := by
  calc
    ((Finset.univ : Finset e.supp).filter fun z =>
        orderSixtyFourRoutingArray G hfree hcount hce x z = k ∧
          orderSixtyFourRoutingArray G hfree hcount hef z w = k).card ≤
        ((Finset.univ : Finset e.supp).filter fun z =>
          orderSixtyFourRoutingArray G hfree hcount hce x z = k).card := by
      apply Finset.card_le_card
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.1
    _ = 4 := orderSixtyFourRoutingArray_row_color_card_eq_four
      G hfree hreg hcount hce x k

/-- Every routing edge of color `k` extends through any third defect component
to at least two monochromatic routing triangles of the same color. -/
theorem orderSixtyFourRoutingArray_monochromatic_triangle_card_ge_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (k : Fin 4) (x : c.supp) (w : f.supp)
    (hxw : orderSixtyFourRoutingArray G hfree hcount hcf x w = k) :
    2 ≤ ((Finset.univ : Finset e.supp).filter fun z =>
      orderSixtyFourRoutingArray G hfree hcount hce x z = k ∧
        orderSixtyFourRoutingArray G hfree hcount hef z w = k).card := by
  let E := orderSixtyFourDefectComponentEquivFinFour G hcount
  let d := E.symm k
  let Bdc := defectComponentCrossIncidenceMatrix (K := ℤ) G d c
  let Bdf := defectComponentCrossIncidenceMatrix (K := ℤ) G d f
  let A := (restrictedComponentOwnerGraph G d e).adjMatrix ℤ
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hcomp := binarySquare_regular_sizeTwoRoutingColor_comp
    G hfree (q := 8) (by norm_num) hreg (by norm_num)
      c d e f hce hef hcf (by simpa using hall e)
  have happ := congrArg (fun M : Matrix c.supp f.supp ℤ => M x w) hcomp
  have hcorr : 0 ≤ (Bdc.transpose * A * Bdf) x w := by
    simp only [Bdc, Bdf, A, Matrix.mul_apply, Matrix.transpose_apply,
      defectComponentCrossIncidenceMatrix,
      defectComponentNeighborIncidenceMatrix, SimpleGraph.adjMatrix_apply]
    positivity
  have hdirect :
      crossRoutingColorMatrix (K := ℤ) G hfree hcf d x w = 1 := by
    rw [show crossRoutingColorMatrix (K := ℤ) G hfree hcf d =
      orderSixtyFourRoutingMatrix G hfree hcount hcf k by rfl]
    rw [orderSixtyFourRoutingMatrix_apply, if_pos hxw]
  change
    (orderSixtyFourRoutingMatrix G hfree hcount hce k *
      orderSixtyFourRoutingMatrix G hfree hcount hef k) x w = _ at happ
  rw [routingMatrix_comp_apply_eq_card G hfree hcount hce hef k x w] at happ
  change
    (((Finset.univ : Finset e.supp).filter fun z =>
      orderSixtyFourRoutingArray G hfree hcount hce x z = k ∧
        orderSixtyFourRoutingArray G hfree hcount hef z w = k).card : ℤ) = _
    at happ
  rw [Matrix.add_apply, Matrix.smul_apply, hdirect] at happ
  change _ = 2 + (Bdc.transpose * A * Bdf) x w at happ
  have hcardZ :
      (2 : ℤ) ≤ (((Finset.univ : Finset e.supp).filter fun z =>
        orderSixtyFourRoutingArray G hfree hcount hce x z = k ∧
          orderSixtyFourRoutingArray G hfree hcount hef z w = k).card : ℤ) := by
    omega
  exact_mod_cast hcardZ

end

end Erdos85
