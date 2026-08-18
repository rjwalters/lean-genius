import Proofs.Erdos85OrderSixtyFourRoutingMonochromaticTriangleMultiplicity
import Proofs.Erdos85OrderSixtyFourFourComponentRoutingArray
import Proofs.Erdos85OrderSixtyFourRegularPartition
import Proofs.Erdos85BinarySquareRoutingCompletionDichotomy

/-! # Exact star core and rainbow excess at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Monochromatic completions of a fixed endpoint pair through a third
component. -/
def orderSixtyFourRoutingCompletionFinset
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f)
    (k : Fin 4) (x : c.supp) (w : f.supp) : Finset e.supp :=
  Finset.univ.filter fun z =>
    orderSixtyFourRoutingArray G hfree hcount hce x z = k ∧
      orderSixtyFourRoutingArray G hfree hcount hef z w = k

/-- The rainbow-excess completions are those whose three canonical common
neighbors are pairwise distinct. -/
def orderSixtyFourRoutingRainbowExcessFinset
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (k : Fin 4) (x : c.supp) (w : f.supp) : Finset e.supp :=
  (orderSixtyFourRoutingCompletionFinset
    G hfree hcount hce hef k x w).filter fun z =>
      crossCommonNeighbor G hfree hce x z ≠
          crossCommonNeighbor G hfree hef z w ∧
        crossCommonNeighbor G hfree hef z w ≠
          crossCommonNeighbor G hfree hcf x w ∧
        crossCommonNeighbor G hfree hcf x w ≠
          crossCommonNeighbor G hfree hce x z

private theorem routingStarFinset_card_eq_two
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
    (hcf : c ≠ f) (x : c.supp) (w : f.supp) :
    ((Finset.univ : Finset e.supp).filter fun z =>
      G.Adj z.1 (crossCommonNeighbor G hfree hcf x w)).card = 2 := by
  let d := crossIntermediateComponent G hfree hcf x w
  have hymem := crossCommonNeighbor_mem_intermediate G hfree hcf x w
  let y : d.supp := ⟨crossCommonNeighbor G hfree hcf x w, hymem⟩
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hcard : (componentCrossNeighborFinset G e y).card = 2 := by
    rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    exact binarySquare_regular_sizeTwoPart_selector_card
      G hfree (q := 8) (by norm_num) hreg (by norm_num) e
        (by simpa using hall e) y.1
  rw [← hcard]
  congr 1
  ext z
  simp [componentCrossNeighborFinset, y, adj_comm]

/-- Exact completion accounting: the completion set is the disjoint union of
the canonical two-element star core and the rainbow-excess set. -/
theorem orderSixtyFourRoutingCompletion_card_eq_two_add_rainbowExcess_card
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
    (orderSixtyFourRoutingCompletionFinset
        G hfree hcount hce hef k x w).card =
      2 + (orderSixtyFourRoutingRainbowExcessFinset
        G hfree hcount hce hef hcf k x w).card := by
  let C := orderSixtyFourRoutingCompletionFinset
    G hfree hcount hce hef k x w
  let S : e.supp → Prop := fun z =>
    G.Adj z.1 (crossCommonNeighbor G hfree hcf x w)
  let R : e.supp → Prop := fun z =>
    crossCommonNeighbor G hfree hce x z ≠
        crossCommonNeighbor G hfree hef z w ∧
      crossCommonNeighbor G hfree hef z w ≠
        crossCommonNeighbor G hfree hcf x w ∧
      crossCommonNeighbor G hfree hcf x w ≠
        crossCommonNeighbor G hfree hce x z
  have hstarSubset : ∀ z : e.supp, S z → z ∈ C := by
    intro z hz
    have hr₁ := crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
      G hfree hce x z
        ⟨(crossCommonNeighbor_spec G hfree hcf x w).1, hz⟩
    have hr₂ := crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
      G hfree hef z w
        ⟨hz, (crossCommonNeighbor_spec G hfree hcf x w).2⟩
    have hr₃ := crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
      G hfree hcf x w (crossCommonNeighbor_spec G hfree hcf x w)
    simp only [C, orderSixtyFourRoutingCompletionFinset,
      Finset.mem_filter, Finset.mem_univ, true_and,
      orderSixtyFourRoutingArray]
    constructor
    · rw [hr₁, ← hr₃]
      exact hxw
    · rw [hr₂, ← hr₃]
      exact hxw
  have hnotStar_iff_rainbow : ∀ z ∈ C, ¬ S z ↔ R z := by
    intro z hz
    have hzdata :
        orderSixtyFourRoutingArray G hfree hcount hce x z = k ∧
          orderSixtyFourRoutingArray G hfree hcount hef z w = k := by
      exact (Finset.mem_filter.mp hz).2
    let E := orderSixtyFourDefectComponentEquivFinFour G hcount
    let d := crossIntermediateComponent G hfree hcf x w
    have h₁ : crossIntermediateComponent G hfree hce x z = d := by
      apply E.injective
      simpa [E, d, orderSixtyFourRoutingArray] using hzdata.1.trans hxw.symm
    have h₂ : crossIntermediateComponent G hfree hef z w = d := by
      apply E.injective
      simpa [E, d, orderSixtyFourRoutingArray] using hzdata.2.trans hxw.symm
    have hcases := monochromatic_routing_completion_star_or_rainbow
      G hfree hce hef hcf x z w h₁ h₂ rfl
    constructor
    · intro hnS
      rcases hcases with hstar | hrainbow
      · exact False.elim (hnS hstar.1)
      · exact ⟨hrainbow.1, hrainbow.2.1, hrainbow.2.2.1⟩
    · intro hR hS
      exact (monochromatic_routing_completion_not_star_and_rainbow
        G hfree hce hef hcf x z w hS) hR
  have hsplit := Finset.card_filter_add_card_filter_not (s := C) S
  have hstarEq : C.filter S =
      (Finset.univ : Finset e.supp).filter S := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hstarSubset z h, h⟩⟩
  have hrainbowEq : C.filter (fun z => ¬ S z) = C.filter R := by
    apply Finset.filter_congr
    intro z hz
    exact hnotStar_iff_rainbow z hz
  rw [hstarEq, routingStarFinset_card_eq_two
    G hfree hreg hcount hcf x w, hrainbowEq] at hsplit
  simpa [C, R, orderSixtyFourRoutingRainbowExcessFinset] using hsplit.symm

/-- At most two rainbow completions remain after removing the forced star
core. -/
theorem orderSixtyFourRoutingRainbowExcess_card_le_two
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
    (orderSixtyFourRoutingRainbowExcessFinset
      G hfree hcount hce hef hcf k x w).card ≤ 2 := by
  have htotal := orderSixtyFourRoutingArray_monochromatic_triangle_card_le_four
    G hfree hreg hcount hce hef k x w
  have hsplit :=
    orderSixtyFourRoutingCompletion_card_eq_two_add_rainbowExcess_card
      G hfree hreg hcount hce hef hcf k x w hxw
  change (orderSixtyFourRoutingCompletionFinset
    G hfree hcount hce hef k x w).card ≤ 4 at htotal
  omega

end

end Erdos85
