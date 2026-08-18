import Proofs.Erdos85OrderSixtyFourRegularPartition
import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity
import Proofs.Erdos85BinarySquareCrossRoutingSymmetry

/-! # The four-color routing array at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A chosen indexing of the four defect components by `Fin 4`. -/
def orderSixtyFourDefectComponentEquivFinFour
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4) :
    (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 4 :=
  Fintype.equivFinOfCardEq hcount

/-- In the four-component branch, label the unique intermediate component of
an endpoint pair by `Fin 4`. -/
def orderSixtyFourRoutingArray
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) : c.supp → e.supp → Fin 4 :=
  fun x z => orderSixtyFourDefectComponentEquivFinFour G hcount
    (crossIntermediateComponent G hfree hce x z)

/-- Reversing the endpoints leaves the `Fin 4` routing color unchanged. -/
theorem orderSixtyFourRoutingArray_reverse
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) :
    orderSixtyFourRoutingArray G hfree hcount hce x z =
      orderSixtyFourRoutingArray G hfree hcount hce.symm z x := by
  simp [orderSixtyFourRoutingArray,
    crossIntermediateComponent_reverse G hfree hce x z]

/-- Every one of the four colors occurs exactly four times in each row of an
order-64 routing array. -/
theorem orderSixtyFourRoutingArray_row_color_card_eq_four
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (k : Fin 4) :
    ((Finset.univ : Finset e.supp).filter fun z =>
      orderSixtyFourRoutingArray G hfree hcount hce x z = k).card = 4 := by
  let E := orderSixtyFourDefectComponentEquivFinFour G hcount
  let d := E.symm k
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hroute :=
    binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
        c d e hce (by simpa using hall c) (by simpa using hall d)
          (by simpa using hall e) x
  convert hroute using 1
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    orderSixtyFourRoutingArray, E, d]
  change E (crossIntermediateComponent G hfree hce x z) = k ↔
    E.symm k = crossIntermediateComponent G hfree hce x z
  constructor
  · intro h
    exact E.injective (by simpa using h.symm)
  · intro h
    exact E.symm.injective (by simpa using h.symm)

/-- Every one of the four colors occurs exactly four times in each column of
an order-64 routing array. -/
theorem orderSixtyFourRoutingArray_column_color_card_eq_four
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (z : e.supp) (k : Fin 4) :
    ((Finset.univ : Finset c.supp).filter fun x =>
      orderSixtyFourRoutingArray G hfree hcount hce x z = k).card = 4 := by
  let E := orderSixtyFourDefectComponentEquivFinFour G hcount
  let d := E.symm k
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hroute :=
    binarySquare_regular_threeSizeTwoParts_routing_column_card_eq_four
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
        c d e hce (by simpa using hall c) (by simpa using hall d)
          (by simpa using hall e) z
  convert hroute using 1
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    orderSixtyFourRoutingArray, E, d]
  change E (crossIntermediateComponent G hfree hce x z) = k ↔
    E.symm k = crossIntermediateComponent G hfree hce x z
  constructor
  · intro h
    exact E.injective (by simpa using h.symm)
  · intro h
    exact E.symm.injective (by simpa using h.symm)

end

end Erdos85
