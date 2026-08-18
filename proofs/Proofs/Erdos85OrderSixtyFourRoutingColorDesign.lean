import Proofs.Erdos85OrderSixtyFourRegularPartition
import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity
import Proofs.Erdos85BinarySquareCrossRoutingSymmetry

/-! # Balanced routing-color designs at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the four-component regular order-64 branch, routing through the four
defect components gives every ordered cross-component endpoint grid a
balanced four-color design: each cell has a unique routing color and every
color occurs exactly four times in every row and every column. Endpoint
reversal preserves the color. -/
theorem orderSixtyFour_regular_fourComponents_routingColorDesign
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4) :
    ∀ (source target : (secondOrderDefectGraph G).ConnectedComponent)
      (hst : source ≠ target),
      (∀ (x : source.supp)
          (d : (secondOrderDefectGraph G).ConnectedComponent),
        ((Finset.univ : Finset target.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hst x z).card = 4) ∧
      (∀ (z : target.supp)
          (d : (secondOrderDefectGraph G).ConnectedComponent),
        ((Finset.univ : Finset source.supp).filter fun x =>
          d = crossIntermediateComponent G hfree hst x z).card = 4) ∧
      (∀ (x : source.supp) (z : target.supp),
        ∃! d : (secondOrderDefectGraph G).ConnectedComponent,
          d = crossIntermediateComponent G hfree hst x z) ∧
      (∀ (x : source.supp) (z : target.supp),
        crossIntermediateComponent G hfree hst x z =
          crossIntermediateComponent G hfree hst.symm z x) := by
  intro source target hst
  have hsize := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x d
    exact binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
      G hfree (q := 8) (by omega) hreg (by norm_num) source d target hst
        (by simpa using hsize source) (by simpa using hsize d)
        (by simpa using hsize target) x
  · intro z d
    exact binarySquare_regular_threeSizeTwoParts_routing_column_card_eq_four
      G hfree (q := 8) (by omega) hreg (by norm_num) source d target hst
        (by simpa using hsize source) (by simpa using hsize d)
        (by simpa using hsize target) z
  · intro x z
    refine ⟨crossIntermediateComponent G hfree hst x z, rfl, ?_⟩
    intro d hd
    exact hd
  · intro x z
    exact crossIntermediateComponent_reverse G hfree hst x z

end

end Erdos85
