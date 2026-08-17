import Proofs.Erdos85OrderSixtyFourNoRainbowForcesRoutingRowSaturation
import Proofs.Erdos85BinarySquareRoutingRowStarDecomposition

/-! # Routing-row saturation is generic at order sixty-four -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Formal dead-end audit: in the four-component order-64 regime, every
routing row is saturated by its two canonical ambient star rows.  Thus bare
`routingRowSaturatedAt` carries no no-rainbow information. -/
theorem orderSixtyFour_regular_fourComponents_routingRowSaturatedAt
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {source middle : (secondOrderDefectGraph G).ConnectedComponent}
    (hsm : source ≠ middle)
    (route : (secondOrderDefectGraph G).ConnectedComponent)
    (x : source.supp) :
    routingRowSaturatedAt G hfree hsm route x := by
  classical
  let S := componentCrossNeighborFinset G route x
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hScard : S.card = 2 := by
    dsimp [S]
    rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    exact binarySquare_regular_sizeTwoPart_selector_card
      G hfree (q := 8) (by norm_num) hreg (by norm_num) route
        (by simpa using hall route) x.1
  obtain ⟨u₁, u₂, hu, hS⟩ := Finset.card_eq_two.mp hScard
  refine ⟨u₁, u₂, ?_⟩
  have hdecomp := routingRow_eq_biUnion_componentCrossNeighborFinset
    G hfree hsm route x
  rw [show componentCrossNeighborFinset G route x = S by rfl, hS] at hdecomp
  simpa [hu] using hdecomp.symm

end

end Erdos85
