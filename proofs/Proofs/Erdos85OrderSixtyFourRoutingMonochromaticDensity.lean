import Proofs.Erdos85OrderSixtyFourRoutingMonochromaticTripleLowerBound

/-! # Monochromatic density in the order-64 routing design -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Summing the per-color bound over the four routing components gives at
least `512` monochromatic routed triples across any three pairwise distinct
endpoint components. Since there are `16³ = 4096` endpoint triples, this is
the routing design's one-eighth monochromatic-density constraint. -/
theorem orderSixtyFour_regular_fourComponents_routing_monochromaticTriple_count_ge
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (c e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f) :
    512 ≤ ∑ d : (secondOrderDefectGraph G).ConnectedComponent,
      ∑ x : c.supp, ∑ w : f.supp,
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
          d = crossIntermediateComponent G hfree hef z w).card := by
  calc
    512 = ∑ _d : (secondOrderDefectGraph G).ConnectedComponent, 128 := by
      simp [hcount]
    _ ≤ ∑ d : (secondOrderDefectGraph G).ConnectedComponent,
        ∑ x : c.supp, ∑ w : f.supp,
          ((Finset.univ : Finset e.supp).filter fun z =>
            d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card := by
      apply Finset.sum_le_sum
      intro d _hd
      exact
        orderSixtyFour_regular_fourComponents_routingColor_monochromaticTriple_count_ge
          G hfree hreg hcount c d e f hce hef hcf

end

end Erdos85
