import Proofs.Erdos85OrderSixtyFourRoutingMonochromaticDensity

/-! # Routing-label agreement density at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem sum_eq_card_routing_agreement
    {C Z : Type*} [Fintype C] [DecidableEq C]
    [Fintype Z] [DecidableEq Z] (a b : Z → C) :
    (∑ d : C, ((Finset.univ : Finset Z).filter fun z =>
      d = a z ∧ d = b z).card) =
      ((Finset.univ : Finset Z).filter fun z => a z = b z).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases h : a z = b z
  · simp [h]
  · simp [h]

/-- Across any three distinct components in the four-component order-64
branch, at least `512` of the `16^3 = 4096` endpoint triples have equal
routing labels on their two consecutive legs. -/
theorem orderSixtyFour_regular_fourComponents_routingAgreement_count_ge
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
    512 ≤ ∑ x : c.supp, ∑ w : f.supp,
      ((Finset.univ : Finset e.supp).filter fun z =>
        crossIntermediateComponent G hfree hce x z =
          crossIntermediateComponent G hfree hef z w).card := by
  have hmono :=
    orderSixtyFour_regular_fourComponents_routing_monochromaticTriple_count_ge
      G hfree hreg hcount c e f hce hef hcf
  calc
    512 ≤ ∑ d : (secondOrderDefectGraph G).ConnectedComponent,
        ∑ x : c.supp, ∑ w : f.supp,
          ((Finset.univ : Finset e.supp).filter fun z =>
            d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card := hmono
    _ = ∑ x : c.supp, ∑ d : (secondOrderDefectGraph G).ConnectedComponent,
        ∑ w : f.supp,
          ((Finset.univ : Finset e.supp).filter fun z =>
            d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card :=
      Finset.sum_comm
    _ = ∑ x : c.supp, ∑ w : f.supp,
        ∑ d : (secondOrderDefectGraph G).ConnectedComponent,
          ((Finset.univ : Finset e.supp).filter fun z =>
            d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro w _hw
      exact sum_eq_card_routing_agreement
        (fun z : e.supp => crossIntermediateComponent G hfree hce x z)
        (fun z : e.supp => crossIntermediateComponent G hfree hef z w)

end

end Erdos85
