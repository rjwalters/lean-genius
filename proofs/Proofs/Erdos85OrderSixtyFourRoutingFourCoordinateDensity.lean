import Proofs.Erdos85OrderSixtyFourRoutingFourCoordinateMultiplicity

/-! # Global four-coordinate routing density at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Summed over all `16 * 16` endpoint pairs, two intermediate coordinates
provide at least `1024` same-color routing witnesses. -/
theorem orderSixtyFour_regular_fourComponents_fourCoordinate_lift_count_ge
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (c e f g : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (hcg : c ≠ g) (hgf : g ≠ f) :
    1024 ≤ ∑ x : c.supp, ∑ w : f.supp,
      (((Finset.univ : Finset e.supp).filter fun z =>
        crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hce x z ∧
          crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hef z w).card +
      ((Finset.univ : Finset g.supp).filter fun z =>
        crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hcg x z ∧
          crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hgf z w).card) := by
  have hsize := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hcCard : Fintype.card c.supp = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_coe_set_eq c.supp).trans (hsize c)
  have hfCard : Fintype.card f.supp = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_coe_set_eq f.supp).trans (hsize f)
  calc
    1024 = ∑ _x : c.supp, ∑ _w : f.supp, 4 := by
      simp [hcCard, hfCard]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x _hx
      apply Finset.sum_le_sum
      intro w _hw
      exact
        orderSixtyFour_regular_fourComponents_fourCoordinate_lift_count_ge_four
          G hfree hreg hcount c e f g hce hef hcf hcg hgf x w

end

end Erdos85
