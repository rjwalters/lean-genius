import Proofs.Erdos85OrderSixtyFourRoutingLiftExcessDichotomy

/-! # Exact routing-lift rigidity at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the four-component order-64 branch, the absence of the owner-triangle
alternative makes both remaining-coordinate lift fibers individually equal to
their forced two-point baseline. -/
theorem orderSixtyFour_regular_fourComponents_routingLift_exact_two_or_ownerTriangle
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
    (hcg : c ≠ g) (hgf : g ≠ f)
    (x : c.supp) (w : f.supp) :
    ((((Finset.univ : Finset e.supp).filter fun z =>
          crossIntermediateComponent G hfree hcf x w =
              crossIntermediateComponent G hfree hce x z ∧
            crossIntermediateComponent G hfree hcf x w =
              crossIntermediateComponent G hfree hef z w).card = 2) ∧
      (((Finset.univ : Finset g.supp).filter fun z =>
          crossIntermediateComponent G hfree hcf x w =
              crossIntermediateComponent G hfree hcg x z ∧
            crossIntermediateComponent G hfree hcf x w =
              crossIntermediateComponent G hfree hgf z w).card = 2)) ∨
    ∃ p : (secondOrderDefectGraph G).ConnectedComponent,
      (p = e ∨ p = g) ∧
      ∃ y₁ y₂ y₃ : Fin 64,
        y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) p).Adj y₁ y₂ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂ y₃ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃ y₁ := by
  let A := (Finset.univ : Finset e.supp).filter fun z =>
    crossIntermediateComponent G hfree hcf x w =
        crossIntermediateComponent G hfree hce x z ∧
      crossIntermediateComponent G hfree hcf x w =
        crossIntermediateComponent G hfree hef z w
  let B := (Finset.univ : Finset g.supp).filter fun z =>
    crossIntermediateComponent G hfree hcf x w =
        crossIntermediateComponent G hfree hcg x z ∧
      crossIntermediateComponent G hfree hcf x w =
        crossIntermediateComponent G hfree hgf z w
  rcases orderSixtyFour_regular_fourComponents_routingLift_baseline_or_ownerTriangle
      G hfree hreg hcount c e f g hce hef hcf hcg hgf x w with hbase | htriangle
  · left
    have heCard : e.supp.ncard = 8 * 2 := by
      simpa using
        (orderSixtyFour_regular_four_defectComponents_all_orderSixteen
          G hfree hreg hcount e)
    have hgCard : g.supp.ncard = 8 * 2 := by
      simpa using
        (orderSixtyFour_regular_four_defectComponents_all_orderSixteen
          G hfree hreg hcount g)
    have hA : 2 ≤ A.card := by
      exact binarySquare_regular_sizeTwoRoutingColor_two_le_lift_card
        G hfree (q := 8) (by omega) hreg (by decide)
          c (crossIntermediateComponent G hfree hcf x w) e f
          hce hef hcf heCard x w rfl
    have hB : 2 ≤ B.card := by
      exact binarySquare_regular_sizeTwoRoutingColor_two_le_lift_card
        G hfree (q := 8) (by omega) hreg (by decide)
          c (crossIntermediateComponent G hfree hcf x w) g f
          hcg hgf hcf hgCard x w rfl
    have hsum : A.card + B.card = 4 := by
      simpa [A, B] using hbase
    have : A.card = 2 ∧ B.card = 2 := by omega
    simpa [A, B] using this
  · exact Or.inr htriangle

end

end Erdos85
