import Proofs.Erdos85BinarySquareRoutingNoncentralLiftOwnerTriangle
import Proofs.Erdos85OrderSixtyFourRoutingFourCoordinateMultiplicity

/-! # Baseline-or-owner-triangle routing dichotomy at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For each direct endpoint pair in the four-component order-64 branch, the
two remaining endpoint coordinates either provide exactly the four central
lifts, or an excess lift forces a rainbow owner triangle. -/
theorem orderSixtyFour_regular_fourComponents_routingLift_baseline_or_ownerTriangle
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
    (((Finset.univ : Finset e.supp).filter fun z =>
        crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hce x z ∧
          crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hef z w).card +
      ((Finset.univ : Finset g.supp).filter fun z =>
        crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hcg x z ∧
          crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hgf z w).card = 4) ∨
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
  have hfour : 4 ≤ A.card + B.card := by
    exact orderSixtyFour_regular_fourComponents_fourCoordinate_lift_count_ge_four
      G hfree hreg hcount c e f g hce hef hcf hcg hgf x w
  by_cases hbase : A.card + B.card = 4
  · exact Or.inl hbase
  · right
    have hexcess : 5 ≤ A.card + B.card := by omega
    have hlarge : 3 ≤ A.card ∨ 3 ≤ B.card := by omega
    rcases hlarge with hA | hB
    · obtain ⟨y₁, y₂, y₃, h12, h23, h31, hoE, hoF, hoC⟩ :=
        three_le_monochromatic_routing_lift_card_exists_rainbow_ownerTriangle
          G hfree (q := 8) (by omega) hreg (by decide)
            hce hef hcf (by
              simpa using
                (orderSixtyFour_regular_four_defectComponents_all_orderSixteen
                  G hfree hreg hcount e)) x w (by simpa [A] using hA)
      exact ⟨e, Or.inl rfl, y₁, y₂, y₃,
        h12, h23, h31, hoE, hoF, hoC⟩
    · obtain ⟨y₁, y₂, y₃, h12, h23, h31, hoG, hoF, hoC⟩ :=
        three_le_monochromatic_routing_lift_card_exists_rainbow_ownerTriangle
          G hfree (q := 8) (by omega) hreg (by decide)
            hcg hgf hcf (by
              simpa using
                (orderSixtyFour_regular_four_defectComponents_all_orderSixteen
                  G hfree hreg hcount g)) x w (by simpa [B] using hB)
      exact ⟨g, Or.inr rfl, y₁, y₂, y₃,
        h12, h23, h31, hoG, hoF, hoC⟩

end

end Erdos85
