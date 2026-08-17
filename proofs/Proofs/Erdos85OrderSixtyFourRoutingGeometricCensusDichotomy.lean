import Proofs.Erdos85RoutingOwnerRainbowChordlessHexagon

/-! # Geometric form of the order-64 routing census split -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The ambient six-vertex pattern forced by a distinct-color routing
rainbow, including the three nonedges forced by C4-freeness. -/
def routingRainbowHexagonPattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  ∃ (y₁ y₂ y₃ : d.supp) (a : e.supp) (b : f.supp) (g : c.supp),
    y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
    G.Adj y₁.1 a.1 ∧ G.Adj y₂.1 a.1 ∧
    G.Adj y₂.1 b.1 ∧ G.Adj y₃.1 b.1 ∧
    G.Adj y₃.1 g.1 ∧ G.Adj y₁.1 g.1 ∧
    ¬ G.Adj y₁.1 b.1 ∧ ¬ G.Adj y₂.1 g.1 ∧ ¬ G.Adj y₃.1 a.1

/-- At order 64, the four-component routing census has a fully graph-facing
split: either a forbidden-diagonal rainbow hexagon occurs, or all direct
routing lift multiplicities are exactly two. -/
theorem orderSixtyFour_regular_fourComponents_hexagon_or_all_direct_two_lifts
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4) :
    (∃ c d e f : (secondOrderDefectGraph G).ConnectedComponent,
      c ≠ e ∧ e ≠ f ∧ c ≠ f ∧ routingRainbowHexagonPattern G d e f c) ∨
    (∀ c d e f : (secondOrderDefectGraph G).ConnectedComponent,
      ∀ (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f),
      ∀ (x : c.supp) (w : f.supp),
        d = crossIntermediateComponent G hfree hcf x w →
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card = 2) := by
  rcases orderSixtyFour_regular_fourComponents_rainbow_or_all_direct_two_lifts
    G hfree hreg hcount with hrainbow | hall
  · left
    obtain ⟨c, d, e, f, hce, hef, hcf, hr⟩ := hrainbow
    refine ⟨c, d, e, f, hce, hef, hcf, ?_⟩
    exact routingOwnerRainbow_exists_ambient_hexagon_forbidden_shortDiagonals
      G hfree d e f c hef hcf.symm hce hr
  · exact Or.inr hall

end

end Erdos85
