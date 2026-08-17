import Proofs.Erdos85BinarySquareRoutingGlobalDichotomy
import Proofs.Erdos85OrderSixtyFourRegularPartition

/-! # Global routing census dichotomy at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A triangle inside routing component `d` whose three edges carry the
three indicated endpoint owner colors. -/
def routingOwnerRainbow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  ∃ y₁ y₂ y₃ : d.supp,
    y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
    (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁.1 y₂.1 ∧
    (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂.1 y₃.1 ∧
    (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃.1 y₁.1

/-- The entire four-component order-64 routing census splits cleanly. Either
some ordered component quadruple supports an owner-color rainbow triangle,
or every directly routed endpoint pair, for every choice of intermediate
component, has exactly two monochromatic lifts. -/
theorem orderSixtyFour_regular_fourComponents_rainbow_or_all_direct_two_lifts
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
      c ≠ e ∧ e ≠ f ∧ c ≠ f ∧ routingOwnerRainbow G d e f c) ∨
    (∀ c d e f : (secondOrderDefectGraph G).ConnectedComponent,
      ∀ (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f),
      ∀ (x : c.supp) (w : f.supp),
        d = crossIntermediateComponent G hfree hcf x w →
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card = 2) := by
  classical
  have hsize := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  by_cases hrainbow : ∃ c d e f :
      (secondOrderDefectGraph G).ConnectedComponent,
      c ≠ e ∧ e ≠ f ∧ c ≠ f ∧ routingOwnerRainbow G d e f c
  · exact Or.inl hrainbow
  · right
    intro c d e f hce hef hcf x w hroute
    rcases binarySquare_regular_sizeTwoRoutingColor_rainbow_or_all_two_lifts
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
        c d e f hce hef hcf (by simpa using hsize e) with hr | hall
    · exact False.elim (hrainbow ⟨c, d, e, f, hce, hef, hcf, hr⟩)
    · exact hall x w hroute

end

end Erdos85
