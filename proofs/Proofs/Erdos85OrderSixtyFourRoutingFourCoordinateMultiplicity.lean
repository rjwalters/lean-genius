import Proofs.Erdos85BinarySquareRoutingColorTwoLifts
import Proofs.Erdos85OrderSixtyFourRegularPartition

/-! # Four-coordinate monochromatic routing multiplicity at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the four-component order-64 branch, a directly routed endpoint pair
has at least two same-color lifts through each of two other endpoint
components.  Consequently the two intermediate coordinates provide at least
four monochromatic routing witnesses in total. -/
theorem orderSixtyFour_regular_fourComponents_fourCoordinate_lift_count_ge_four
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
    4 ≤
      ((Finset.univ : Finset e.supp).filter fun z =>
        crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hce x z ∧
          crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hef z w).card +
      ((Finset.univ : Finset g.supp).filter fun z =>
        crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hcg x z ∧
          crossIntermediateComponent G hfree hcf x w =
            crossIntermediateComponent G hfree hgf z w).card := by
  have hsize := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  calc
    4 = 2 + 2 := by norm_num
    _ ≤ _ := add_le_add
      (binarySquare_regular_sizeTwoRoutingColor_two_le_lift_card
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          c (crossIntermediateComponent G hfree hcf x w) e f hce hef hcf
          (by simpa using hsize e) x w rfl)
      (binarySquare_regular_sizeTwoRoutingColor_two_le_lift_card
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          c (crossIntermediateComponent G hfree hcf x w) g f hcg hgf hcf
          (by simpa using hsize g) x w rfl)

end

end Erdos85
