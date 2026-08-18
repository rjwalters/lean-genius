import Proofs.Erdos85BinarySquareRoutingColorTwoLifts
import Proofs.Erdos85BinarySquareRoutingExcessRainbow

/-! # Routing multiplicity dichotomy on binary-square size-two parts -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every directly routed endpoint pair has exactly its two canonical
shared-center completions, unless the routing component contains a rainbow
triangle in the three endpoint owner colors. -/
theorem binarySquare_regular_sizeTwoRoutingColor_two_lifts_or_owner_rainbow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (he : e.supp.ncard = q * 2)
    (x : c.supp) (w : f.supp)
    (hroute : d = crossIntermediateComponent G hfree hcf x w) :
    ((Finset.univ : Finset e.supp).filter fun z =>
      d = crossIntermediateComponent G hfree hce x z ∧
        d = crossIntermediateComponent G hfree hef z w).card = 2 ∨
      ∃ y₁ y₂ y₃ : d.supp,
        y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁.1 y₂.1 ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂.1 y₃.1 ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃.1 y₁.1 := by
  let L := (Finset.univ : Finset e.supp).filter fun z =>
    d = crossIntermediateComponent G hfree hce x z ∧
      d = crossIntermediateComponent G hfree hef z w
  have htwo : 2 ≤ L.card := by
    exact binarySquare_regular_sizeTwoRoutingColor_two_le_lift_card
      G hfree hq hreg hcard c d e f hce hef hcf he x w hroute
  by_cases hthree : 3 ≤ L.card
  · right
    apply binarySquare_regular_sizeTwoRoutingColor_rainbow_of_three_le_lift_card
      G hfree hq hreg hcard hce hef hcf he x w hroute.symm
    simpa only [L, eq_comm] using hthree
  · left
    change L.card = 2
    omega

end

end Erdos85
