import Proofs.Erdos85OrderSixtyFourFiveCrossComponentsOwnerProfile
import Proofs.Erdos85OrderSixtyFourCrossBipartiteCycleCount

/-! # Two owner four-cycles lower the cross-component count -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If a restricted owner factor on an order-sixteen defect component has
two distinct order-four connected components, then its paired cross graph
has at most four components.  Indeed every cross block has at most five
components, while the five-component profile has a unique owner four-cycle.

This is the graph-facing count consequence of the disjoint branch for two
propagated equal-row pairs in the order-64 `λ = 6` escape. -/
theorem orderSixtyFour_twoOwnerFourCycles_crossComponent_count_le_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hst : source ≠ target)
    (hsource : source.supp.ncard = 16)
    (htarget : target.supp.ncard = 16)
    (a b : (restrictedComponentOwnerGraph G source target).ConnectedComponent)
    (hab : a ≠ b) (ha4 : a.supp.ncard = 4) (hb4 : b.supp.ncard = 4) :
    Fintype.card
      (componentCrossBipartiteGraph G source target).ConnectedComponent ≤ 4 := by
  have hle5 :=
    orderSixtyFour_twoSizeTwoParts_crossBipartiteComponent_count_le_five
      G hfree hreg hcard source target hst hsource htarget
  by_contra hle4
  have hfive : Fintype.card
      (componentCrossBipartiteGraph G source target).ConnectedComponent = 5 := by
    omega
  obtain ⟨⟨c, hc4, hcUnique⟩, _hshape⟩ :=
    orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerProfile
      G hfree hreg hcard source target hst hsource htarget hfive
  have hac : a = c := hcUnique a ha4
  have hbc : b = c := hcUnique b hb4
  exact hab (hac.trans hbc.symm)

end

end Erdos85
