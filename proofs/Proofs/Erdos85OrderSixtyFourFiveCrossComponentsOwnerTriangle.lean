import Proofs.Erdos85OrderSixtyFourCrossBipartiteFiveProfile
import Proofs.Erdos85BinarySquareSizeTwoOwnerTriangleIffCrossSixComponent

/-! # Five cross components force an owner triangle at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If a cross block between distinct normalized size-two components has
five connected components, its restricted owner factor contains a triangle. -/
theorem orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_exists_ownerTriangle
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
    (hfive : Fintype.card
      (componentCrossBipartiteGraph G source target).ConnectedComponent = 5) :
    ∃ x y z : source.supp,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      (restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).Adj y z ∧
      (restrictedComponentOwnerGraph G source target).Adj z x := by
  classical
  apply
    (binarySquare_regular_twoSizeTwoParts_ownerTriangle_iff_exists_crossComponent_order_six
      G hfree (q := 8) (by omega) hreg (by omega) source target
        (by omega) (by omega)).mpr
  obtain ⟨hone, hshape⟩ :=
    orderSixtyFour_twoSizeTwoParts_crossBipartite_fiveComponent_profile
      G hfree hreg hcard source target hst hsource htarget hfive
  by_contra hn
  simp only [not_exists] at hn
  have hall8 : ∀ e : (componentCrossBipartiteGraph G source target).ConnectedComponent,
      e.supp.ncard = 8 := by
    intro e
    exact (hshape e).resolve_left (hn e)
  have hfilter :
      Finset.univ.filter (fun e :
        (componentCrossBipartiteGraph G source target).ConnectedComponent =>
          e.supp.ncard = 8) = Finset.univ := by
    exact Finset.filter_eq_self.mpr (fun e _ => hall8 e)
  rw [hfilter, Finset.card_univ, hfive] at hone
  omega

end

end Erdos85
