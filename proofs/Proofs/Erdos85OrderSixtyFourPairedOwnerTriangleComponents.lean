import Proofs.Erdos85OrderSixtyFourFiveCrossComponentsOwnerTriangleCount
import Proofs.Erdos85BinarySquareSizeTwoPairedOwnerComponentEquiv

/-! # Canonical equivalence of paired owner triangle components -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The canonical equivalence between paired owner-factor components
restricts to an equivalence between their order-three (triangle) components. -/
def binarySquare_regular_twoSizeTwoParts_pairedOwnerTriangleComponentEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2) :
    {a : (restrictedComponentOwnerGraph G source target).ConnectedComponent //
      a.supp.ncard = 3} ≃
    {b : (restrictedComponentOwnerGraph G target source).ConnectedComponent //
      b.supp.ncard = 3} := by
  let P := binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv
    G hfree hq hreg hcard source target hsource htarget
  apply Equiv.subtypeEquiv P
  intro a
  have hsize :=
    binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv_supp_ncard
      G hfree hq hreg hcard source target hsource htarget a
  rw [hsize]

/-- With five cross components at order 64, the source owner factor has
exactly four triangle components. -/
theorem orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerTriangleComponent_card
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
    Fintype.card
      {a : (restrictedComponentOwnerGraph G source target).ConnectedComponent //
        a.supp.ncard = 3} = 4 := by
  rw [Fintype.card_subtype]
  exact
    orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerTriangleComponent_count
      G hfree hreg hcard source target hst hsource htarget hfive

/-- The target owner factor also has exactly four triangle components, and
the canonical restricted equivalence pairs them. -/
theorem orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_reverseOwnerTriangleComponent_card
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
    Fintype.card
      {b : (restrictedComponentOwnerGraph G target source).ConnectedComponent //
        b.supp.ncard = 3} = 4 := by
  rw [← orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerTriangleComponent_card
    G hfree hreg hcard source target hst hsource htarget hfive]
  exact Fintype.card_congr
    (binarySquare_regular_twoSizeTwoParts_pairedOwnerTriangleComponentEquiv
      G hfree (q := 8) (by omega) hreg (by omega) source target
        (by omega) (by omega)).symm

end

end Erdos85
