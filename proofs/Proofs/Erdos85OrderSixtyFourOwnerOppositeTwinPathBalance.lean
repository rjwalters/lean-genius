import Proofs.Erdos85TwoRegularOrderFourOppositeTwins
import Proofs.Erdos85BinarySquareSizeTwoCrossFactorPathBalance

/-! # Alternating-path balance from owner opposite twins -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Under the five-component profile, choose the opposite pair on the unique
owner four-cycle. Intertwining of the paired owner factors then says that,
for every target vertex, the number of cross-then-owner paths from either
opposite vertex is the same. -/
theorem orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_exists_ownerOppositeTwins_pathBalance
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
    ∃ x y : source.supp, x ≠ y ∧
      ¬ (restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).neighborFinset x =
        (restrictedComponentOwnerGraph G source target).neighborFinset y ∧
      ∀ z : target.supp,
        ((Finset.univ : Finset target.supp).filter fun u =>
          G.Adj x.1 u.1 ∧
            (restrictedComponentOwnerGraph G target source).Adj u z).card =
        ((Finset.univ : Finset target.supp).filter fun u =>
          G.Adj y.1 u.1 ∧
            (restrictedComponentOwnerGraph G target source).Adj u z).card := by
  classical
  obtain ⟨x, y, hxy, hnxy, hN⟩ :=
    orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_exists_ownerOppositeTwins
      G hfree hreg hcard source target hst hsource htarget hfive
  refine ⟨x, y, hxy, hnxy, hN, ?_⟩
  intro z
  have hxBalance :=
    binarySquare_regular_twoSizeTwoParts_alternatingPath_card_eq
      G hfree (q := 8) (by omega) hreg (by omega) source target
        (by omega) (by omega) x z
  have hyBalance :=
    binarySquare_regular_twoSizeTwoParts_alternatingPath_card_eq
      G hfree (q := 8) (by omega) hreg (by omega) source target
        (by omega) (by omega) y z
  rw [← hxBalance, ← hyBalance]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hAdj :
      (restrictedComponentOwnerGraph G source target).Adj x u ↔
        (restrictedComponentOwnerGraph G source target).Adj y u := by
    rw [← (restrictedComponentOwnerGraph G source target).mem_neighborFinset,
      ← (restrictedComponentOwnerGraph G source target).mem_neighborFinset, hN]
  exact and_congr hAdj Iff.rfl

end

end Erdos85
