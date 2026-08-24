import Proofs.Erdos85OddSquareOrderNineOrder18ArticulationCapstone
import Proofs.Erdos85OddSquareOrderNineOrder27PuncturedTransfer

/-!
# Connectivity after deleting the order-nine second-profile owner

This module combines the complete order-18, order-27, and order-34
articulation eliminations with the deleted-owner shore classifier.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the three-high second profile, deleting the unique incidence-three
owner leaves the ordinary second-order defect graph connected. -/
theorem squareOrderNine_threeHigh_secondProfile_deleted_owner_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hOcard : ((Finset.univ : Finset V) \
      squareOrderHighVertices G 9).card = 78)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅)
    (hfullConnected : ((secondOrderDefectGraph G).induce
      (↑((Finset.univ : Finset V) \
        squareOrderHighVertices G 9) : Set V)).Connected) :
    ((secondOrderDefectGraph G).induce
      (↑(((Finset.univ : Finset V) \
        squareOrderHighVertices G 9).erase owner) : Set V)).Connected := by
  classical
  by_contra hnot
  obtain ⟨S, T, hunion, hdisj, horders, _hbeta, hfull,
      hSclosed, hTclosed, hSboundary, hTboundary⟩ :=
    squareOrderNine_threeHigh_secondProfile_deleted_owner_order_pairs_of_not_connected
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
        h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner hOcard
        hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
        hfullConnected hnot
  rcases horders with h18 | h59 | h27 | h50 | h34 | h43
  · exact false_of_orderNine_order18_unordered_articulation_output
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
        h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner S T hunion hdisj
        (Or.inl h18) hfull hSclosed hTclosed hSboundary hTboundary
        hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
  · exact false_of_orderNine_order18_unordered_articulation_output
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
        h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner S T hunion hdisj
        (Or.inr h59) hfull hSclosed hTclosed hSboundary hTboundary
        hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
  · exact false_of_orderNine_order27_unordered_articulation_output
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
        h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner S T hunion hdisj
        (Or.inl h27) hfull hSclosed hTclosed hSboundary hTboundary
        hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
  · exact false_of_orderNine_order27_unordered_articulation_output
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
        h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner S T hunion hdisj
        (Or.inr h50) hfull hSclosed hTclosed hSboundary hTboundary
        hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
  · exact false_of_orderNine_order34_unordered_articulation_output
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
        h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner S T hunion hdisj
        (Or.inl h34) hfull hSclosed hTclosed hSboundary hTboundary
        hdegOrd hdegHigh hdefectHighIsolated
  · exact false_of_orderNine_order34_unordered_articulation_output
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
        h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner S T hunion hdisj
        (Or.inr h43) hfull hSclosed hTclosed hSboundary hTboundary
        hdegOrd hdegHigh hdefectHighIsolated

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_deleted_owner_connected

end

end Erdos85
