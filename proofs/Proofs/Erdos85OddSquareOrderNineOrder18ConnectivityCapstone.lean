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

/-- Actual-profile form of deleted-owner connectivity.  The high-root
enumeration, degree data, isolation, and unpunctured connectivity are all
derived from the standard second-profile hypotheses. -/
theorem squareOrderNine_threeHigh_secondProfile_deleted_owner_connected_of_profile
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
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3) :
    ((secondOrderDefectGraph G).induce
      (↑(((Finset.univ : Finset V) \
        squareOrderHighVertices G 9).erase owner) : Set V)).Connected := by
  classical
  let H := squareOrderHighVertices G 9
  let D := secondOrderDefectGraph G
  obtain ⟨h₁, h₂, h₃, h₁₂, h₁₃, h₂₃, hH⟩ := Finset.card_eq_three.mp hhigh
  have hOcard : ((Finset.univ : Finset V) \
      squareOrderHighVertices G 9).card = 78 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ H),
      Finset.card_univ, hcard]
    change H.card = 3 at hhigh
    omega
  have hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9 := by
    intro x hx
    have hxH : x ∉ H := by simpa [H, hH] using hx
    rcases hp.degree_dichotomy x with hlo | hhi
    · exact hlo
    · exact (hxH (Finset.mem_filter.mpr
        ⟨Finset.mem_univ x, by norm_num at hhi ⊢; exact hhi⟩)).elim
  have hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10 := by
    intro h hh
    have hhH : h ∈ H := by simpa [H, hH] using hh
    have hd := (Finset.mem_filter.mp hhH).2
    norm_num at hd ⊢
    exact hd
  have hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V) := by
    intro h hh
    rw [Finset.disjoint_left]
    intro y hyN hy
    have hhH : h ∈ H := by simpa [H, hH] using hh
    have hyH : y ∈ H := by simpa [H, hH] using hy
    exact hp.high_independent hhH hyH
      ((G.mem_neighborFinset h y).mp hyN)
  have hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      D.neighborFinset h = ∅ := by
    intro h hh
    have hd : D.degree h = 0 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree (by norm_num) hmin hcard (by
          have := hdegHigh h hh
          omega)).1
    rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hd]
  have hfullConnected :=
    squareOrderNine_threeHigh_secondProfile_ordinaryDefect_connected
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
  exact squareOrderNine_threeHigh_secondProfile_deleted_owner_connected
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
      h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner hOcard
      hdegOrd hdegHigh hhighIndependent hdefectHighIsolated hfullConnected

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_deleted_owner_connected
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_deleted_owner_connected_of_profile

end

end Erdos85
