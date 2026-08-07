import Proofs.Erdos85OrderFortyNineDefectEigenvectors

/-!
# Perfect codes in the order-49 low defect graph

Every high neighborhood is an efficient dominating set of the low-sector
second-order defect graph.  This is a combinatorial form of `B (D + I) = J`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The closed defect neighborhood of every low vertex meets every high
neighborhood in exactly one vertex. -/
theorem orderFortyNine_closedDefectNeighborhood_inter_highNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v x : V}
    (hv : G.degree v = 8) (hx : G.degree x = 7) :
    (insert x ((secondOrderDefectGraph G).neighborFinset x) ∩
        G.neighborFinset v).card = 1 := by
  have hcount := orderFortyNine_card_highNeighbors_inter_defectNeighbors
    G hfree hmin hcard hv hx
  rw [Finset.inter_comm] at hcount
  by_cases hvx : G.Adj v x
  · rw [if_pos hvx] at hcount
    have hempty : (secondOrderDefectGraph G).neighborFinset x ∩
        G.neighborFinset v = ∅ := Finset.card_eq_zero.mp hcount
    simp [Finset.insert_inter, SimpleGraph.mem_neighborFinset, hvx, hempty]
  · rw [if_neg hvx] at hcount
    simpa [Finset.insert_inter, SimpleGraph.mem_neighborFinset, hvx] using hcount

/-- A defect edge cannot join two low vertices having a common high
neighbor.  Equivalently, incidence blocks at the ends of a defect edge are
disjoint. -/
theorem orderFortyNine_no_common_highNeighbor_of_defectAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v x y : V}
    (hv : G.degree v = 8) (hx : G.degree x = 7)
    (hDxy : (secondOrderDefectGraph G).Adj x y) :
    ¬ (G.Adj v x ∧ G.Adj v y) := by
  rintro ⟨hvx, hvy⟩
  have hcount := orderFortyNine_card_highNeighbors_inter_defectNeighbors
    G hfree hmin hcard hv hx
  rw [if_pos hvx, Finset.card_eq_zero] at hcount
  have hy : y ∈ G.neighborFinset v ∩
      (secondOrderDefectGraph G).neighborFinset x := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hvy, hDxy⟩
  rw [hcount] at hy
  exact Finset.notMem_empty y hy

end

end Erdos85
