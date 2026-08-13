import Proofs.Erdos85OrderFortyNineHighBranchGeometry

/-!
# The two five-block systems in the order-49 one-high stratum

Around the unique high vertex, the forty leaves admit two partitions into
eight blocks of size five: the original-graph second-layer branches and the
second-order-defect owner fibers.  Their overlap matrix is the finite quotient
object for the remaining one-high analysis.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def orderFortyNineDefectOwnerFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s : {z : V // z ∈ G.neighborSet v}) : Finset V :=
  (secondOrderDefectGraph G).neighborFinset s.1

def orderFortyNineOneHighOverlap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  (secondLayerBranch G v s ∩ orderFortyNineDefectOwnerFiber G v t).card

/-- Every defect-owner fiber centered in `N(v)` has five leaves. -/
theorem orderFortyNine_card_defectOwnerFiber_eq_five_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (orderFortyNineDefectOwnerFiber G v s).card = 5 := by
  have hs : s.1 ∈ G.neighborFinset v := by
    exact (G.mem_neighborFinset v s.1).2 s.2
  have hclosed :=
    orderFortyNine_card_closedDefectNeighborhood_eq_six_of_one_high
      G hfree hmin hcard hHigh hv hs
  have hnot : s.1 ∉ (secondOrderDefectGraph G).neighborFinset s.1 := by simp
  rw [Finset.card_insert_of_notMem hnot] at hclosed
  simpa [orderFortyNineDefectOwnerFiber] using hclosed

/-- Every original-graph branch has five leaves. -/
theorem orderFortyNine_card_originalBranch_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (secondLayerBranch G v s).card = 5 :=
  orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
    G hfree hmin hcard hv s

/-- Every overlap entry lies between zero and five. -/
theorem orderFortyNineOneHighOverlap_le_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    orderFortyNineOneHighOverlap G v s t ≤ 5 := by
  apply le_trans (Finset.card_le_card Finset.inter_subset_left)
  exact (orderFortyNine_card_originalBranch_eq_five
    G hfree hmin hcard hv s).le

end

end Erdos85
