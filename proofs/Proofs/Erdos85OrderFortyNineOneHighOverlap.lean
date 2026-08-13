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

/-- Each original branch is partitioned by the eight defect-owner fibers. -/
theorem orderFortyNine_biUnion_branch_inter_ownerFiber
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
    (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).biUnion
        (fun t => secondLayerBranch G v s ∩
          orderFortyNineDefectOwnerFiber G v t) =
      secondLayerBranch G v s := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨t, _, hyt⟩ := hy
    exact (Finset.mem_inter.mp hyt).1
  · intro hy
    have hyOutside : y ∉ insert v (G.neighborFinset v) :=
      (Finset.mem_sdiff.mp hy).2
    have hyv : y ≠ v := by
      intro h
      subst y
      exact hyOutside (by simp)
    have hvy : ¬ G.Adj v y := by
      intro h
      exact hyOutside (by
        simp [SimpleGraph.mem_neighborFinset, h])
    have hydeg : G.degree y = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard y with hy7 | hy8
      · exact hy7
      · have hvHigh : v ∈ orderFortyNineHighVertices G := by
          simp [orderFortyNineHighVertices, hv]
        have hyHigh : y ∈ orderFortyNineHighVertices G := by
          simp [orderFortyNineHighVertices, hy8]
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hHigh
        have hvw : v = w := by simpa [hw] using hvHigh
        have hyw : y = w := by simpa [hw] using hyHigh
        exact (hyv (hyw.trans hvw.symm)).elim
    obtain ⟨x, hx, _⟩ :=
      orderFortyNine_existsUnique_defectCenter_of_not_adj_high
        G hfree hmin hcard hv hydeg hvy
    let t : {z : V // z ∈ G.neighborSet v} :=
      ⟨x, (G.mem_neighborFinset v x).1 hx.1⟩
    rw [Finset.mem_biUnion]
    refine ⟨t, Finset.mem_univ t, Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
    exact ((secondOrderDefectGraph G).mem_neighborFinset x y).2 hx.2

/-- The intersections in the preceding branch decomposition are pairwise
disjoint. -/
theorem orderFortyNine_branch_inter_ownerFiber_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    ((Finset.univ : Finset {z : V // z ∈ G.neighborSet v}) :
      Set {z : V // z ∈ G.neighborSet v}).PairwiseDisjoint
      (fun t => secondLayerBranch G v s ∩
        orderFortyNineDefectOwnerFiber G v t) := by
  intro t _ u _ htu
  apply Finset.disjoint_left.mpr
  intro y hyt hyu
  have htOwner := (Finset.mem_inter.mp hyt).2
  have huOwner := (Finset.mem_inter.mp hyu).2
  have hpair := orderFortyNine_closedDefectNeighborhood_pairwiseDisjoint_at_high
    G hfree hmin hcard hv
  have htmem : t.1 ∈ (G.neighborFinset v : Set V) := by
    exact (G.mem_neighborFinset v t.1).2 t.2
  have humem : u.1 ∈ (G.neighborFinset v : Set V) := by
    exact (G.mem_neighborFinset v u.1).2 u.2
  have htune : t.1 ≠ u.1 := fun h => htu (Subtype.ext h)
  have hdisj := hpair htmem humem htune
  exact Finset.disjoint_left.mp hdisj
    (Finset.mem_insert.mpr (Or.inr htOwner))
    (Finset.mem_insert.mpr (Or.inr huOwner))

/-- Every row of the one-high overlap matrix sums to five. -/
theorem sum_orderFortyNineOneHighOverlap_row_eq_five
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
    (∑ t, orderFortyNineOneHighOverlap G v s t) = 5 := by
  rw [← orderFortyNine_card_originalBranch_eq_five
      G hfree hmin hcard hv s,
    ← orderFortyNine_biUnion_branch_inter_ownerFiber
      G hfree hmin hcard hHigh hv s,
    Finset.card_biUnion
      (orderFortyNine_branch_inter_ownerFiber_pairwiseDisjoint
        G hfree hmin hcard hv s)]
  rfl

end

end Erdos85
