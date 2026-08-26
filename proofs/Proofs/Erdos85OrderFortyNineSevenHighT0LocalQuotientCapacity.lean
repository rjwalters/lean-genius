import Proofs.Erdos85OrderFortyNineSevenHighT0LocalQuotientBridge

/-!
# Graph-facing local empty-neighbor capacities

The pair- and zero-support filters are disjoint subsets of a low vertex's
seven neighbors.  Combined with the exact graph law `P = E + k`, this gives
the uniform bound `E + k ≤ 3`, hence the familiar capacities `E≤1,2,3` for
pair-, singleton-, and empty-support roots respectively.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Two distinct weight fibers occupy at most the ambient finite set. -/
theorem card_filter_eq_two_add_card_filter_eq_zero_le_card
    {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → Nat) :
    (S.filter fun x => weight x = 2).card +
      (S.filter fun x => weight x = 0).card ≤ S.card := by
  let P := S.filter fun x => weight x = 2
  let Z := S.filter fun x => weight x = 0
  have hdisjoint : Disjoint P Z := by
    rw [Finset.disjoint_left]
    intro x hxP hxZ
    have h2 := (Finset.mem_filter.mp hxP).2
    have h0 := (Finset.mem_filter.mp hxZ).2
    omega
  rw [← Finset.card_union_of_disjoint hdisjoint]
  apply Finset.card_le_card
  exact Finset.union_subset (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)

/-- Every low root has at most three empty-low neighbors plus high neighbors.
Equivalently, if its high-support size is `k`, its empty-low degree is at most
`3-k`.  This is stated without truncated subtraction. -/
theorem sevenHigh_t0_lowEmptyNeighborCount_add_support_le_three
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7) :
    (((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).filter fun x =>
        x ∉ orderFortyNineHighVertices G).card +
      (orderFortyNineHighSupport G y).card ≤ 3 := by
  have hpair := sevenHigh_t0_pairNeighborCount_eq_zeroSupportNeighborCount
    G hfree hmin hHigh hzero hy
  have hexact :=
    sevenHigh_t0_pairNeighborCount_eq_lowEmptyNeighborCount_add_support
      G hfree hmin hHigh hzero hy
  have hcap := card_filter_eq_two_add_card_filter_eq_zero_le_card
    (G.neighborFinset y) fun x => (orderFortyNineHighSupport G x).card
  have hcard : (G.neighborFinset y).card = 7 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hy
  omega

/-- Pair-support roots have at most one actual low empty-support neighbor. -/
theorem sevenHigh_t0_pairRoot_lowEmptyNeighbor_bound
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7)
    (hySupport : (orderFortyNineHighSupport G y).card = 2) :
    (((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).filter fun x =>
        x ∉ orderFortyNineHighVertices G).card ≤ 1 := by
  have h := sevenHigh_t0_lowEmptyNeighborCount_add_support_le_three
    G hfree hmin hHigh hzero hy
  omega

/-- Singleton-support roots have at most two actual low empty-support
neighbors. -/
theorem sevenHigh_t0_singletonRoot_lowEmptyNeighbor_bound
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7)
    (hySupport : (orderFortyNineHighSupport G y).card = 1) :
    (((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).filter fun x =>
        x ∉ orderFortyNineHighVertices G).card ≤ 2 := by
  have h := sevenHigh_t0_lowEmptyNeighborCount_add_support_le_three
    G hfree hmin hHigh hzero hy
  omega

/-- Empty-support roots have at most three actual low empty-support
neighbors. -/
theorem sevenHigh_t0_emptyRoot_lowEmptyNeighbor_bound
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7) :
    (((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).filter fun x =>
        x ∉ orderFortyNineHighVertices G).card ≤ 3 := by
  exact (Nat.le_add_right _ _).trans
    (sevenHigh_t0_lowEmptyNeighborCount_add_support_le_three
      G hfree hmin hHigh hzero hy)

end

end Erdos85

#print axioms Erdos85.card_filter_eq_two_add_card_filter_eq_zero_le_card
#print axioms Erdos85.sevenHigh_t0_lowEmptyNeighborCount_add_support_le_three
#print axioms Erdos85.sevenHigh_t0_pairRoot_lowEmptyNeighbor_bound
#print axioms Erdos85.sevenHigh_t0_singletonRoot_lowEmptyNeighbor_bound
#print axioms Erdos85.sevenHigh_t0_emptyRoot_lowEmptyNeighbor_bound
