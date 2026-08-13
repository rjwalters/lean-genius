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

/-- Global perfect-code form of the preceding pointwise count.  Fixing a
degree-eight vertex `v`, every low vertex belongs to the closed defect
neighborhood of a unique neighbor of `v`.  These unique owners are the
partition map used in the unresolved small-high order-49 strata. -/
theorem orderFortyNine_existsUnique_highNeighbor_closedDefectOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v y : V}
    (hv : G.degree v = 8) (hy : G.degree y = 7) :
    ∃! x : V, x ∈ G.neighborFinset v ∧
      y ∈ insert x ((secondOrderDefectGraph G).neighborFinset x) := by
  have hcardOne :=
    orderFortyNine_closedDefectNeighborhood_inter_highNeighborhood
      G hfree hmin hcard hv hy
  rcases Finset.card_eq_one.mp hcardOne with ⟨x, hx⟩
  have hxmem : x ∈ insert y
      ((secondOrderDefectGraph G).neighborFinset y) ∩
        G.neighborFinset v := by
    simp [hx]
  refine ⟨x, ?_, ?_⟩
  · have hxparts := Finset.mem_inter.mp hxmem
    refine ⟨hxparts.2, ?_⟩
    rcases Finset.mem_insert.mp hxparts.1 with hxy | hD
    · exact Finset.mem_insert.mpr (Or.inl hxy.symm)
    · exact Finset.mem_insert.mpr (Or.inr (by
        simpa [SimpleGraph.mem_neighborFinset,
          (secondOrderDefectGraph G).adj_comm] using hD))
  · intro z hz
    have hzmem : z ∈ insert y
        ((secondOrderDefectGraph G).neighborFinset y) ∩
          G.neighborFinset v := by
      apply Finset.mem_inter.mpr
      refine ⟨?_, hz.1⟩
      rcases Finset.mem_insert.mp hz.2 with hyz | hD
      · exact Finset.mem_insert.mpr (Or.inl hyz.symm)
      · exact Finset.mem_insert.mpr (Or.inr (by
          simpa [SimpleGraph.mem_neighborFinset,
            (secondOrderDefectGraph G).adj_comm] using hD))
    simpa [hx] using hzmem

/-- Distinct code vertices have disjoint closed defect neighborhoods. -/
theorem orderFortyNine_closedDefectNeighborhood_pairwiseDisjoint_at_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8) :
    (G.neighborFinset v : Set V).PairwiseDisjoint
      (fun x => (insert x
        ((secondOrderDefectGraph G).neighborFinset x) : Finset V)) := by
  intro x hx z hz hxz
  change Disjoint
    (insert x ((secondOrderDefectGraph G).neighborFinset x))
    (insert z ((secondOrderDefectGraph G).neighborFinset z))
  rw [Finset.disjoint_left]
  intro y hyx hyz
  have hxAdj : G.Adj v x := by
    simpa [SimpleGraph.mem_neighborFinset] using hx
  have hxdeg : G.degree x = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv hxAdj
  have hydeg : G.degree y = 7 := by
    rcases Finset.mem_insert.mp hyx with rfl | hD
    · exact hxdeg
    · rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard y with hy7 | hy8
      · exact hy7
      · have hyDzero :=
          (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
            G hfree hmin hcard hy8).1
        have hDAdj : (secondOrderDefectGraph G).Adj y x := by
          simpa [SimpleGraph.mem_neighborFinset,
            (secondOrderDefectGraph G).adj_comm] using hD
        have hpos : 0 < (secondOrderDefectGraph G).degree y := by
          rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr
            ⟨x, ((secondOrderDefectGraph G).mem_neighborFinset y x).mpr hDAdj⟩
        omega
  obtain ⟨owner, howner, hunique⟩ :=
    orderFortyNine_existsUnique_highNeighbor_closedDefectOwner
      G hfree hmin hcard hv hydeg
  have hxeq : x = owner := hunique x ⟨hx, hyx⟩
  have hzeq : z = owner := hunique z ⟨hz, hyz⟩
  exact hxz (hxeq.trans hzeq.symm)

end

end Erdos85
