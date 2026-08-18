import Proofs.Erdos85OrderFortyNineHighPartnerBound

/-!
# Forced low triangles at order 49

A degree-seven vertex whose neighbors are all degree seven has positive
local triangle degree by an exact rooted Moore-layer count.  In particular,
every low vertex with no high neighbor lies in an all-low triangle.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Rooted Moore accounting when the center and all its neighbors have degree
seven.  The one-vertex deficit from the triangle-free Moore tree is absorbed
by local triangle degree. -/
theorem orderFortyNine_external_add_one_eq_localNeighborhoodDegreeSum_of_all_neighbors_low
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 49) {x : V}
    (hx : G.degree x = 7)
    (hneigh : ∀ y, G.Adj x y → G.degree y = 7) :
    (externalRepairCandidates G x).card + 1 =
      ∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y := by
  classical
  let S := ∑ y : {z : V // z ∈ G.neighborSet x},
    (G.induce (G.neighborSet x)).degree y
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree x
  have hD : (secondLayer G x).card =
      ∑ y : {z : V // z ∈ G.neighborSet x},
        (secondLayerBranch G x y).card := by
    rw [secondLayer, Finset.card_biUnion hdisj]
  have hNcard : Fintype.card {z : V // z ∈ G.neighborSet x} = 7 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hx]
  have hbranches :
      (∑ y : {z : V // z ∈ G.neighborSet x},
          ((secondLayerBranch G x y).card +
            (G.induce (G.neighborSet x)).degree y + 1)) =
        ∑ _y : {z : V // z ∈ G.neighborSet x}, 7 := by
    apply Finset.sum_congr rfl
    intro y _
    rw [degree_induce_neighborSet_eq_card_common]
    exact (card_secondLayerBranch_add_common_add_one G x y).trans
      (hneigh y.1 y.2)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hbranches
  have hones :
      (∑ _y : {z : V // z ∈ G.neighborSet x}, 1) = 7 := by
    rw [Finset.sum_const, Finset.card_univ, hNcard]
    norm_num
  have hsevens :
      (∑ _y : {z : V // z ∈ G.neighborSet x}, 7) = 7 * 7 := by
    rw [Finset.sum_const, Finset.card_univ, hNcard]
    norm_num
  have hbranches' : (secondLayer G x).card + S + 7 = 7 * 7 := by
    rw [hD]
    simpa [S, hones, hsevens] using hbranches
  have hpartition :=
    card_externalRepairCandidates_add_card_secondLayer_add_degree_add_one G x
  rw [hx, hcard] at hpartition
  change (externalRepairCandidates G x).card + (secondLayer G x).card + 7 + 1 =
    49 at hpartition
  change (externalRepairCandidates G x).card + 1 = S
  omega

/-- In particular the local triangle-degree sum is positive. -/
theorem orderFortyNine_localNeighborhoodDegreeSum_pos_of_all_neighbors_low
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 49) {x : V}
    (hx : G.degree x = 7)
    (hneigh : ∀ y, G.Adj x y → G.degree y = 7) :
    0 < ∑ y : {z : V // z ∈ G.neighborSet x},
      (G.induce (G.neighborSet x)).degree y := by
  have h :=
    orderFortyNine_external_add_one_eq_localNeighborhoodDegreeSum_of_all_neighbors_low
      G hfree hcard hx hneigh
  omega

/-- The antipodal degree of such a center is odd: its successor is twice the
number of triangles through the center. -/
theorem orderFortyNine_antipodalNeighbors_card_odd_of_all_neighbors_low
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 49) {x : V}
    (hx : G.degree x = 7)
    (hneigh : ∀ y, G.Adj x y → G.degree y = 7) :
    Odd (antipodalNeighbors G x).card := by
  have hexact :=
    orderFortyNine_external_add_one_eq_localNeighborhoodDegreeSum_of_all_neighbors_low
      G hfree hcard hx hneigh
  have hmap : (antipodalNeighbors G x).card =
      (externalRepairCandidates G x).card := by
    simp [antipodalNeighbors]
  have hhand :
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) =
        2 * (G.induce (G.neighborSet x)).edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges
      (G.induce (G.neighborSet x))
  rw [← hmap, hhand] at hexact
  refine ⟨(G.induce (G.neighborSet x)).edgeFinset.card - 1, ?_⟩
  have hpos : 0 < (G.induce (G.neighborSet x)).edgeFinset.card := by
    omega
  omega

/-- A low vertex with no high neighbor belongs to a triangle all three of
whose vertices are low. -/
theorem orderFortyNine_exists_allLow_triangle_of_highNeighborCount_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7)
    (hkzero : (G.neighborFinset x ∩
      orderFortyNineHighVertices G).card = 0) :
    ∃ y z : V,
      G.degree y = 7 ∧ G.degree z = 7 ∧
      G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  have hnoneHigh : ∀ y, G.Adj x y → G.degree y = 7 := by
    intro y hxy
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard y with hy | hy
    · exact hy
    · have hyMem : y ∈ G.neighborFinset x ∩
          orderFortyNineHighVertices G := by
        simp [SimpleGraph.mem_neighborFinset, hxy,
          orderFortyNineHighVertices, hy]
      rw [Finset.card_eq_zero] at hkzero
      rw [hkzero] at hyMem
      exact (Finset.notMem_empty y hyMem).elim
  have hsum :=
    orderFortyNine_localNeighborhoodDegreeSum_pos_of_all_neighbors_low
      G hfree hcard hx hnoneHigh
  have hex : ∃ y : {z : V // z ∈ G.neighborSet x},
      0 < (G.induce (G.neighborSet x)).degree y := by
    by_contra hnone
    push_neg at hnone
    have hzero : (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      have hy := hnone y
      omega
    omega
  rcases hex with ⟨y, hypos⟩
  rcases ((G.induce (G.neighborSet x)).degree_pos_iff_exists_adj y).mp hypos with
    ⟨z, hyz⟩
  refine ⟨y.1, z.1, hnoneHigh y.1 y.2, hnoneHigh z.1 z.2,
    y.2, z.2, ?_⟩
  exact hyz

end

end Erdos85
