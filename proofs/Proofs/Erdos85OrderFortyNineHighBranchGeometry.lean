import Proofs.Erdos85OrderFortyNineLowTriangleIncidence

/-!
# Zero-slack branches around a high vertex at order 49

Each of the eight neighbors of a high vertex has five vertices in its
second-layer branch.  These branches are pairwise disjoint and exhaust all
forty vertices outside the closed high neighborhood.  Branches whose parents
form one of the four local triangle pairs have no edges between them.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every second-layer branch rooted at a neighbor of a high vertex has size
five. -/
theorem orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V} (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (secondLayerBranch G v s).card = 5 := by
  have hs7 := orderFortyNine_neighbor_degree_seven_of_degreeEight
    G hfree hmin hcard hv s.2
  have hcommon := orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
    G hfree hmin hcard hv s
  rw [degree_induce_neighborSet_eq_card_common] at hcommon
  have haccount := card_secondLayerBranch_add_common_add_one G v s
  omega

/-- The second layer of a high vertex has exactly forty vertices. -/
theorem orderFortyNine_card_secondLayer_degreeEight_eq_forty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V} (hv : G.degree v = 8) :
    (secondLayer G v).card = 40 := by
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
  rw [secondLayer, Finset.card_biUnion hdisj]
  calc
    (∑ s : {z : V // z ∈ G.neighborSet v},
        (secondLayerBranch G v s).card) =
        ∑ _s : {z : V // z ∈ G.neighborSet v}, 5 := by
      apply Finset.sum_congr rfl
      intro s _
      exact orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
        G hfree hmin hcard hv s
    _ = 40 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_subtype]
      have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
          G.neighborFinset v := by ext z; simp
      rw [heq, G.card_neighborFinset_eq_degree, hv]
      norm_num

/-- No vertex lies beyond distance two from a high vertex. -/
theorem orderFortyNine_externalRepairCandidates_degreeEight_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V} (hv : G.degree v = 8) :
    externalRepairCandidates G v = ∅ := by
  have hpartition :=
    card_externalRepairCandidates_add_card_secondLayer_add_degree_add_one G v
  rw [orderFortyNine_card_secondLayer_degreeEight_eq_forty
      G hfree hmin hcard hv, hv, hcard] at hpartition
  apply Finset.card_eq_zero.mp
  omega

/-- If two parents are paired inside the neighborhood of a high vertex,
there are no edges between their five-vertex second-layer branches. -/
theorem orderFortyNine_not_adj_between_paired_highBranches
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s t : {z : V // z ∈ G.neighborSet v}} (hst : G.Adj s.1 t.1)
    {a b : V} (ha : a ∈ secondLayerBranch G v s)
    (hb : b ∈ secondLayerBranch G v t) :
    ¬ G.Adj a b := by
  intro hab
  have hsa : G.Adj s.1 a := by
    exact (G.mem_neighborFinset s.1 a).mp (Finset.mem_sdiff.mp ha).1
  have htb : G.Adj t.1 b := by
    exact (G.mem_neighborFinset t.1 b).mp (Finset.mem_sdiff.mp hb).1
  have haOutside : a ∉ insert v (G.neighborFinset v) :=
    (Finset.mem_sdiff.mp ha).2
  have hbOutside : b ∉ insert v (G.neighborFinset v) :=
    (Finset.mem_sdiff.mp hb).2
  have hsb : s.1 ≠ b := by
    intro h
    subst b
    apply hbOutside
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
    exact Or.inr s.2
  have hat : a ≠ t.1 := by
    intro h
    subst a
    apply haOutside
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
    exact Or.inr t.2
  exact hfree (containsC4_of_two_common hsb hat
    hsa.symm hab hst.symm htb)

/-- An outer vertex has at most one neighbor in any fixed high-root branch.
This is the basic cross-branch `C₄` restriction. -/
theorem orderFortyNine_card_neighbors_inter_highBranch_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v a : V}
    (haOutside : a ∉ insert v (G.neighborFinset v))
    (t : {z : V // z ∈ G.neighborSet v}) :
    (G.neighborFinset a ∩ secondLayerBranch G v t).card ≤ 1 := by
  have hat : a ≠ t.1 := by
    intro h
    subst a
    apply haOutside
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
    exact Or.inr t.2
  have hsub : G.neighborFinset a ∩ secondLayerBranch G v t ⊆
      G.neighborFinset a ∩ G.neighborFinset t.1 := by
    intro b hb
    have hab := (Finset.mem_inter.mp hb).1
    have htb := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).2).1
    exact Finset.mem_inter.mpr ⟨hab, htb⟩
  exact (Finset.card_le_card hsub).trans
    (common_le_one_of_not_containsC4 hfree a t.1 hat)

/-- For two distinct high vertices, their unique common neighbor is exactly
the unique parent in the first high vertex's neighborhood whose second-layer
branch contains the second high vertex. -/
theorem orderFortyNine_existsUnique_highBranch_containing_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v w : V}
    (hv : G.degree v = 8) (hw : G.degree w = 8) (hvw : v ≠ w) :
    ∃! c : {z : V // z ∈ G.neighborSet v},
      w ∈ secondLayerBranch G v c := by
  have hcommon := orderFortyNine_card_common_degreeEight_eq_one
    G hfree hmin hcard hv hw hvw
  rcases Finset.card_eq_one.mp hcommon with ⟨c, hc⟩
  have hcmem : c ∈ G.neighborFinset v ∩ G.neighborFinset w := by
    simp [hc]
  have hcv : G.Adj v c := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hcmem).1
  have hcw : G.Adj c w := by
    have := (Finset.mem_inter.mp hcmem).2
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  let C : {z : V // z ∈ G.neighborSet v} := ⟨c, hcv⟩
  refine ⟨C, ?_, ?_⟩
  · apply Finset.mem_sdiff.mpr
    refine ⟨(G.mem_neighborFinset c w).mpr hcw, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨hvw.symm,
      orderFortyNine_not_adj_degreeEight_degreeEight
        G hfree hmin hcard hv hw⟩
  · intro D hwD
    apply Subtype.ext
    have hDcommon : D.1 ∈ G.neighborFinset v ∩ G.neighborFinset w := by
      have hDw : G.Adj D.1 w :=
        (G.mem_neighborFinset D.1 w).mp (Finset.mem_sdiff.mp hwD).1
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨D.2, by simpa [G.adj_comm] using hDw⟩
    simpa [hc] using hDcommon

/-- Let `w` lie in the branch of parent `c` around a high root `v`.  Then
`w` has exactly one neighbor in every branch whose parent is not paired with
`c`.  This is the basic compatibility law between two high-root branch
systems. -/
theorem orderFortyNine_card_highNeighbors_in_unpaired_branch_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v w : V}
    (hv : G.degree v = 8) (hw : G.degree w = 8)
    {c u : {z : V // z ∈ G.neighborSet v}}
    (hwc : w ∈ secondLayerBranch G v c)
    (hcu : ¬ G.Adj c.1 u.1) :
    (G.neighborFinset w ∩ secondLayerBranch G v u).card = 1 := by
  have hwOutside : w ∉ insert v (G.neighborFinset v) :=
    (Finset.mem_sdiff.mp hwc).2
  have hle := orderFortyNine_card_neighbors_inter_highBranch_le_one
    G hfree hwOutside u
  have hwu : w ≠ u.1 := by
    intro h
    subst w
    have hu7 := orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv u.2
    omega
  have hconflictSet := orderFortyNine_conflictNeighborFinset_degreeEight
    G hfree hmin hcard hw
  have huErase : u.1 ∈ (Finset.univ : Finset V).erase w := by
    simp [hwu.symm]
  have huConflictMem :
      u.1 ∈ (commonNeighborConflict G).neighborFinset w := by
    rw [hconflictSet]
    exact huErase
  obtain ⟨q, hq⟩ :=
    (((commonNeighborConflict G).mem_neighborFinset w u.1).mp
      huConflictMem).2
  have hqCommon : q ∈ G.neighborFinset w ∩ G.neighborFinset u.1 := hq
  have hqw : G.Adj w q := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hqCommon).1
  have hqu : G.Adj u.1 q := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hqCommon).2
  have hqv : q ≠ v := by
    intro h
    subst q
    exact (orderFortyNine_not_adj_degreeEight_degreeEight
      G hfree hmin hcard hv hw) hqw.symm
  have hqNotNv : q ∉ G.neighborFinset v := by
    intro hqNv
    have hqvc : q ∈ G.neighborFinset v ∩ G.neighborFinset w := by
      exact Finset.mem_inter.mpr ⟨hqNv,
        (G.mem_neighborFinset w q).mpr hqw⟩
    have hcvc : c.1 ∈ G.neighborFinset v ∩ G.neighborFinset w := by
      have hcw : G.Adj c.1 w :=
        (G.mem_neighborFinset c.1 w).mp (Finset.mem_sdiff.mp hwc).1
      exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset v c.1).mpr c.2,
        (G.mem_neighborFinset w c.1).mpr hcw.symm⟩
    have hone := orderFortyNine_card_common_degreeEight_eq_one
      G hfree hmin hcard hv hw (by
        intro h
        subst w
        exact hwOutside (by simp))
    rcases Finset.card_eq_one.mp hone with ⟨r, hr⟩
    have hqr : q = r := by simpa [hr] using hqvc
    have hcr : c.1 = r := by simpa [hr] using hcvc
    have hqc : q = c.1 := hqr.trans hcr.symm
    exact hcu (hqc ▸ hqu.symm)
  have hqBranch : q ∈ secondLayerBranch G v u := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(G.mem_neighborFinset u.1 q).mpr hqu, ?_⟩
    simp only [Finset.mem_insert, hqv, false_or,
      SimpleGraph.mem_neighborFinset]
    intro hvq
    exact hqNotNv ((G.mem_neighborFinset v q).mpr hvq)
  have hpos : 0 <
      (G.neighborFinset w ∩ secondLayerBranch G v u).card := by
    apply Finset.card_pos.mpr
    exact ⟨q, Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset w q).mpr hqw, hqBranch⟩⟩
  omega

end

end Erdos85
