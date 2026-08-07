import Proofs.Erdos85OrderFortyNineHighBranchGeometry

/-!
# Pinning the three-high distinct-common-neighbor configuration

Let `s12` and `s13` be the distinct common neighbors of `(v1,v2)` and
`(v1,v3)`.  Around the high root `v1`, the two foreign highs lie in the
branches rooted at `s12` and `s13`.  There is a sharp dichotomy: if the two
parents are locally paired, the branches have no cross edges; otherwise each
foreign high has exactly one neighbor in the opposite branch.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The two foreign highs occupy the branches rooted at their respective
common neighbors with the first high. -/
theorem orderFortyNineDistOne_foreign_highs_in_respective_branches
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 s12 s13 : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (hs12_1 : G.Adj s12 v1) (hs12_2 : G.Adj s12 v2)
    (hs13_1 : G.Adj s13 v1) (hs13_3 : G.Adj s13 v3) :
    let p12 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨s12, by simpa using hs12_1.symm⟩
    let p13 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨s13, by simpa using hs13_1.symm⟩
    v2 ∈ secondLayerBranch G v1 p12 ∧
      v3 ∈ secondLayerBranch G v1 p13 := by
  dsimp
  have hnot12 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv2
  have hnot13 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv3
  constructor
  · rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hs12_2, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨h12.symm, fun h => hnot12 h⟩
  · rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hs13_3, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨h13.symm, fun h => hnot13 h⟩

/-- Exact partner/non-partner dichotomy for the two occupied branches. -/
theorem orderFortyNineDistOne_branch_cross_incidence_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 s12 s13 : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (hs : s12 ≠ s13)
    (hs12_1 : G.Adj s12 v1) (hs12_2 : G.Adj s12 v2)
    (hs13_1 : G.Adj s13 v1) (hs13_3 : G.Adj s13 v3) :
    let p12 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨s12, by simpa using hs12_1.symm⟩
    let p13 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨s13, by simpa using hs13_1.symm⟩
    (G.Adj s12 s13 ∧
        (G.neighborFinset v2 ∩ secondLayerBranch G v1 p13).card = 0 ∧
        (G.neighborFinset v3 ∩ secondLayerBranch G v1 p12).card = 0) ∨
      (¬ G.Adj s12 s13 ∧
        (G.neighborFinset v2 ∩ secondLayerBranch G v1 p13).card = 1 ∧
        (G.neighborFinset v3 ∩ secondLayerBranch G v1 p12).card = 1) := by
  dsimp
  let p12 : {z : V // z ∈ G.neighborSet v1} :=
    ⟨s12, by simpa using hs12_1.symm⟩
  let p13 : {z : V // z ∈ G.neighborSet v1} :=
    ⟨s13, by simpa using hs13_1.symm⟩
  have hbranches := orderFortyNineDistOne_foreign_highs_in_respective_branches
    G hfree hmin hcard hv1 hv2 hv3 h12 h13
      hs12_1 hs12_2 hs13_1 hs13_3
  change v2 ∈ secondLayerBranch G v1 p12 ∧
    v3 ∈ secondLayerBranch G v1 p13 at hbranches
  by_cases hpaired : G.Adj s12 s13
  · left
    refine ⟨hpaired, ?_, ?_⟩
    · rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact orderFortyNine_not_adj_between_paired_highBranches
        G hfree hpaired hbranches.1 (Finset.mem_inter.mp hq).2
          ((G.mem_neighborFinset v2 q).mp (Finset.mem_inter.mp hq).1)
    · rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact orderFortyNine_not_adj_between_paired_highBranches
        G hfree hpaired.symm hbranches.2 (Finset.mem_inter.mp hq).2
          ((G.mem_neighborFinset v3 q).mp (Finset.mem_inter.mp hq).1)
  · right
    refine ⟨hpaired, ?_, ?_⟩
    · exact orderFortyNine_card_highNeighbors_in_unpaired_branch_eq_one
        G hfree hmin hcard hv1 hv2 hbranches.1 hpaired
    · exact orderFortyNine_card_highNeighbors_in_unpaired_branch_eq_one
        G hfree hmin hcard hv1 hv3 hbranches.2 (by
          simpa [G.adj_comm] using hpaired)

end

end Erdos85
