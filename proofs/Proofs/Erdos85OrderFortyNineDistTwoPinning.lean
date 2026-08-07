import Proofs.Erdos85OrderFortyNineHighBranchGeometry
import Proofs.Erdos85OrderFortyNineLocalEdgePartition

/-!
# Pinning the three-high distance-two configuration at order 49

Suppose a degree-seven vertex is adjacent to three degree-eight vertices.
It is the unique common neighbor of each pair.  Relative to any one high
root, the other two highs therefore lie in the same five-vertex branch, and
the center's local matching partner is adjacent to neither of them.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A displayed common neighbor of two distinct high vertices is their
unique common neighbor. -/
theorem orderFortyNineDistTwo_common_highPair_eq_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v w s : V} (hv : G.degree v = 8) (hw : G.degree w = 8)
    (hvw : v ≠ w) (hsv : G.Adj s v) (hsw : G.Adj s w) :
    G.neighborFinset v ∩ G.neighborFinset w = {s} := by
  have hone := orderFortyNine_card_common_degreeEight_eq_one
    G hfree hmin hcard hv hw hvw
  rw [Finset.card_eq_one] at hone
  rcases hone with ⟨q, hq⟩
  have hs : s ∈ G.neighborFinset v ∩ G.neighborFinset w := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hsv.symm, hsw.symm⟩
  have hsq : s = q := by simpa [hq] using hs
  simpa [hsq] using hq

/-- Relative to the first high root, both foreign highs lie in the branch
whose parent is the common low vertex. -/
theorem orderFortyNineDistTwo_foreign_highs_in_common_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 sStar : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (hs1 : G.Adj sStar v1) (hs2 : G.Adj sStar v2)
    (hs3 : G.Adj sStar v3) :
    let parent : {z : V // z ∈ G.neighborSet v1} :=
      ⟨sStar, by simpa using hs1.symm⟩
    v2 ∈ secondLayerBranch G v1 parent ∧
      v3 ∈ secondLayerBranch G v1 parent := by
  dsimp
  have hnot12 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv2
  have hnot13 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv3
  constructor
  · rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hs2, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨h12.symm, fun h => hnot12 h⟩
  · rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hs3, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨h13.symm, fun h => hnot13 h⟩

/-- The common low vertex has a unique partner inside the first high
neighborhood.  That partner cannot see either foreign high, since it would
be a second common neighbor of the corresponding high pair. -/
theorem orderFortyNineDistTwo_exists_partner_not_adj_foreign_highs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 sStar : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (hs1 : G.Adj sStar v1) (hs2 : G.Adj sStar v2)
    (hs3 : G.Adj sStar v3) :
    ∃! t : V, G.Adj sStar t ∧ G.Adj v1 t ∧
      ¬ G.Adj t v2 ∧ ¬ G.Adj t v3 := by
  let sLocal : {z : V // z ∈ G.neighborSet v1} :=
    ⟨sStar, by simpa using hs1.symm⟩
  have hdeg := orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
    G hfree hmin hcard hv1 sLocal
  rw [← (G.induce (G.neighborSet v1)).card_neighborFinset_eq_degree,
    Finset.card_eq_one] at hdeg
  rcases hdeg with ⟨tLocal, htLocal⟩
  refine ⟨tLocal.1, ?_, ?_⟩
  · have htmem : tLocal ∈
        (G.induce (G.neighborSet v1)).neighborFinset sLocal := by
      simp [htLocal]
    have hst : G.Adj sStar tLocal.1 := by
      exact ((G.induce (G.neighborSet v1)).mem_neighborFinset
        sLocal tLocal).mp htmem
    have ht1 : G.Adj v1 tLocal.1 := tLocal.2
    refine ⟨hst, ht1, ?_, ?_⟩
    · intro ht2
      have hcommon := orderFortyNineDistTwo_common_highPair_eq_singleton
        G hfree hmin hcard hv1 hv2 h12 hs1 hs2
      have htmem' : tLocal.1 ∈
          G.neighborFinset v1 ∩ G.neighborFinset v2 := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨ht1, ht2.symm⟩
      have hts : tLocal.1 = sStar := by simpa [hcommon] using htmem'
      exact G.loopless.irrefl sStar (hts ▸ hst)
    · intro ht3
      have hcommon := orderFortyNineDistTwo_common_highPair_eq_singleton
        G hfree hmin hcard hv1 hv3 h13 hs1 hs3
      have htmem' : tLocal.1 ∈
          G.neighborFinset v1 ∩ G.neighborFinset v3 := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨ht1, ht3.symm⟩
      have hts : tLocal.1 = sStar := by simpa [hcommon] using htmem'
      exact G.loopless.irrefl sStar (hts ▸ hst)
  · intro q hq
    have hqmem : (⟨q, hq.2.1⟩ : {z : V // z ∈ G.neighborSet v1}) ∈
        (G.induce (G.neighborSet v1)).neighborFinset sLocal := by
      exact ((G.induce (G.neighborSet v1)).mem_neighborFinset sLocal
        (⟨q, hq.2.1⟩ : {z : V // z ∈ G.neighborSet v1})).mpr hq.1
    have heq : (⟨q, hq.2.1⟩ : {z : V // z ∈ G.neighborSet v1}) =
        tLocal := by simpa [htLocal] using hqmem
    exact congrArg Subtype.val heq

end

end Erdos85
