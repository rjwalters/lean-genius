import Proofs.Erdos85SquareOrderOuterGraph
import Proofs.Erdos85ConflictDefectDuality
import Proofs.Erdos85OrderFortyNineHighBranchGeometry

/-!
# The defect graph of the order-49 outer layer

At a unique degree-eight root, the forty vertices in the second layer induce
a six-regular `C₄`-free graph.  Its second-order defect graph is therefore
nine-regular.  Moreover, each of the eight five-point root branches is a
clique in that defect graph: two vertices in one branch already share their
parent outside the outer graph, so `C₄`-freeness forbids a second common
neighbor inside it.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The defect graph of the forty-vertex outer graph is nine-regular. -/
theorem orderFortyNine_outerDefect_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v) :
    ∀ x, (secondOrderDefectGraph (squareOrderOuterGraph G v)).degree x = 9 := by
  let R := squareOrderOuterGraph G v
  have hstructure := squareOrder_degree_succ_highRoot_structure
    G hfree (by omega : 2 ≤ 7) hmin (by simpa using hcard) hv
  have houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7 := by
    intro a ha
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard a with ha7 | ha8
    · exact ha7
    · have hav : a = v := hunique ha8
      rw [secondLayer] at ha
      rcases Finset.mem_biUnion.mp ha with ⟨s, _, has⟩
      exact ((Finset.mem_sdiff.mp has).2 (by simp [hav])).elim
  have hRreg : ∀ x, R.degree x = 6 := by
    simpa [R] using squareOrderOuterGraph_regular
      G hfree (by omega : 2 ≤ 7) (by simpa using hcard) hv
        hstructure.2.1 hstructure.2.2 houterDegree
  have hRcard : Fintype.card {x : V // x ∈ secondLayer G v} =
      6 * (6 - 1) + 3 + 7 := by
    rw [card_squareOrderOuterGraph G hfree (by omega : 2 ≤ 7) hv
      hstructure.2.1 hstructure.2.2]
  letI : DecidableRel (antipodalGraph R).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph R).Adj := Classical.decRel _
  intro x
  have h := secondOrderDefectGraph_degree_eq_excess_add_two
    R (squareOrderOuterGraph_not_containsC4 G hfree) hRreg hRcard x
  norm_num at h
  simpa [R] using h

/-- Distinct vertices in one high-root branch are adjacent in the defect
graph of the induced outer layer. -/
theorem orderFortyNine_outerDefect_adj_of_sameBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s : {z : V // z ∈ G.neighborSet v})
    (a b : {x : V // x ∈ secondLayer G v})
    (ha : a.1 ∈ secondLayerBranch G v s)
    (hb : b.1 ∈ secondLayerBranch G v s)
    (hab : a ≠ b) :
    (secondOrderDefectGraph (squareOrderOuterGraph G v)).Adj a b := by
  let R := squareOrderOuterGraph G v
  change (secondOrderDefectGraph R).Adj a b
  letI : DecidableRel (antipodalGraph R).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph R).Adj := Classical.decRel _
  have hRfree : ¬ containsC4 _ R :=
    squareOrderOuterGraph_not_containsC4 G hfree
  rw [← commonNeighborConflict_compl_eq_secondOrderDefectGraph R hRfree,
    SimpleGraph.compl_adj, commonNeighborConflict_adj_iff]
  refine ⟨hab, ?_⟩
  rintro ⟨_hab', hcommon⟩
  rcases hcommon with ⟨q, hq⟩
  have hqa := (Finset.mem_inter.mp hq).1
  have hqb := (Finset.mem_inter.mp hq).2
  have hsa : G.Adj s.1 a.1 := by
    exact (G.mem_neighborFinset s.1 a.1).mp
      (Finset.mem_sdiff.mp ha).1
  have hsb : G.Adj s.1 b.1 := by
    exact (G.mem_neighborFinset s.1 b.1).mp
      (Finset.mem_sdiff.mp hb).1
  have hqaG : G.Adj q.1 a.1 := by
    exact ((R.mem_neighborFinset a q).mp hqa).symm
  have hqbG : G.Adj q.1 b.1 := by
    exact ((R.mem_neighborFinset b q).mp hqb).symm
  have hsq : s.1 ≠ q.1 := by
    intro h
    have hqSecond := q.2
    change q.1 ∈ Finset.univ.biUnion (secondLayerBranch G v) at hqSecond
    rcases Finset.mem_biUnion.mp hqSecond with ⟨t, _, hqt⟩
    apply (Finset.mem_sdiff.mp hqt).2
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
    exact Or.inr (by simpa [h] using s.2)
  exact hfree (containsC4_of_two_common
    (Subtype.val_injective.ne hab) hsq hsa hsb hqaG hqbG)

end

end Erdos85
