import Proofs.Erdos85DefectPathOwner
import Proofs.Erdos85OddSquareOrderNineThreeHighBinOneDefectTypes
import Proofs.Erdos85LocalTriangleParity
import Proofs.Erdos85SquareOrderLowTriangleDefectIdentity

/-! # Original-edge constraint on the q = 9 three-high ordinary core

Node: B.3 / GAP B-CLASSIFY.  A non-rainbow vertex of the properly
three-colored ordinary defect core has two neighbors of one high color.  Their
shared high root is the exact common-neighbor owner, so the two incident
defect edges cannot both be original edges.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Along a defect two-path through a low bin-one vertex, if the two distinct
endpoints share a high neighbor, at least one path edge is absent from the
original graph. -/
theorem squareOrderNine_binOne_not_both_originalEdges_of_sameHigh_twoPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y z r : V}
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hrH : r ∈ squareOrderHighVertices G 9)
    (hDxy : (secondOrderDefectGraph G).Adj x y)
    (hDyz : (secondOrderDefectGraph G).Adj y z)
    (hxz : x ≠ z)
    (hrx : G.Adj r x) (hrz : G.Adj r z) :
    ¬ (G.Adj x y ∧ G.Adj y z) := by
  have hyLow : y ∈ (Finset.univ : Finset V) \ squareOrderHighVertices G 9 :=
    (Finset.mem_filter.mp hy).1
  have hyr : y ≠ r := by
    intro hyr
    subst y
    exact (Finset.mem_sdiff.mp hyLow).2 hrH
  have hnotDxz : ¬ (secondOrderDefectGraph G).Adj x z :=
    not_secondOrderDefect_adj_of_commonNeighbor
      G hfree hxz hrx.symm hrz.symm
  exact not_both_originalEdges_of_induced_secondOrderDefect_path_of_commonOwner
    G hfree hDxy hDyz hxz hnotDxz hrx hrz hyr

/-- More generally, among any collection of defect neighbors of a bin-one
center that all have one fixed high color, at most one is joined to the
center by an original edge.  Thus original edges form a matching across every
monochromatic fan in the ordinary defect core. -/
theorem squareOrderNine_binOne_sameHigh_defectNeighbors_original_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {y r : V}
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hrH : r ∈ squareOrderHighVertices G 9)
    (S : Finset V)
    (hSdefect : S ⊆ (secondOrderDefectGraph G).neighborFinset y)
    (hScolor : ∀ x ∈ S, G.Adj r x) :
    (S ∩ G.neighborFinset y).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx z hz
  have hxS := (Finset.mem_inter.mp hx).1
  have hzS := (Finset.mem_inter.mp hz).1
  by_contra hxz
  have hDxy : (secondOrderDefectGraph G).Adj x y :=
    ((secondOrderDefectGraph G).mem_neighborFinset y x).mp
      (hSdefect hxS) |>.symm
  have hDyz : (secondOrderDefectGraph G).Adj y z :=
    ((secondOrderDefectGraph G).mem_neighborFinset y z).mp (hSdefect hzS)
  have hnot := squareOrderNine_binOne_not_both_originalEdges_of_sameHigh_twoPath
    G hfree hy hrH hDxy hDyz hxz (hScolor x hxS) (hScolor z hzS)
  exact hnot ⟨
    ((G.mem_neighborFinset y x).mp (Finset.mem_inter.mp hx).2).symm,
    (G.mem_neighborFinset y z).mp (Finset.mem_inter.mp hz).2⟩

/-- Every bin-one vertex has odd original-edge degree inside the second-order
defect graph.  Indeed it is a low vertex of original degree nine, and
`G ∩ D` is the triangle-free-edge graph. -/
theorem squareOrderNine_binOne_triangleFree_degree_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81) {y : V}
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1) :
    Odd (triangleFreeNeighbors G y).card := by
  have hyLow : y ∈ (Finset.univ : Finset V) \ squareOrderHighVertices G 9 :=
    (Finset.mem_filter.mp hy).1
  have hyNotHigh : y ∉ squareOrderHighVertices G 9 :=
    (Finset.mem_sdiff.mp hyLow).2
  have hyDegree : G.degree y = 9 := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard y with hlo | hhi
    · exact hlo
    · exact (hyNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hmod := triangleFreeNeighbors_card_mod_two_eq_vertexDegree G hfree y
  rw [hyDegree] at hmod
  exact Nat.odd_iff.mpr (by omega)

/-- The triangle-corrected two-ball identity leaves exactly four local
original/antipodal profiles at a q=9 bin-one vertex. -/
theorem squareOrderNine_binOne_triangle_defect_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81) {y : V}
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1) :
    ((antipodalNeighbors G y).card = 0 ∧
        (triangleFreeNeighbors G y).card = 7 ∧
        (G.induce (G.neighborSet y)).edgeFinset.card = 1) ∨
      ((antipodalNeighbors G y).card = 2 ∧
        (triangleFreeNeighbors G y).card = 5 ∧
        (G.induce (G.neighborSet y)).edgeFinset.card = 2) ∨
      ((antipodalNeighbors G y).card = 4 ∧
        (triangleFreeNeighbors G y).card = 3 ∧
        (G.induce (G.neighborSet y)).edgeFinset.card = 3) ∨
      ((antipodalNeighbors G y).card = 6 ∧
        (triangleFreeNeighbors G y).card = 1 ∧
        (G.induce (G.neighborSet y)).edgeFinset.card = 4) := by
  have hyLow : y ∈ (Finset.univ : Finset V) \ squareOrderHighVertices G 9 :=
    (Finset.mem_filter.mp hy).1
  have hyNotHigh : y ∉ squareOrderHighVertices G 9 :=
    (Finset.mem_sdiff.mp hyLow).2
  have hyDegree : G.degree y = 9 := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard y with hlo | hhi
    · exact hlo
    · exact (hyNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hinc : squareOrderHighIncidenceCount G 9 y = 1 :=
    (Finset.mem_filter.mp hy).2
  have hdefect := squareOrder_defectDegree_add_highIncidence_eq_pred
    G hfree (by norm_num) hmin hcover hcard hyDegree
  rw [hinc] at hdefect
  have hsplit := congrArg Finset.card
    (secondOrderDefectGraph_neighborFinset G y)
  rw [Finset.card_union_of_disjoint
    (disjoint_antipodal_triangleFreeNeighbors G y),
    (secondOrderDefectGraph G).card_neighborFinset_eq_degree] at hsplit
  have htriangle :=
    squareOrder_low_antipodal_add_highIncidence_add_one_eq_two_mul_localEdges
      G hfree (by norm_num) hmin hcover hcard hyDegree
  rw [hinc] at htriangle
  omega

/-- A bin-one vertex and its high neighbor lie in exactly one triangle.  This
is the forced high-root matching edge inside the bin-one vertex's local
triangle census. -/
theorem squareOrderNine_binOne_highRoot_commonNeighbor_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81) {y r : V}
    (_hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hrH : r ∈ squareOrderHighVertices G 9)
    (hry : G.Adj r y) :
    (G.neighborFinset r ∩ G.neighborFinset y).card = 1 := by
  have hrDegree : G.degree r = 10 := (Finset.mem_filter.mp hrH).2
  have hyMem : y ∈ G.neighborSet r := hry
  have hlocal :=
    (squareOrder_degree_succ_highRoot_structure
      G hfree (by norm_num) hmin hcard hrDegree).2.2 ⟨y, hyMem⟩
  rw [degree_induce_neighborSet_eq_card_common] at hlocal
  simpa [Finset.inter_comm] using hlocal

/-- Deleting the high root from the local neighborhood graph removes exactly
one edge.  The residual edge count is therefore the exact number of all-low
triangles through the bin-one vertex. -/
theorem squareOrderNine_binOne_residualLocalEdges_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81) {y r : V}
    (_hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hrH : r ∈ squareOrderHighVertices G 9)
    (hry : G.Adj r y) :
    let H := G.induce (G.neighborSet y)
    let r' : {z : V // z ∈ G.neighborSet y} := ⟨r, hry.symm⟩
    (H.deleteIncidenceSet r').edgeFinset.card + 1 = H.edgeFinset.card := by
  dsimp only
  let H := G.induce (G.neighborSet y)
  let r' : {z : V // z ∈ G.neighborSet y} := ⟨r, hry.symm⟩
  change (H.deleteIncidenceSet r').edgeFinset.card + 1 = H.edgeFinset.card
  have hlocal : H.degree r' = 1 := by
    rw [degree_induce_neighborSet_eq_card_common]
    simpa [Finset.inter_comm] using
      squareOrderNine_binOne_highRoot_commonNeighbor_card_eq_one
        G hfree hmin hcard _hy hrH hry
  have hdelete := H.card_edgeFinset_deleteIncidenceSet r'
  have hle := H.degree_le_card_edgeFinset r'
  rw [hlocal] at hdelete hle
  omega

end

end Erdos85

#print axioms Erdos85.squareOrderNine_binOne_not_both_originalEdges_of_sameHigh_twoPath
#print axioms Erdos85.squareOrderNine_binOne_sameHigh_defectNeighbors_original_card_le_one
#print axioms Erdos85.squareOrderNine_binOne_triangleFree_degree_odd
#print axioms Erdos85.squareOrderNine_binOne_triangle_defect_profile
#print axioms Erdos85.squareOrderNine_binOne_highRoot_commonNeighbor_card_eq_one
#print axioms Erdos85.squareOrderNine_binOne_residualLocalEdges_add_one
