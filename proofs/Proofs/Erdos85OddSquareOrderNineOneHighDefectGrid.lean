import Proofs.Erdos85OddSquareOrderNineOneHighDefectDecomposition

/-! # The two block systems in the q=9 one-high horn

Node: B.3 / GAP B-CLASSIFY.  Defect blocks and ordinary high-root
second-layer branches obey a forbidden-cell law along the matching of the
high root's neighborhood.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- For any C4-free graph, if two branch indices at a root are adjacent,
the defect neighbors of the first index are disjoint from the ordinary
second-layer branch of the second.  Indeed the second index would otherwise
be a common original neighbor. -/
theorem defectNeighbors_disjoint_secondLayerBranch_of_adjacent_indices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (y z : {w : V // w ∈ G.neighborSet v})
    (hyz : G.Adj y.1 z.1) :
    Disjoint (secondOrderDefectGraph G |>.neighborFinset y.1)
      (secondLayerBranch G v z) := by
  classical
  rw [Finset.disjoint_left]
  intro x hDx hxBranch
  have hDadj : (secondOrderDefectGraph G).Adj y.1 x :=
    ((secondOrderDefectGraph G).mem_neighborFinset y.1 x).mp hDx
  have hyx : y.1 ≠ x := (secondOrderDefectGraph G).ne_of_adj hDadj
  have hzero :=
    (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree hyx).mp hDadj
  have hzx : G.Adj z.1 x := by
    have hxNeighbor : x ∈ G.neighborFinset z.1 :=
      (Finset.mem_sdiff.mp hxBranch).1
    exact (G.mem_neighborFinset z.1 x).mp hxNeighbor
  have hzCommon : z.1 ∈ G.neighborFinset y.1 ∩ G.neighborFinset x := by
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset y.1 z.1).mpr hyz,
      (G.mem_neighborFinset x z.1).mpr hzx.symm⟩
  have hpos : 0 < (G.neighborFinset y.1 ∩ G.neighborFinset x).card :=
    Finset.card_pos.mpr ⟨z.1, hzCommon⟩
  omega

/-- In the one-high q=9 horn, choose the unique high root.  Its ten
one-incidence neighbors index both the seven-point defect blocks and the
seven-point ordinary second-layer branches.  The cell formed by a vertex and
its matched partner is empty. -/
theorem squareOrderNine_oneHigh_forbidden_matched_defectBranch_cells
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 1) :
    ∃ v : V,
      squareOrderHighVertices G 9 = {v} ∧
      squareOrderNineLowIncidenceBin G 1 = G.neighborFinset v ∧
      (∀ s : {z : V // z ∈ G.neighborSet v},
        (secondLayerBranch G v s).card = 7) ∧
      secondLayer G v = squareOrderNineLowIncidenceBin G 0 ∧
      ∀ y z : {w : V // w ∈ G.neighborSet v}, G.Adj y.1 z.1 →
        Disjoint
          ((secondOrderDefectGraph G).neighborFinset y.1 ∩
            squareOrderNineLowIncidenceBin G 0)
          (secondLayerBranch G v z) := by
  classical
  obtain ⟨v, hH, hB1, hlocal⟩ :=
    squareOrderNine_oneHigh_bin_one_eq_highRoot_neighbors
      G hfree hmin hcard hp hhigh
  have hvH : v ∈ squareOrderHighVertices G 9 := by rw [hH]; simp
  have hvdeg : G.degree v = 10 := (Finset.mem_filter.mp hvH).2
  have hroot := squareOrder_degree_succ_highRoot_structure
    G hfree (by norm_num) hmin hcard hvdeg
  have hdec := squareOrderNine_oneHigh_defect_decomposition
    G hfree hmin hcover hcard hp hhigh
  dsimp only at hdec
  refine ⟨v, hH, hB1, ?_, ?_, ?_⟩
  · intro s
    have hs := card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
      G (by norm_num) hvdeg hroot.2.1 hlocal s
    norm_num at hs ⊢
    exact hs
  · have hsub : secondLayer G v ⊆ squareOrderNineLowIncidenceBin G 0 := by
      intro x hx
      rw [secondLayer, Finset.mem_biUnion] at hx
      obtain ⟨s, _, hxs⟩ := hx
      have hxClosed := (Finset.mem_sdiff.mp hxs).2
      have hxne : x ≠ v := by
        intro hxv
        subst x
        exact hxClosed (by simp)
      have hxnotN : x ∉ G.neighborFinset v := by
        intro hxN
        exact hxClosed (Finset.mem_insert.mpr (Or.inr hxN))
      refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨by simp, ?_⟩, ?_⟩
      · rw [hH]
        simpa using hxne
      · have hvnot : v ∉ G.neighborFinset x := by
          intro hvx
          apply hxnotN
          exact (G.mem_neighborFinset v x).mpr
            ((G.mem_neighborFinset x v).mp hvx).symm
        simp [squareOrderHighIncidenceCount, hH, hvnot]
    apply Finset.eq_of_subset_of_card_le hsub
    have hsecond := card_secondLayer_eq_mul_sub_two_of_squareOrder_highRoot
      G hfree (by norm_num) hvdeg hroot.2.1 hlocal
    have hb0 := hdec.1
    norm_num at hsecond
    omega
  · intro y z hyz
    rw [Finset.disjoint_left]
    intro x hx hxBranch
    exact (Finset.disjoint_left.mp
      (defectNeighbors_disjoint_secondLayerBranch_of_adjacent_indices
        G hfree v y z hyz)) (Finset.mem_inter.mp hx).1 hxBranch

end

end Erdos85

#print axioms Erdos85.defectNeighbors_disjoint_secondLayerBranch_of_adjacent_indices
#print axioms Erdos85.squareOrderNine_oneHigh_forbidden_matched_defectBranch_cells
