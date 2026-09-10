import Proofs.Erdos85SevenVertexTriangleCount

/-! The degree-two vertices avoid the unique triangle and form an independent set. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem triangleFree_card_le_defect_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] (x : V) :
    (triangleFreeNeighbors G x).card ≤ (secondOrderDefectGraph G).degree x := by
  rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    secondOrderDefectGraph_neighborFinset]
  exact Finset.card_le_card Finset.subset_union_right

/-- With exactly one triangle, all defect incidences are triangle-free edges. -/
theorem sevenVertex_uniqueTriangle_defect_degree_eq_triangleFree_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (hmax : ∀ x, G.degree x ≤ 3) (hedges : G.edgeFinset.card = 9)
    (htri : (G.cliqueFinset 3).card = 1) (x : V) :
    (secondOrderDefectGraph G).degree x = (triangleFreeNeighbors G x).card := by
  classical
  have hD := sevenVertex_subcubic_nine_edges_sum_defect_degree G hfree hcard hmax hedges
  have hsum : (∑ y : V, (triangleFreeNeighbors G y).card) +
      2 * (∑ y : V, (G.induce (G.neighborSet y)).edgeFinset.card) = 18 := by
    calc
      _ = ∑ y : V, ((triangleFreeNeighbors G y).card +
        2 * (G.induce (G.neighborSet y)).edgeFinset.card) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ y : V, G.degree y := Finset.sum_congr rfl (fun y _ =>
        card_triangleFreeNeighbors_add_two_mul_localEdges G hfree y)
      _ = 18 := by rw [G.sum_degrees_eq_twice_card_edges, hedges]
  rw [sum_localEdges_eq_three_mul_cliques, htri] at hsum
  have hF : (∑ y : V, (triangleFreeNeighbors G y).card) = 12 := by omega
  have heq : (∑ y : V, (triangleFreeNeighbors G y).card) =
      ∑ y : V, (secondOrderDefectGraph G).degree y := by omega
  have hall := (Finset.sum_eq_sum_iff_of_le (fun y (_ : y ∈ (Finset.univ : Finset V)) =>
    triangleFree_card_le_defect_degree G y)).mp heq
  exact (hall x (Finset.mem_univ x)).symm

/-- Every degree-two vertex avoids triangles and has only cubic neighbors. -/
theorem sevenVertex_uniqueTriangle_degree_two_neighbors_cubic
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (hmax : ∀ x, G.degree x ≤ 3) (hedges : G.edgeFinset.card = 9)
    (htri : (G.cliqueFinset 3).card = 1) (x : V) (hx : G.degree x = 2) :
    (G.induce (G.neighborSet x)).edgeFinset.card = 0 ∧
      ∀ y, G.Adj x y → G.degree y = 3 := by
  classical
  have hmin := sevenVertex_subcubic_nine_edges_degree_ge_two G hfree hcard hmax hedges
  have hcons := secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
    G hfree (d := 2) (q := 4) (by omega) hmin (by omega) x
  rw [hx] at hcons
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have hDF := sevenVertex_uniqueTriangle_defect_degree_eq_triangleFree_card
    G hfree hcard hmax hedges htri x
  have hbound : ∀ y ∈ G.neighborFinset x, G.degree y - 2 ≤ 1 := by
    intro y _
    have := hmax y
    omega
  have hNle : neighborDegreeExcess G 2 x ≤ 2 := by
    rw [neighborDegreeExcess_eq_sum_neighborFinset]
    calc
      _ ≤ ∑ _y ∈ G.neighborFinset x, 1 := Finset.sum_le_sum hbound
      _ = 2 := by simp [hx]
  have hN : neighborDegreeExcess G 2 x = 2 := by omega
  refine ⟨by omega, ?_⟩
  have heq : (∑ y ∈ G.neighborFinset x, (G.degree y - 2)) =
      ∑ _y ∈ G.neighborFinset x, 1 := by
    rw [← neighborDegreeExcess_eq_sum_neighborFinset]
    simp [hN, hx]
  have hall := (Finset.sum_eq_sum_iff_of_le hbound).mp heq
  intro y hxy
  have hy := hall y (by simpa using hxy)
  have := hmax y
  omega

/-- The three degree-two vertices are independent and avoid every triangle. -/
theorem sevenVertex_uniqueTriangle_independent_three_avoiding_triangle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (hmax : ∀ x, G.degree x ≤ 3) (hedges : G.edgeFinset.card = 9)
    (htri : (G.cliqueFinset 3).card = 1) :
    let L := Finset.univ.filter (fun x => G.degree x = 2)
    L.card = 3 ∧
      (∀ u ∈ L, ∀ v ∈ L, u ≠ v → ¬ G.Adj u v) ∧
      ∀ t ∈ G.cliqueFinset 3, Disjoint L t := by
  classical
  dsimp only
  refine ⟨(sevenVertex_subcubic_nine_edges_degree_counts G hfree hcard hmax hedges).1, ?_, ?_⟩
  · intro u hu v hv _ huv
    have h := (sevenVertex_uniqueTriangle_degree_two_neighbors_cubic
      G hfree hcard hmax hedges htri u (Finset.mem_filter.mp hu).2).2 v huv
    have := (Finset.mem_filter.mp hv).2
    omega
  · intro t ht
    apply Finset.disjoint_left.mpr
    intro v hv hvt
    have hzero := (sevenVertex_uniqueTriangle_degree_two_neighbors_cubic
      G hfree hcard hmax hedges htri v (Finset.mem_filter.mp hv).2).1
    rw [localEdges_eq_cliques_containing] at hzero
    have hempty := Finset.card_eq_zero.mp hzero
    have hmem : t ∈ (G.cliqueFinset 3).filter (v ∈ ·) := Finset.mem_filter.mpr ⟨ht, hvt⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty t hmem
end Erdos85
#print axioms Erdos85.sevenVertex_uniqueTriangle_defect_degree_eq_triangleFree_card
#print axioms Erdos85.sevenVertex_uniqueTriangle_degree_two_neighbors_cubic
#print axioms Erdos85.sevenVertex_uniqueTriangle_independent_three_avoiding_triangle
