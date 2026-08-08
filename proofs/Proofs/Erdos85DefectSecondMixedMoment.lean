import Proofs.Erdos85PositiveExcessOneOperator

/-!
# The second adjacency--defect mixed moment

Write the second-order defect graph as `D = C + T`, where `C` is the
antipodal graph and `T` is the triangle-free-edge graph.  In the mixed
moment `tr(A D²)`, all color words except `A C²` vanish.  Indeed, an
antipodal edge has no common neighbor in the original graph, while a
triangle-free edge cannot lie in a triangle.

This reduction is independent of the excess and turns the next spectral
moment into a purely antipodal service count.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An original edge, an antipodal edge, and a triangle-free edge cannot
form a triangle. -/
theorem false_of_adj_antipodal_triangleFree_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V} (hxy : G.Adj x y)
    (hyz : (antipodalGraph G).Adj y z)
    (hzx : (triangleFreeEdgeGraph G).Adj z x) : False := by
  have hxz : G.Adj x z :=
    ((mem_triangleFreeNeighbors G z x).mp hzx).1.symm
  have hzero : G.neighborFinset y ∩ G.neighborFinset z = ∅ :=
    Finset.card_eq_zero.mp
      ((mem_antipodalNeighbors G y z).mp
        ((antipodalGraph_adj G y z).mp hyz)).2.2
  have hxmem : x ∈ G.neighborFinset y ∩ G.neighborFinset z := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxy.symm, hxz.symm⟩
  rw [hzero] at hxmem
  exact Finset.notMem_empty x hxmem

/-- An original edge cannot close two triangle-free edges to a triangle. -/
theorem false_of_adj_two_triangleFree_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V} (hxy : G.Adj x y)
    (hyz : (triangleFreeEdgeGraph G).Adj y z)
    (hzx : (triangleFreeEdgeGraph G).Adj z x) : False := by
  have hzero : G.neighborFinset y ∩ G.neighborFinset z = ∅ :=
    Finset.card_eq_zero.mp
      ((mem_triangleFreeNeighbors G y z).mp hyz).2
  have hxz : G.Adj x z :=
    ((mem_triangleFreeNeighbors G z x).mp hzx).1.symm
  have hxmem : x ∈ G.neighborFinset y ∩ G.neighborFinset z := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxy.symm, hxz.symm⟩
  rw [hzero] at hxmem
  exact Finset.notMem_empty x hxmem

/-- Matrix form of the two forbidden colored triangles. -/
theorem trace_adj_mul_antipodal_mul_triangleFree_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix.trace
      (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ *
        (triangleFreeEdgeGraph G).adjMatrix ℤ) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro x _
  change (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ *
    (triangleFreeEdgeGraph G).adjMatrix ℤ) x x = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hzx : (triangleFreeEdgeGraph G).Adj z x
  · rw [SimpleGraph.adjMatrix_apply, if_pos hzx, mul_one]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : G.Adj x y
    · by_cases hyz : (antipodalGraph G).Adj y z
      · exact (false_of_adj_antipodal_triangleFree_triangle
          G hxy hyz hzx).elim
      · have hc : (antipodalGraph G).adjMatrix ℤ y z = 0 := by
          rw [SimpleGraph.adjMatrix_apply, if_neg hyz]
        rw [hc, mul_zero]
    · have ha : G.adjMatrix ℤ x y = 0 := by
        rw [SimpleGraph.adjMatrix_apply, if_neg hxy]
      rw [ha, zero_mul]
  · have ht : (triangleFreeEdgeGraph G).adjMatrix ℤ z x = 0 := by
      rw [SimpleGraph.adjMatrix_apply, if_neg hzx]
    rw [ht, mul_zero]

/-- The reversed mixed color word vanishes as well. -/
theorem trace_adj_mul_triangleFree_mul_antipodal_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix.trace
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro x _
  change (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ *
    (antipodalGraph G).adjMatrix ℤ) x x = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hzx : (antipodalGraph G).Adj z x
  · rw [SimpleGraph.adjMatrix_apply, if_pos hzx, mul_one]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : G.Adj x y
    · by_cases hyz : (triangleFreeEdgeGraph G).Adj y z
      · exact (false_of_adj_antipodal_triangleFree_triangle
          G hxy.symm hzx.symm hyz.symm).elim
      · have ht : (triangleFreeEdgeGraph G).adjMatrix ℤ y z = 0 := by
          rw [SimpleGraph.adjMatrix_apply, if_neg hyz]
        rw [ht, mul_zero]
    · have ha : G.adjMatrix ℤ x y = 0 := by
        rw [SimpleGraph.adjMatrix_apply, if_neg hxy]
      rw [ha, zero_mul]
  · have hc : (antipodalGraph G).adjMatrix ℤ z x = 0 := by
      rw [SimpleGraph.adjMatrix_apply, if_neg hzx]
    rw [hc, mul_zero]

/-- The word `A T²` also has zero trace. -/
theorem trace_adj_mul_triangleFree_sq_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix.trace
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ *
        (triangleFreeEdgeGraph G).adjMatrix ℤ) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro x _
  change (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ *
    (triangleFreeEdgeGraph G).adjMatrix ℤ) x x = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hzx : (triangleFreeEdgeGraph G).Adj z x
  · rw [SimpleGraph.adjMatrix_apply, if_pos hzx, mul_one]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : G.Adj x y
    · by_cases hyz : (triangleFreeEdgeGraph G).Adj y z
      · exact (false_of_adj_two_triangleFree_triangle G hxy hyz hzx).elim
      · have ht : (triangleFreeEdgeGraph G).adjMatrix ℤ y z = 0 := by
          rw [SimpleGraph.adjMatrix_apply, if_neg hyz]
        rw [ht, mul_zero]
    · have ha : G.adjMatrix ℤ x y = 0 := by
        rw [SimpleGraph.adjMatrix_apply, if_neg hxy]
      rw [ha, zero_mul]
  · have ht : (triangleFreeEdgeGraph G).adjMatrix ℤ z x = 0 := by
      rw [SimpleGraph.adjMatrix_apply, if_neg hzx]
    rw [ht, mul_zero]

/-- **Second mixed-moment reduction.**  The moment `tr(A D²)` counts only
two-step antipodal services across original edges. -/
theorem trace_adj_mul_secondOrderDefect_sq_eq_antipodal_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    Matrix.trace (A * D * D) = Matrix.trace (A * C * C) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  have hD : D = C + T :=
    secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G
  have hACT : Matrix.trace (A * C * T) = 0 := by
    exact trace_adj_mul_antipodal_mul_triangleFree_eq_zero G
  have hATC : Matrix.trace (A * T * C) = 0 := by
    exact trace_adj_mul_triangleFree_mul_antipodal_eq_zero G
  have hATT : Matrix.trace (A * T * T) = 0 := by
    exact trace_adj_mul_triangleFree_sq_eq_zero G
  have hexpand :
      A * D * D = A * C * C + A * C * T + A * T * C + A * T * T := by
    rw [hD]
    noncomm_ring
  rw [hexpand, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    hACT, hATC, hATT]
  simp [A, C]

end

end Erdos85
