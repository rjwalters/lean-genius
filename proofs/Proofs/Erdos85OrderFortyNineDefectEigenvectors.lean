import Proofs.Erdos85OrderFortyNineDefectIncidence

/-!
# Defect eigenvectors from the order-49 high sector

Differences of high adjacency rows are `-1` eigenvectors of the second-order
defect graph.  This is the linear-algebraic content of `B (D + I) = J`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Multiplying a graph adjacency matrix by an adjacency-row vector counts
the corresponding mixed common neighbors. -/
theorem adjMatrix_mulVec_adjRow_eq_card_mixed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (x y : V) :
    (T.adjMatrix ℤ).mulVec (fun w => G.adjMatrix ℤ x w) y =
      ((G.neighborFinset x ∩ T.neighborFinset y).card : ℤ) := by
  calc
    (T.adjMatrix ℤ).mulVec (fun w => G.adjMatrix ℤ x w) y =
        (G.adjMatrix ℤ * T.adjMatrix ℤ) x y := by
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hT : T.Adj y w <;> by_cases hG : G.Adj x w <;>
        simp [SimpleGraph.adjMatrix_apply, hT, hG, T.adj_comm]
    _ = _ := adjMatrix_mul_subgraph_apply_eq_card_mixed G T x y

/-- Difference of the adjacency rows at two vertices. -/
def orderFortyNineHighRowDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x z : V) : V → ℤ :=
  fun y => G.adjMatrix ℤ x y - G.adjMatrix ℤ z y

/-- Distinct high vertices yield a nonzero row-difference vector. -/
theorem orderFortyNine_highRowDifference_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x z : V}
    (hx : G.degree x = 8) (hz : G.degree z = 8) (hxz : x ≠ z) :
    orderFortyNineHighRowDifference G x z ≠ 0 := by
  have hcommon := orderFortyNine_card_common_degreeEight_eq_one
    G hfree hmin hcard hx hz hxz
  rcases Finset.card_eq_one.mp hcommon with ⟨y, hy⟩
  have hyx : G.Adj x y := by
    have : y ∈ G.neighborFinset x ∩ G.neighborFinset z := by simp [hy]
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp this).1
  have hyz : G.Adj z y := by
    have : y ∈ G.neighborFinset x ∩ G.neighborFinset z := by simp [hy]
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp this).2
  -- Evaluate instead at `x`: the `z` row sees no high--high edge, while
  -- looplessness kills the `x` entry.  A common neighbor is not useful here,
  -- so use any neighbor of `x` outside the unique common one.
  have hxcard : (G.neighborFinset x).card = 8 := by
    rw [G.card_neighborFinset_eq_degree, hx]
  have hex : ∃ w ∈ G.neighborFinset x, w ≠ y := by
    by_contra hnone
    push_neg at hnone
    have hsub : G.neighborFinset x ⊆ {y} := by
      intro w hw
      simp [hnone w hw]
    have := Finset.card_le_card hsub
    simp at this
    omega
  rcases hex with ⟨w, hwx, hwy⟩
  have hwz : ¬ G.Adj z w := by
    intro hzw
    have hwcommon : w ∈ G.neighborFinset x ∩ G.neighborFinset z := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa [SimpleGraph.mem_neighborFinset] using hwx, hzw⟩
    have : w = y := by simpa [hy] using hwcommon
    exact hwy this
  intro hzero
  have hw := congrFun hzero w
  simp [orderFortyNineHighRowDifference, SimpleGraph.adjMatrix_apply,
    (by simpa [SimpleGraph.mem_neighborFinset] using hwx : G.Adj x w), hwz] at hw

/-- Every high-row difference is a `-1` eigenvector of the defect adjacency
matrix. -/
theorem orderFortyNine_defect_mulVec_highRowDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x z : V}
    (hx : G.degree x = 8) (hz : G.degree z = 8) :
    ((secondOrderDefectGraph G).adjMatrix ℤ).mulVec
        (orderFortyNineHighRowDifference G x z) =
      - orderFortyNineHighRowDifference G x z := by
  funext y
  change ((secondOrderDefectGraph G).adjMatrix ℤ).mulVec
      (fun w => G.adjMatrix ℤ x w - G.adjMatrix ℤ z w) y =
    -(G.adjMatrix ℤ x y - G.adjMatrix ℤ z y)
  have hxm := adjMatrix_mulVec_adjRow_eq_card_mixed
    G (secondOrderDefectGraph G) x y
  have hzm := adjMatrix_mulVec_adjRow_eq_card_mixed
    G (secondOrderDefectGraph G) z y
  simp only [Matrix.mulVec, dotProduct] at hxm hzm ⊢
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hxm, hzm]
  rcases orderFortyNine_degree_eq_seven_or_eight
    G hfree hmin hcard y with hy | hy
  · rw [orderFortyNine_card_highNeighbors_inter_defectNeighbors
        G hfree hmin hcard hx hy,
      orderFortyNine_card_highNeighbors_inter_defectNeighbors
        G hfree hmin hcard hz hy]
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases hxy : G.Adj x y <;> by_cases hzy : G.Adj z y <;>
      simp [hxy, hzy]
  · have hyD : (secondOrderDefectGraph G).neighborFinset y = ∅ := by
      rw [← Finset.card_eq_zero,
        (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
        (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
          G hfree hmin hcard hy).1]
    have hxy : ¬ G.Adj x y :=
      orderFortyNine_not_adj_degreeEight_degreeEight
        G hfree hmin hcard hx hy
    have hzy : ¬ G.Adj z y :=
      orderFortyNine_not_adj_degreeEight_degreeEight
        G hfree hmin hcard hz hy
    simp [hyD, SimpleGraph.adjMatrix_apply, hxy, hzy]

end

end Erdos85
