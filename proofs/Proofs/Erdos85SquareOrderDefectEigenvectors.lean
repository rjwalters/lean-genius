import Proofs.Erdos85SquareOrderDefectIncidence
import Proofs.Erdos85SquareOrderHighIncidenceGram

/-!
# Uniform defect eigenvectors from the square-order high sector

Differences of adjacency rows at high vertices are `-1` eigenvectors of the
second-order defect graph.  This is the linear-algebraic form of
`B(D+I)=J`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Multiplying a graph adjacency matrix by an adjacency-row vector counts
mixed common neighbors. -/
theorem adjMatrix_mulVec_adjRow_eq_card_mixed_squareOrder
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
      intro w hw
      by_cases hT : T.Adj y w <;> by_cases hG : G.Adj x w <;>
        simp [SimpleGraph.adjMatrix_apply, hT, hG, T.adj_comm]
    _ = _ := adjMatrix_mul_subgraph_apply_eq_card_mixed G T x y

/-- Difference of adjacency rows at two vertices. -/
def squareOrderHighRowDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x z : V) : V → ℤ :=
  fun y => G.adjMatrix ℤ x y - G.adjMatrix ℤ z y

/-- Distinct high vertices have distinct adjacency rows, so their row
difference is nonzero. -/
theorem squareOrder_highRowDifference_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x z : V}
    (hx : G.degree x = d + 1) (hz : G.degree z = d + 1)
    (hxz : x ≠ z) :
    squareOrderHighRowDifference G x z ≠ 0 := by
  have hcommon := squareOrder_card_common_degree_succ_eq_one
    G hfree hd hmin hcover hcard hx hz hxz
  rcases Finset.card_eq_one.mp hcommon with ⟨y, hy⟩
  have hxcard : (G.neighborFinset x).card = d + 1 := by
    rw [G.card_neighborFinset_eq_degree, hx]
  have hex : ∃ w ∈ G.neighborFinset x, w ≠ y := by
    by_contra hnone
    push Not at hnone
    have hsub : G.neighborFinset x ⊆ {y} := by
      intro w hw
      simp [hnone w hw]
    have hle := Finset.card_le_card hsub
    simp [hxcard] at hle
    omega
  obtain ⟨w, hwx, hwy⟩ := hex
  have hwz : ¬ G.Adj z w := by
    intro hzw
    have hwcommon : w ∈ G.neighborFinset x ∩ G.neighborFinset z := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa [SimpleGraph.mem_neighborFinset] using hwx, hzw⟩
    have : w = y := by simpa [hy] using hwcommon
    exact hwy this
  intro hzero
  have hw := congrFun hzero w
  simp [squareOrderHighRowDifference, SimpleGraph.adjMatrix_apply,
    (by simpa [SimpleGraph.mem_neighborFinset] using hwx : G.Adj x w), hwz] at hw

/-- The high-incidence columns are linearly independent over the integers.
This is the direct algebraic consequence of the nonsingular Gram matrix. -/
theorem squareOrder_highIncidence_columns_linearIndependent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hpositive : 0 < (squareOrderHighVertices G d).card) :
    let B := squareOrderFinsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
      (squareOrderHighVertices G d)
    LinearIndependent ℤ B.col := by
  classical
  let B := squareOrderFinsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
    (squareOrderHighVertices G d)
  let Q := Matrix.transpose B * B
  dsimp only
  have hdet : Q.det ≠ 0 := by
    simpa [Q, B] using squareOrder_highIncidence_gram_det_ne_zero
      G hfree hd hmin hcover hcard hpositive
  have hQ : LinearIndependent ℤ Q.col :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  apply LinearIndependent.of_comp (Matrix.mulVecLin (Matrix.transpose B))
  have heq :
      (Matrix.mulVecLin (Matrix.transpose B)) ∘ B.col = Q.col := by
    funext j
    ext i
    rw [Function.comp_apply, Matrix.mulVecLin_apply]
    change (∑ r, B r i * B r j) = (B.transpose * B) i j
    rw [Matrix.mul_apply]
    rfl
  rw [heq]
  exact hQ

/-- Every difference of two high adjacency rows is a `-1` eigenvector of the
square-order defect adjacency matrix. -/
theorem squareOrder_defect_mulVec_highRowDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x z : V}
    (hx : G.degree x = d + 1) (hz : G.degree z = d + 1) :
    ((secondOrderDefectGraph G).adjMatrix ℤ).mulVec
        (squareOrderHighRowDifference G x z) =
      - squareOrderHighRowDifference G x z := by
  funext y
  let D := secondOrderDefectGraph G
  change (D.adjMatrix ℤ).mulVec
      (fun w => G.adjMatrix ℤ x w - G.adjMatrix ℤ z w) y =
    -(G.adjMatrix ℤ x y - G.adjMatrix ℤ z y)
  have hxm := adjMatrix_mulVec_adjRow_eq_card_mixed_squareOrder G D x y
  have hzm := adjMatrix_mulVec_adjRow_eq_card_mixed_squareOrder G D z y
  simp only [Matrix.mulVec, dotProduct] at hxm hzm ⊢
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hxm, hzm]
  rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard y with hy | hy
  · rw [squareOrder_card_highNeighbors_inter_defectNeighbors
        G hfree hd hmin hcard hx hy,
      squareOrder_card_highNeighbors_inter_defectNeighbors
        G hfree hd hmin hcard hz hy]
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases hxy : G.Adj x y <;> by_cases hzy : G.Adj z y <;>
      simp [hxy, hzy]
  · have hyDdegree : D.degree y = 0 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree hd hmin hcard hy).1
    have hyD : D.neighborFinset y = ∅ := by
      rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hyDdegree]
    have hxy : ¬ G.Adj x y :=
      squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover hx hy
    have hzy : ¬ G.Adj z y :=
      squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover hz hy
    simp [hyD, SimpleGraph.adjMatrix_apply, hxy, hzy]

end

end Erdos85
