import Proofs.Erdos85PositiveExcessOne

/-!
# Operator package for odd excess one

In an odd-degree regular `C₄`-free graph of order `d(d-1)+4`, the
triangle-free-edge color is a perfect matching.  This file records the
matrix consequences independently of any congruence assumption: its
adjacency matrix is an involution, its mixed trace with the original
adjacency matrix is the number of vertices, and the combined defect matrix
is the sum of the antipodal two-factor and matching matrices.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The triangle-free-edge matching matrix is an involution in every
odd-degree excess-one graph. -/
theorem triangleFreeEdgeGraph_adjMatrix_sq_eq_one_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    (triangleFreeEdgeGraph G).adjMatrix ℤ *
        (triangleFreeEdgeGraph G).adjMatrix ℤ = (1 : Matrix V V ℤ) := by
  apply adjMatrix_sq_eq_one_of_degree_one
  exact triangleFreeEdgeGraph_degree_eq_one_of_odd_excessOne
    G hfree hd hodd hreg hcard

/-- The matching consists of original edges, one at every vertex, so its
mixed trace with the original adjacency matrix is `|V|`. -/
theorem trace_adjMatrix_mul_triangleFreeEdgeGraph_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    Matrix.trace (G.adjMatrix ℤ *
      (triangleFreeEdgeGraph G).adjMatrix ℤ) = Fintype.card V := by
  rw [Matrix.trace]
  have hentry : ∀ x : V,
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x x = 1 := by
    intro x
    rw [(triangleFreeEdgeGraph G).mul_adjMatrix_apply]
    rw [triangleFreeEdgeGraph_neighborFinset]
    calc
      (∑ z ∈ triangleFreeNeighbors G x, G.adjMatrix ℤ x z) =
          ∑ _z ∈ triangleFreeNeighbors G x, 1 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [SimpleGraph.adjMatrix_apply, if_pos]
        exact ((mem_triangleFreeNeighbors G x z).mp hz).1
      _ = (triangleFreeNeighbors G x).card := by simp
      _ = 1 := by
        exact_mod_cast excessOne_triangleFreeNeighbors_card_eq_one_of_odd
          G hfree hd hodd hreg hcard x
  calc
    (∑ x : V, (G.adjMatrix ℤ *
        (triangleFreeEdgeGraph G).adjMatrix ℤ) x x) =
        ∑ _x : V, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hentry x
    _ = Fintype.card V := by simp

/-- The combined defect adjacency matrix splits entrywise as the sum of the
antipodal two-factor matrix and the triangle-free matching matrix. -/
theorem secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    (secondOrderDefectGraph G).adjMatrix ℤ =
      (antipodalGraph G).adjMatrix ℤ +
        (triangleFreeEdgeGraph G).adjMatrix ℤ := by
  classical
  have adjMatrix_sup_of_edge_disjoint
      (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
      (hdisj : ∀ x y, H.Adj x y → K.Adj x y → False) :
      (H ⊔ K).adjMatrix ℤ = H.adjMatrix ℤ + K.adjMatrix ℤ := by
    ext x y
    rw [Matrix.add_apply, SimpleGraph.adjMatrix_apply,
      SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
    change (if H.Adj x y ∨ K.Adj x y then 1 else 0) =
      (if H.Adj x y then 1 else 0) + (if K.Adj x y then 1 else 0)
    by_cases hh : H.Adj x y
    · have hk : ¬K.Adj x y := fun hk => hdisj x y hh hk
      simp [hh, hk]
    · by_cases hk : K.Adj x y <;> simp [hh, hk]
  have hmat := adjMatrix_sup_of_edge_disjoint
    (antipodalGraph G) (triangleFreeEdgeGraph G) (by
      intro x y ha hm
      exact (Finset.disjoint_left.mp
        (disjoint_antipodal_triangleFreeNeighbors G x))
          ((antipodalGraph_adj G x y).mp ha)
          ((triangleFreeEdgeGraph_adj G x y).mp hm))
  ext x y
  convert congrFun (congrFun hmat x) y using 1
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  by_cases h : (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y <;>
    simp [secondOrderDefectGraph, h]

end

end Erdos85
