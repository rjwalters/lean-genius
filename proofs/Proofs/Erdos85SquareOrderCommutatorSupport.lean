import Proofs.Erdos85SquareOrderDefectIncidence
import Proofs.Erdos85NonregularDefectOperator

/-!
# Exact commutator support at square order

In a tight-edge-cover square-order witness every degree is `d` or `d+1`.
The nonregular adjacency/defect commutator therefore has entries in
`{-1,0,1}` and is nonzero exactly on ordered nonadjacent high/low pairs.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Squared commutator entries are the indicator of nonadjacent cross-sector
pairs.  This removes orientation signs and is the pointwise input for an
exact Frobenius-norm count. -/
theorem squareOrder_commutator_entry_sq_eq_crossNonedgeIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (x y : V) :
    let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
    C x y * C x y =
      if (((x ∈ squareOrderHighVertices G d ∧
              y ∉ squareOrderHighVertices G d) ∨
            (x ∉ squareOrderHighVertices G d ∧
              y ∈ squareOrderHighVertices G d)) ∧ ¬ G.Adj x y)
      then 1 else 0 := by
  classical
  dsimp only
  rw [adjMatrix_secondOrderDefect_commutator_apply G hfree x y]
  have hdegree : ∀ z : V,
      z ∈ squareOrderHighVertices G d → G.degree z = d + 1 := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hdegreeLow : ∀ z : V,
      z ∉ squareOrderHighVertices G d → G.degree z = d := by
    intro z hz
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmin hcover hcard z with hzd | hzhigh
    · exact hzd
    · exact (hz (Finset.mem_filter.mpr ⟨by simp, hzhigh⟩)).elim
  by_cases hxy : G.Adj x y
  · simp [hxy, SimpleGraph.adjMatrix_apply]
  · rw [SimpleGraph.adjMatrix_apply, if_neg hxy]
    simp only [sub_zero, mul_one]
    by_cases hx : x ∈ squareOrderHighVertices G d <;>
      by_cases hy : y ∈ squareOrderHighVertices G d
    · simp [hx, hy, hdegree x hx, hdegree y hy]
    · simp [hx, hy, hdegree x hx, hdegreeLow y hy, hxy]
    · simp [hx, hy, hdegreeLow x hx, hdegree y hy, hxy]
    · simp [hx, hy, hdegreeLow x hx, hdegreeLow y hy]

end

end Erdos85
