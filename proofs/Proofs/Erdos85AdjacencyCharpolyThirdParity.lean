import Mathlib

/-!
# Parity of the third adjacency characteristic coefficient

Every odd-order alternating adjacency minor vanishes modulo two.  The
three-by-three case already shows that the third characteristic coefficient
of a simple graph is even; this is the first modular input needed for the
integral residual factor.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem two_dvd_det_adjMatrix_submatrix_card_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : s.card = 3) :
    (2 : ℤ) ∣ ((G.adjMatrix ℤ).submatrix
      (Subtype.val : s → V) (Subtype.val : s → V)).det := by
  classical
  let e : s ≃ Fin 3 := s.equivFinOfCardEq hs
  rw [← Matrix.det_reindex_self e
    ((G.adjMatrix ℤ).submatrix
      (Subtype.val : s → V) (Subtype.val : s → V))]
  rw [Matrix.det_fin_three]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    SimpleGraph.adjMatrix_apply]
  by_cases h₀₁ : G.Adj (e.symm 0).1 (e.symm 1).1 <;>
    by_cases h₀₂ : G.Adj (e.symm 0).1 (e.symm 2).1 <;>
    by_cases h₁₂ : G.Adj (e.symm 1).1 (e.symm 2).1 <;>
    simp [h₀₁, h₀₂, h₁₂, G.adj_comm]

/-- The coefficient three places below the leading term of an integer
adjacency characteristic polynomial is divisible by two. -/
theorem two_dvd_adjMatrix_charpoly_thirdCoeff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) :
    (2 : ℤ) ∣ (G.adjMatrix ℤ).charpoly.coeff (Fintype.card V - 3) := by
  rw [Matrix.charpoly_coeff_eq_sum_minors (G.adjMatrix ℤ) 3 hcard]
  norm_num
  apply Finset.dvd_sum
  intro s hs
  exact two_dvd_det_adjMatrix_submatrix_card_three G s
    (Finset.mem_powersetCard.mp hs).2

end

end Erdos85
