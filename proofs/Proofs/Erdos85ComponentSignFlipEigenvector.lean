import Mathlib

/-! # Sign flips on graph connected components preserve eigenvectors -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Negating an adjacency eigenvector on one connected component preserves
its eigenvalue. -/
theorem connectedComponent_signFlip_adjMatrix_eigenvector
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (b : H.ConnectedComponent) (s : X → ℤ) (lambda : ℤ)
    (hs : (H.adjMatrix ℤ).mulVec s = lambda • s) :
    let t : X → ℤ := fun x ↦
      if H.connectedComponentMk x = b then -s x else s x
    (H.adjMatrix ℤ).mulVec t = lambda • t := by
  classical
  dsimp only
  funext x
  have hsx := congrFun hs x
  rw [H.adjMatrix_mulVec_apply] at hsx ⊢
  by_cases hx : H.connectedComponentMk x = b
  · have hsum : ∑ y ∈ H.neighborFinset x,
        (if H.connectedComponentMk y = b then -s y else s y) =
        -∑ y ∈ H.neighborFinset x, s y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      have hxy := (H.mem_neighborFinset x y).mp hy
      have hyx := ConnectedComponent.connectedComponentMk_eq_of_adj hxy
      simp [hyx.symm.trans hx]
    rw [hsum, hsx]
    simp [hx]
  · have hsum : ∑ y ∈ H.neighborFinset x,
        (if H.connectedComponentMk y = b then -s y else s y) =
        ∑ y ∈ H.neighborFinset x, s y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hxy := (H.mem_neighborFinset x y).mp hy
      have hyx := ConnectedComponent.connectedComponentMk_eq_of_adj hxy
      have hy : H.connectedComponentMk y ≠ b := by
        intro hyb
        exact hx (hyx.trans hyb)
      simp [hy]
    rw [hsum, hsx]
    simp [hx]

end


end Erdos85

#print axioms Erdos85.connectedComponent_signFlip_adjMatrix_eigenvector
