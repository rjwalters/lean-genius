import Mathlib

/-!
# Reducing-subspace bridge for the square-order quadratic sector

The square-order high-difference family spans an adjacency-invariant subspace.
For a symmetric operator, invariance of a subspace automatically gives
invariance of its orthogonal complement.  This small bridge allows the
characteristic-polynomial factorization over a reducing subspace to be applied
without constructing an explicit commuting projection.
-/

open scoped InnerProductSpace

namespace Erdos85

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A symmetric linear operator preserves the orthogonal complement of every
invariant subspace. -/
theorem orthogonal_invariant_of_isSymmetric
    {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric)
    (H : Submodule ℝ V) (hH : ∀ x ∈ H, T x ∈ H) :
    ∀ y ∈ Hᗮ, T y ∈ Hᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro x hx
  rw [← hT x y]
  exact hy (T x) (hH x hx)

end

end Erdos85
