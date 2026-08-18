import Mathlib

/-! # Shifted eigenvectors for commuting matrix operators

The signed-vector arguments in the Erdős 85 campaign repeatedly use the fact
that a commuting operator preserves an eigenspace, including after adding a
scalar multiple of the original eigenvector.
-/

open Matrix

namespace Erdos85

/-- If `A` and `D` commute and `s` is a `D`-eigenvector, then `A s + κ s`
is a `D`-eigenvector with the same eigenvalue. -/
theorem commuting_mulVec_add_smul_eigen
    {n : Type*} [Fintype n] [DecidableEq n]
    (A D : Matrix n n ℤ) (hcomm : A * D = D * A)
    (s : n → ℤ) (eigenvalue shift : ℤ)
    (hDs : D *ᵥ s = eigenvalue • s) :
    D *ᵥ (A *ᵥ s + shift • s) =
      eigenvalue • (A *ᵥ s + shift • s) := by
  calc
    D *ᵥ (A *ᵥ s + shift • s) =
        D *ᵥ (A *ᵥ s) + shift • (D *ᵥ s) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    _ = (D * A) *ᵥ s + shift • (D *ᵥ s) := by
      rw [Matrix.mulVec_mulVec]
    _ = (A * D) *ᵥ s + shift • (D *ᵥ s) := by rw [← hcomm]
    _ = A *ᵥ (D *ᵥ s) + shift • (D *ᵥ s) := by
      rw [Matrix.mulVec_mulVec]
    _ = A *ᵥ (eigenvalue • s) + shift • (eigenvalue • s) := by rw [hDs]
    _ = eigenvalue • (A *ᵥ s + shift • s) := by
      rw [Matrix.mulVec_smul]
      module

end Erdos85

#print axioms Erdos85.commuting_mulVec_add_smul_eigen
