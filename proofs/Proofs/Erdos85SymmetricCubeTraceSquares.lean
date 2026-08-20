import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Sixth trace as the square mass of the adjacency cube -/

open Matrix

namespace Erdos85

/-- For a symmetric matrix, the sixth trace is the entrywise square mass of
its cube.  This is the matrix bridge between spectral sixth-moment bounds and
row-by-row cubic walk ledgers. -/
theorem trace_pow_six_eq_sum_cube_apply_sq
    {R X : Type*} [CommRing R] [Fintype X] [DecidableEq X]
    (A : Matrix X X R) (hA : A.IsSymm) :
    Matrix.trace (A ^ 6) = ∑ i, ∑ j, (A ^ 3) i j ^ 2 := by
  have hcube : (A ^ 3).IsSymm := hA.pow 3
  rw [show A ^ 6 = A ^ 3 * A ^ 3 by
    rw [← pow_add]]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : (A ^ 3) j i = (A ^ 3) i j :=
    congrFun (congrFun hcube.eq i) j
  rw [hij]
  ring

end Erdos85

#print axioms Erdos85.trace_pow_six_eq_sum_cube_apply_sq
