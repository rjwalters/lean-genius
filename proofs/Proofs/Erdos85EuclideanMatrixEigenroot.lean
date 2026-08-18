import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Euclidean matrix eigenvalues are characteristic roots
-/

namespace Erdos85

theorem Matrix.isRoot_charpoly_of_toEuclideanLin_hasEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (lambda : ℝ)
    (h : Module.End.HasEigenvalue A.toEuclideanLin lambda) :
    A.charpoly.IsRoot lambda := by
  have hr :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly A.toEuclideanLin lambda).mp h
  simpa [Matrix.toEuclideanLin_eq_toLin, Matrix.charpoly_toLin] using hr

end Erdos85
