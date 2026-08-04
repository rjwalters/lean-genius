import Proofs.Erdos85ComponentFactorization

namespace Erdos85

open Polynomial Polynomial.Chebyshev SimpleGraph

noncomputable local instance (n : ℕ) : DecidableRel (pathGraph n).Adj := Classical.decRel _

theorem pathCharmatrix_tail (n : ℕ) :
    (((pathGraph (n + 1)).adjMatrix ℤ).charmatrix.submatrix Fin.succ Fin.succ) =
      ((pathGraph n).adjMatrix ℤ).charmatrix := by
  ext i j
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, pathGraph_adj, Matrix.submatrix_apply]

theorem pathCharmatrix_firstOffdiagMinor (n : ℕ) :
    ((((pathGraph (n + 2)).adjMatrix ℤ).charmatrix.submatrix
      Fin.succ (Fin.succ 0).succAbove).det) =
      -((pathGraph n).adjMatrix ℤ).charpoly := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Matrix.charpoly]
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, pathGraph_adj, Matrix.submatrix_apply]
  congr 1
  ext i j
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, pathGraph_adj, Matrix.submatrix_apply]

theorem pathGraph_charpoly_succ_succ (n : ℕ) :
    ((pathGraph (n + 2)).adjMatrix ℤ).charpoly =
      X * ((pathGraph (n + 1)).adjMatrix ℤ).charpoly -
        ((pathGraph n).adjMatrix ℤ).charpoly := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  have htail :
      ((adjMatrix ℤ (pathGraph (n + 2))).charmatrix.submatrix
        Fin.succ (Fin.succAbove 0)) =
        (adjMatrix ℤ (pathGraph (n + 1))).charmatrix := by
    simpa [Nat.add_assoc] using pathCharmatrix_tail (n + 1)
  rw [htail, pathCharmatrix_firstOffdiagMinor n]
  have hz (x : Fin n) : (0 : Fin (n + 2)) ≠ x.succ.succ := by
    apply Fin.ne_of_val_ne
    simp
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, pathGraph_adj, Matrix.submatrix_apply,
    Matrix.charpoly, hz]
  ring

theorem pathGraph_charpoly_eq_chebyshev_S (n : ℕ) :
    ((pathGraph n).adjMatrix ℤ).charpoly = S ℤ (n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Matrix.charpoly, S_zero]
  | one =>
      simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix,
        Matrix.scalar_apply, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply,
        pathGraph_adj, S_one]
  | more n ih0 ih1 =>
      rw [pathGraph_charpoly_succ_succ n, ih1, ih0]
      simpa using (S_add_two ℤ (n : ℤ)).symm

end Erdos85
