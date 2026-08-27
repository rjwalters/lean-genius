import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-! # Nonsingularity of grounded defect operators

The ordinary defect operator has the form `lapMatrix D₀ + diagonal r`, where
`r` counts incidences with the high vertices.  This file isolates the generic
linear-algebra fact that such a matrix is nonsingular when every connected
component contains a vertex on which `r` is positive.
-/

open Matrix

namespace Erdos85

noncomputable section

open SimpleGraph

theorem det_lapMatrix_add_diagonal_ne_zero_of_grounded
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (r : V → ℝ) (hr : ∀ v, 0 ≤ r v)
    (hground : ∀ v, ∃ w, D.Reachable v w ∧ 0 < r w) :
    (D.lapMatrix ℝ + diagonal r).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hquad : Matrix.toLinearMap₂' ℝ (D.lapMatrix ℝ + diagonal r) x x = 0 := by
    rw [Matrix.toLinearMap₂'_apply', hx, dotProduct_zero]
  have hlap_nonneg : 0 ≤ Matrix.toLinearMap₂' ℝ (D.lapMatrix ℝ) x x := by
    rw [SimpleGraph.lapMatrix_toLinearMap₂' ℝ]
    positivity
  have hdiag_nonneg : 0 ≤ ∑ v, r v * x v * x v := by
    apply Finset.sum_nonneg
    intro v _
    rw [mul_assoc]
    exact mul_nonneg (hr v) (mul_self_nonneg (x v))
  have hsplit : Matrix.toLinearMap₂' ℝ (D.lapMatrix ℝ) x x +
      ∑ v, r v * x v * x v = 0 := by
    simpa [Matrix.toLinearMap₂'_apply', Matrix.add_mulVec, dotProduct_add,
      Matrix.mulVec_diagonal, dotProduct, mul_comm, mul_left_comm, mul_assoc] using hquad
  have hlap : Matrix.toLinearMap₂' ℝ (D.lapMatrix ℝ) x x = 0 := by
    linarith
  have hdiag : ∑ v, r v * x v * x v = 0 := by
    linarith
  have hreach : ∀ i j, D.Reachable i j → x i = x j :=
    (SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable
      (G := D) x).mp hlap
  have hterm : ∀ w, 0 < r w → x w = 0 := by
    intro w hrw
    have hwzero : r w * x w * x w = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun v _ ↦ by
          rw [mul_assoc]
          exact mul_nonneg (hr v) (mul_self_nonneg (x v)))).mp hdiag w (by simp)
    have hwzero' : r w * (x w * x w) = 0 := by simpa [mul_assoc] using hwzero
    rcases mul_eq_zero.mp hwzero' with hr0 | hxx
    · exact (ne_of_gt hrw hr0).elim
    · exact mul_self_eq_zero.mp hxx
  apply hx0
  funext v
  obtain ⟨w, hvw, hrw⟩ := hground v
  exact (hreach v w hvw).trans (hterm w hrw)

theorem isUnit_det_lapMatrix_add_diagonal_of_grounded
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (r : V → ℚ) (hr : ∀ v, 0 ≤ r v)
    (hground : ∀ v, ∃ w, D.Reachable v w ∧ 0 < r w) :
    IsUnit (D.lapMatrix ℚ + diagonal r).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  have hreal := det_lapMatrix_add_diagonal_ne_zero_of_grounded D
    (fun v ↦ (r v : ℝ)) (fun v ↦ by exact_mod_cast hr v)
    (fun v ↦ by
      obtain ⟨w, hvw, hrw⟩ := hground v
      exact ⟨w, hvw, by exact_mod_cast hrw⟩)
  apply hreal
  have hmatrix : (algebraMap ℚ ℝ).mapMatrix (D.lapMatrix ℚ + diagonal r) =
      D.lapMatrix ℝ + diagonal (fun v ↦ (r v : ℝ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix]
    · by_cases hadj : D.Adj i j <;>
        simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
          Matrix.diagonal_apply_ne _ hij, hadj]
  rw [← hmatrix, ← RingHom.map_det, hdet, map_zero]

end

end Erdos85

#print axioms Erdos85.det_lapMatrix_add_diagonal_ne_zero_of_grounded
#print axioms Erdos85.isUnit_det_lapMatrix_add_diagonal_of_grounded
