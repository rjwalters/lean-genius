import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic

/-! A positive strict supersolution makes a nonnegative zero-diagonal matrix's
scalar shift nonsingular. This conditional matrix lemma does not construct
weights from a graph or exclude a q7 profile. -/
namespace Erdos85
open scoped BigOperators Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weighted strict diagonal dominance for a nonnegative defect matrix. -/
theorem weighted_defect_det_ne_zero (D : Matrix V V ℝ) (w : V → ℝ) (q : ℝ)
    (hD : ∀ i j, 0 ≤ D i j) (hdiag : ∀ i, D i i = 0)
    (hw : ∀ i, 0 < w i) (hq : 0 < q)
    (hrow : ∀ i, ∑ j, D i j * w j < q * w i) :
    (q • (1 : Matrix V V ℝ) - D).det ≠ 0 := by
  let B := Matrix.diagonal (fun i => (w i)⁻¹) *
    (q • (1 : Matrix V V ℝ) - D) * Matrix.diagonal w
  have hentry (i j : V) :
      B i j = (w i)⁻¹ * ((q • (1 : Matrix V V ℝ) - D) i j) * w j := by
    simp [B, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hbdiag (i : V) : B i i = q := by
    rw [hentry]
    simp [Matrix.sub_apply, Matrix.smul_apply, hdiag]
    field_simp [ne_of_gt (hw i)]
  have hboff (i j : V) (hij : j ≠ i) :
      ‖B i j‖ = (w i)⁻¹ * (D i j * w j) := by
    rw [hentry]
    have hij' : i ≠ j := Ne.symm hij
    simp [Matrix.sub_apply, Matrix.smul_apply, hij',
      norm_mul, norm_inv, Real.norm_of_nonneg (le_of_lt (hw i)),
      Real.norm_of_nonneg (le_of_lt (hw j)), Real.norm_of_nonneg (hD i j)]
    ring
  have hb : B.det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    rw [hbdiag, Real.norm_of_nonneg (le_of_lt hq)]
    calc
      ∑ j ∈ Finset.univ.erase i, ‖B i j‖ =
          ∑ j ∈ Finset.univ.erase i, (w i)⁻¹ * (D i j * w j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hboff i j (Finset.mem_erase.mp hj).1
      _ = (w i)⁻¹ * (∑ j, D i j * w j) := by
        rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
        simp [hdiag]
      _ < (w i)⁻¹ * (q * w i) :=
        mul_lt_mul_of_pos_left (hrow i) (inv_pos.mpr (hw i))
      _ = q := by field_simp [ne_of_gt (hw i)]
  intro hz
  apply hb
  simp [B, Matrix.det_mul, hz]

/-- The q7 low defect identities give the positive weight `7-t` directly.
This proves nonsingularity of `6I-D`, conditional on those identities. -/
theorem q7_defect_shift_det_ne_zero (D : Matrix V V ℝ) (t : V → ℝ) (h : ℝ)
    (hD : ∀ i j, 0 ≤ D i j) (hdiag : ∀ i, D i i = 0)
    (ht : ∀ i, t i ≤ 3) (hh : 0 < h)
    (hrow : ∀ i, ∑ j, D i j = 6 - t i)
    (hDt : ∀ i, ∑ j, D i j * t j = h - t i) :
    ((6 : ℝ) • (1 : Matrix V V ℝ) - D).det ≠ 0 := by
  apply weighted_defect_det_ne_zero D (fun i => 7 - t i) 6 hD hdiag
  · intro i
    linarith [ht i]
  · norm_num
  · intro i
    calc
      ∑ j, D i j * (7 - t j) = (∑ j, D i j) * 7 - ∑ j, D i j * t j := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = (6 - t i) * 7 - (h - t i) := by rw [hrow, hDt]
      _ < 6 * (7 - t i) := by linarith

end Erdos85
