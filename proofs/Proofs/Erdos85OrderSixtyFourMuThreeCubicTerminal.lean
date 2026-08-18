import Mathlib

/-! # The rational mu-three cubic terminal at order sixty-four -/

namespace Erdos85

/-- Numbers whose squares are four have cubic sum equal to four times their
linear sum.  In the order-64 spectral application these are exactly the
`α = ±2` lifts above the rational defect eigenvalue `μ = 3`; all case-B
irrational conjugate pairs have already canceled from both odd moments. -/
theorem sum_cube_eq_four_mul_sum_of_sq_eq_four
    {ι : Type*} [Fintype ι] (α : ι → ℤ)
    (hsq : ∀ i, α i ^ 2 = 4) :
    (∑ i, α i ^ 3) = 4 * ∑ i, α i := by
  calc
    (∑ i, α i ^ 3) = ∑ i, 4 * α i := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        α i ^ 3 = α i * (α i ^ 2) := by ring
        _ = α i * 4 := by rw [hsq i]
        _ = 4 * α i := by ring
    _ = 4 * ∑ i, α i := by rw [Finset.mul_sum]

/-- If the only uncanceled odd-moment contributions at order 64 are
`μ=3` lifts, the global linear trace `-8` forces cubic contribution `-32`.
The cubic trace identity then pins the ambient triangle count to `80`. -/
theorem orderSixtyFour_muThree_only_triangleCount_eq_eighty
    {ι : Type*} [Fintype ι] (α : ι → ℤ) (T : ℤ)
    (hsq : ∀ i, α i ^ 2 = 4)
    (hlinear : (∑ i, α i) = -8)
    (hcubic : 6 * T = 512 + ∑ i, α i ^ 3) :
    T = 80 := by
  rw [sum_cube_eq_four_mul_sum_of_sq_eq_four α hsq, hlinear] at hcubic
  norm_num at hcubic ⊢
  omega

end Erdos85
