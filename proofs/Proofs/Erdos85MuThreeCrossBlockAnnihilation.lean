import Mathlib

/-! # Norm saturation for the order-64 mu-three cross blocks -/

namespace Erdos85

/-- Suppose `x` is supported on a coordinate sector `S`, the coordinates of
`y` inside `S` already equal `-2x`, and `y` has the norm forced by an
operator satisfying `A²x = 4x`.  The inside coordinates exhaust that norm,
so every coordinate of `y` outside `S` vanishes.

In the order-64 application, `x` is a component-supported `μ=3` defect
eigenvector and `y = A x`.  This is the elementary norm-saturation step that
turns a one-dimensional local trace `-2` into annihilation by all ambient
cross-component blocks. -/
theorem outside_eq_zero_of_inside_eq_neg_two_and_sq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i, i ∉ S → x i = 0)
    (hy : ∀ i ∈ S, y i = -2 * x i)
    (hnorm : (∑ i, y i ^ 2) = 4 * ∑ i, x i ^ 2) :
    ∀ i, i ∉ S → y i = 0 := by
  classical
  have hxsum : (∑ i, x i ^ 2) = ∑ i ∈ S, x i ^ 2 := by
    exact (Finset.sum_subset (Finset.subset_univ S)
      (fun i _ hi ↦ by rw [hx i hi]; simp)).symm
  have hinside : (∑ i ∈ S, y i ^ 2) = 4 * ∑ i ∈ S, x i ^ 2 := by
    calc
      (∑ i ∈ S, y i ^ 2) = ∑ i ∈ S, 4 * x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hy i hi]
        ring
      _ = 4 * ∑ i ∈ S, x i ^ 2 := by rw [Finset.mul_sum]
  have hsplit :
      (∑ i ∈ (Finset.univ \ S), y i ^ 2) + (∑ i ∈ S, y i ^ 2) =
        ∑ i, y i ^ 2 := by
    exact Finset.sum_sdiff (Finset.subset_univ S)
  have houtsum : ∑ i ∈ (Finset.univ \ S), y i ^ 2 = 0 := by
    rw [hxsum] at hnorm
    nlinarith
  intro i hi
  have hi' : i ∈ (Finset.univ \ S) := by simp [hi]
  have hsq : y i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ sq_nonneg (y j))).mp houtsum i hi'
  nlinarith [sq_nonneg (y i)]

end Erdos85
