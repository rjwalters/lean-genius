import Mathlib

/-!
# Symmetric fractional-cover inequalities

The localized order-49 obstruction is a fractional `f`-factor cut.  Degree
equations contribute demand at selected vertices, while common-neighbor caps
contribute weighted row covers.  Because the unknown edge matrix is symmetric,
a cap centered at either endpoint may cover the same edge variable.

This file packages the general summation argument.  A concrete terminal only
needs to supply the small dual cover and show that its total capacity is below
its selected degree demand.
-/

namespace Erdos85

noncomputable section

/-- Total coefficient assigned by cover rows centered at `v` to the variable
joining `v` to `w`. -/
def centeredCoverCoefficient
    {V I : Type*} [Fintype I] [DecidableEq V]
    (center : I → V) (weight : I → ℚ) (row : I → V → ℚ)
    (v w : V) : ℚ :=
  ∑ i : I, (if center i = v then weight i * row i w else 0)

/-- A pointwise symmetric dual cover bounds the corresponding weighted degree
demand by the sum of the row capacities. -/
theorem symmetricFractionalCover_degree_le_capacity
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (x : V → V → ℚ) (degreeDemand : V → ℚ)
    (center : I → V) (row : I → V → ℚ)
    (capacity weight : I → ℚ)
    (alpha : V → ℚ)
    (hsymm : ∀ v w, x v w = x w v)
    (hnonneg : ∀ v w, 0 ≤ x v w)
    (hdegree : ∀ v, (∑ w : V, x v w) = degreeDemand v)
    (hweight : ∀ i, 0 ≤ weight i)
    (hcap : ∀ i, (∑ w : V, row i w * x (center i) w) ≤ capacity i)
    (hcover : ∀ v w,
      alpha v + alpha w ≤
        centeredCoverCoefficient center weight row v w +
        centeredCoverCoefficient center weight row w v) :
    (∑ v : V, alpha v * degreeDemand v) ≤
      ∑ i : I, weight i * capacity i := by
  have hcapSum :
      (∑ i : I, weight i *
        (∑ w : V, row i w * x (center i) w)) ≤
        ∑ i : I, weight i * capacity i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hcap i) (hweight i)
  have hpoint (v w : V) :
      (alpha v + alpha w) * x v w ≤
        (centeredCoverCoefficient center weight row v w +
          centeredCoverCoefficient center weight row w v) * x v w :=
    mul_le_mul_of_nonneg_right (hcover v w) (hnonneg v w)
  have hdouble :
      (∑ v : V, ∑ w : V, (alpha v + alpha w) * x v w) ≤
        ∑ v : V, ∑ w : V,
          (centeredCoverCoefficient center weight row v w +
            centeredCoverCoefficient center weight row w v) * x v w := by
    apply Finset.sum_le_sum
    intro v _
    apply Finset.sum_le_sum
    intro w _
    exact hpoint v w
  have hdegreeDouble :
      (∑ v : V, ∑ w : V, (alpha v + alpha w) * x v w) =
        2 * ∑ v : V, alpha v * degreeDemand v := by
    calc
      (∑ v : V, ∑ w : V, (alpha v + alpha w) * x v w) =
          (∑ v : V, ∑ w : V, alpha v * x v w) +
          ∑ v : V, ∑ w : V, alpha w * x v w := by
        simp_rw [add_mul, Finset.sum_add_distrib]
      _ = (∑ v : V, alpha v * ∑ w : V, x v w) +
          ∑ w : V, alpha w * ∑ v : V, x w v := by
        congr 1
        · apply Finset.sum_congr rfl
          intro v _
          rw [Finset.mul_sum]
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro w _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          rw [hsymm v w]
      _ = 2 * ∑ v : V, alpha v * degreeDemand v := by
        simp_rw [hdegree]
        ring
  have hcoverDouble :
      (∑ v : V, ∑ w : V,
        (centeredCoverCoefficient center weight row v w +
          centeredCoverCoefficient center weight row w v) * x v w) =
        2 * ∑ i : I, weight i *
          (∑ w : V, row i w * x (center i) w) := by
    simp only [centeredCoverCoefficient]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [show
      (∑ v : V, ∑ w : V,
        (∑ i : I, if center i = w then weight i * row i v else 0) * x v w) =
      ∑ v : V, ∑ w : V,
        (∑ i : I, if center i = v then weight i * row i w else 0) * x v w by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      rw [hsymm w v]]
    rw [← two_mul]
    congr 1
    simp_rw [Finset.sum_mul]
    rw [show
      (∑ v : V, ∑ w : V, ∑ i : I,
        (if center i = v then weight i * row i w else 0) * x v w) =
      ∑ v : V, ∑ i : I, ∑ w : V,
        (if center i = v then weight i * row i w else 0) * x v w by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp [eq_comm]
    ring
  rw [hdegreeDouble, hcoverDouble] at hdouble
  have hmain :
      (∑ v : V, alpha v * degreeDemand v) ≤
        ∑ i : I, weight i *
          (∑ w : V, row i w * x (center i) w) := by
    linarith
  calc
    (∑ v : V, alpha v * degreeDemand v) ≤ _ := hmain
    _ ≤ ∑ i : I, weight i * capacity i := hcapSum

/-- Strictly insufficient total cover capacity is impossible. -/
theorem false_of_symmetricFractionalCover_capacity_lt_degree
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (x : V → V → ℚ) (degreeDemand : V → ℚ)
    (center : I → V) (row : I → V → ℚ)
    (capacity weight : I → ℚ) (alpha : V → ℚ)
    (hsymm : ∀ v w, x v w = x w v)
    (hnonneg : ∀ v w, 0 ≤ x v w)
    (hdegree : ∀ v, (∑ w : V, x v w) = degreeDemand v)
    (hweight : ∀ i, 0 ≤ weight i)
    (hcap : ∀ i, (∑ w : V, row i w * x (center i) w) ≤ capacity i)
    (hcover : ∀ v w,
      alpha v + alpha w ≤
        centeredCoverCoefficient center weight row v w +
        centeredCoverCoefficient center weight row w v)
    (hstrict : (∑ i : I, weight i * capacity i) <
      ∑ v : V, alpha v * degreeDemand v) : False := by
  have hle := symmetricFractionalCover_degree_le_capacity
    x degreeDemand center row capacity weight alpha hsymm hnonneg
    hdegree hweight hcap hcover
  exact (not_lt_of_ge hle) hstrict

end

end Erdos85

#print axioms Erdos85.symmetricFractionalCover_degree_le_capacity
#print axioms Erdos85.false_of_symmetricFractionalCover_capacity_lt_degree
