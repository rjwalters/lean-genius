import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic

/-
# Two-Sided Derivative Bounds Sandwich the Increment

## What This Proves

This is the **signed, two-sided quantitative form of the Mean Value Theorem**.
If `f` is continuous on `[a, b]` (with `a ≤ b`) and differentiable on `(a, b)`
with its derivative pinned between two constants,

  `m ≤ f'(x) ≤ M`  for all `x ∈ (a, b)`,

then the total increment is sandwiched between the two linear predictions:

  `m · (b - a) ≤ f(b) - f(a) ≤ M · (b - a)`.

The parent `mean-value-theorem` gives the existence statement `f'(c) = slope`.
The sibling `mean-value-theorem-oq-03` proves only the *absolute*, one-sided norm
bound `‖f(b) - f(a)‖ ≤ C(b - a)`, which discards sign and gives no lower bound.
This child keeps the sign and both bounds, and then specializes:

* `m > 0` forces a strict increase (`f a < f b`);
* `M < 0` forces a strict decrease (`f b < f a`);
* `0 ≤ m` gives ordinary monotonicity (`f a ≤ f b`);
* `m = -C`, `M = C` recovers the scalar Lipschitz estimate
  `|f(b) - f(a)| ≤ C(b - a)`.

## Method

Both halves are direct applications of the named Mathlib engines
`Convex.mul_sub_le_image_sub_of_le_deriv` (lower bound) and
`Convex.image_sub_le_mul_sub_of_deriv_le` (upper bound), instantiated at the
convex set `D = Set.Icc a b`, whose interior is `Set.Ioo a b`
(`interior_Icc`). Everything else is `linarith` / `abs_le` bookkeeping.

0 sorries, 0 axioms (only `propext` / `Classical.choice` / `Quot.sound`).
-/

open Set

namespace MeanValueTheoremOQ06

/-- **Two-sided increment sandwich.** If `f` is continuous on `[a, b]`, differentiable on
`(a, b)`, and its derivative satisfies `m ≤ f' ≤ M` throughout `(a, b)`, then the increment
`f b - f a` is trapped between `m (b - a)` and `M (b - a)`. This is the signed, quantitative
Mean Value Theorem. -/
theorem deriv_bounds_imply_increment_bounds {a b m M : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hm : ∀ x ∈ Set.Ioo a b, m ≤ deriv f x)
    (hM : ∀ x ∈ Set.Ioo a b, deriv f x ≤ M) :
    m * (b - a) ≤ f b - f a ∧ f b - f a ≤ M * (b - a) := by
  -- Reshape the interior of `Icc a b` into `Ioo a b`.
  rw [← interior_Icc] at hfd hm hM
  refine ⟨?_, ?_⟩
  · exact (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hfc hfd hm
      a (left_mem_Icc.2 hab) b (right_mem_Icc.2 hab) hab
  · exact (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hfc hfd hM
      a (left_mem_Icc.2 hab) b (right_mem_Icc.2 hab) hab

/-- The lower half in isolation: a lower derivative bound gives a lower increment bound. -/
theorem le_increment_of_le_deriv {a b m : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hm : ∀ x ∈ Set.Ioo a b, m ≤ deriv f x) :
    m * (b - a) ≤ f b - f a := by
  rw [← interior_Icc] at hfd hm
  exact (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hfc hfd hm
    a (left_mem_Icc.2 hab) b (right_mem_Icc.2 hab) hab

/-- The upper half in isolation: an upper derivative bound gives an upper increment bound. -/
theorem increment_le_of_deriv_le {a b M : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hM : ∀ x ∈ Set.Ioo a b, deriv f x ≤ M) :
    f b - f a ≤ M * (b - a) := by
  rw [← interior_Icc] at hfd hM
  exact (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hfc hfd hM
    a (left_mem_Icc.2 hab) b (right_mem_Icc.2 hab) hab

/-- **Lipschitz recovery.** A two-sided *absolute* bound `|f'| ≤ C` on `(a, b)` yields the
scalar Lipschitz estimate `|f b - f a| ≤ C (b - a)`. This is the `m = -C`, `M = C`
specialization; it matches the magnitude bound of the vector-valued sibling `oq-03`. -/
theorem abs_increment_le_of_abs_deriv_le {a b C : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hC : ∀ x ∈ Set.Ioo a b, |deriv f x| ≤ C) :
    |f b - f a| ≤ C * (b - a) := by
  have hlo : ∀ x ∈ Set.Ioo a b, -C ≤ deriv f x := fun x hx => (abs_le.1 (hC x hx)).1
  have hhi : ∀ x ∈ Set.Ioo a b, deriv f x ≤ C := fun x hx => (abs_le.1 (hC x hx)).2
  obtain ⟨h1, h2⟩ := deriv_bounds_imply_increment_bounds hab hfc hfd hlo hhi
  rw [abs_le]
  constructor
  · linarith [h1]
  · linarith [h2]

/-- **Strict increase gap.** A strictly positive lower derivative bound on `(a, b)` with
`a < b` forces `f a < f b` (indeed `f b - f a ≥ m (b - a) > 0`). -/
theorem lt_of_pos_deriv_lower_bound {a b m : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hm : ∀ x ∈ Set.Ioo a b, m ≤ deriv f x) (hmpos : 0 < m) :
    f a < f b := by
  have h1 : m * (b - a) ≤ f b - f a := le_increment_of_le_deriv hab.le hfc hfd hm
  have : 0 < m * (b - a) := mul_pos hmpos (sub_pos.2 hab)
  linarith

/-- **Strict decrease gap.** A strictly negative upper derivative bound on `(a, b)` with
`a < b` forces `f b < f a`. -/
theorem gt_of_neg_deriv_upper_bound {a b M : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hM : ∀ x ∈ Set.Ioo a b, deriv f x ≤ M) (hMneg : M < 0) :
    f b < f a := by
  have h2 : f b - f a ≤ M * (b - a) := increment_le_of_deriv_le hab.le hfc hfd hM
  have : M * (b - a) < 0 := mul_neg_of_neg_of_pos hMneg (sub_pos.2 hab)
  linarith

/-- **Monotone version.** A nonnegative lower derivative bound gives `f a ≤ f b`. -/
theorem le_of_nonneg_deriv_lower_bound {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hm : ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x) :
    f a ≤ f b := by
  have h1 : (0 : ℝ) * (b - a) ≤ f b - f a := le_increment_of_le_deriv hab hfc hfd hm
  simp only [zero_mul] at h1
  linarith

/-- **Antitone version.** A nonpositive upper derivative bound gives `f b ≤ f a`. -/
theorem ge_of_nonpos_deriv_upper_bound {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hM : ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0) :
    f b ≤ f a := by
  have h2 : f b - f a ≤ (0 : ℝ) * (b - a) := increment_le_of_deriv_le hab hfc hfd hM
  simp only [zero_mul] at h2
  linarith

/-- Worked example. For any `f` continuous on `[0, 2]`, differentiable on `(0, 2)`, whose
derivative stays in `[1, 3]` throughout, the increment `f 2 - f 0` is pinned to `[2, 6]`.
This is the theorem doing genuine numerical work: pointwise slope bounds `1 ≤ f' ≤ 3`
become the global two-sided increment bound `2 ≤ f(2) - f(0) ≤ 6`. -/
example {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc 0 2))
    (hfd : DifferentiableOn ℝ f (Set.Ioo 0 2))
    (h1 : ∀ x ∈ Set.Ioo (0 : ℝ) 2, 1 ≤ deriv f x)
    (h3 : ∀ x ∈ Set.Ioo (0 : ℝ) 2, deriv f x ≤ 3) :
    2 ≤ f 2 - f 0 ∧ f 2 - f 0 ≤ 6 := by
  obtain ⟨lo, hi⟩ := deriv_bounds_imply_increment_bounds (by norm_num) hfc hfd h1 h3
  constructor
  · linarith
  · linarith

end MeanValueTheoremOQ06
