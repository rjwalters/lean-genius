/-
  Closed form of the finite second-moment sum Σ k²·rᵏ
  Open Question: summation-by-parts-oq-01-oq-02

  The parent entry gives the arithmetico-geometric sum Σ k·rᵏ in closed form.
  This entry handles the next moment: the finite second-moment sum
    S(n) = Σ_{k=0}^{n-1} k²·rᵏ.

  ## Main Results

  `sq_geom_sum` (PROVED, division-free): for every real r and every n,
    (1 − r)³ · Σ_{k<n} k²·rᵏ
      = r(r+1) + rⁿ·( −n²(r−1)² + 2n·r(r−1) − r(r+1) ).
  This polynomial identity is valid for ALL r (including r = 1, where both sides
  vanish) and is proved by induction closing purely with `ring`.

  `sq_geom_sum_div` (PROVED, closed form): for r ≠ 1,
    Σ_{k<n} k²·rᵏ
      = ( r(r+1) + rⁿ·(−n²(r−1)² + 2n·r(r−1) − r(r+1)) ) / (1 − r)³.

  ## Proof Strategy

  Multiplying through by (1−r)³ clears all denominators, turning the closed form
  into a polynomial identity in r and rⁿ with coefficients polynomial in n. The
  induction step uses Σ_{k<n+1} = Σ_{k<n} + n²·rⁿ and `r^(n+1) = r^n·r`; the
  resulting identity is true as a polynomial, so `ring` closes it. The divided
  form follows by dividing by the nonzero (1−r)³.
-/

import Mathlib

namespace SummationByPartsOQ01OQ02

/-- The numerator polynomial of the closed form:
    `B(n, r) = r(r+1) + rⁿ·(−n²(r−1)² + 2n·r(r−1) − r(r+1))`. -/
private def num (r : ℝ) (n : ℕ) : ℝ :=
  r * (r + 1) +
    r ^ n * (-(n : ℝ) ^ 2 * (r - 1) ^ 2 + 2 * (n : ℝ) * r * (r - 1) - r * (r + 1))

/-- **Division-free closed form.** For every real `r` and every `n`,
    `(1 − r)³ · Σ_{k<n} k²·rᵏ = r(r+1) + rⁿ·(−n²(r−1)² + 2n·r(r−1) − r(r+1))`.
    Valid for all `r` (at `r = 1` both sides are `0`). -/
theorem sq_geom_sum (r : ℝ) (n : ℕ) :
    (1 - r) ^ 3 * ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 * r ^ k = num r n := by
  induction n with
  | zero => simp [num]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, num, num, pow_succ]
    push_cast
    ring

/-- **Closed form.** For `r ≠ 1`,
    `Σ_{k<n} k²·rᵏ = (r(r+1) + rⁿ·(−n²(r−1)² + 2n·r(r−1) − r(r+1))) / (1 − r)³`. -/
theorem sq_geom_sum_div (r : ℝ) (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 * r ^ k = num r n / (1 - r) ^ 3 := by
  have h : (1 - r) ^ 3 ≠ 0 := pow_ne_zero 3 (sub_ne_zero.mpr hr.symm)
  rw [eq_div_iff h, mul_comm]
  exact sq_geom_sum r n

-- Sanity checks against direct evaluation.
example : ∑ k ∈ Finset.range 4, (k : ℝ) ^ 2 * (2 : ℝ) ^ k = 0 + 2 + 4 * 4 + 9 * 8 := by
  norm_num [Finset.sum_range_succ]

example : (1 - (2 : ℝ)) ^ 3 * ∑ k ∈ Finset.range 4, (k : ℝ) ^ 2 * (2 : ℝ) ^ k = num 2 4 := by
  simpa using sq_geom_sum 2 4

end SummationByPartsOQ01OQ02
