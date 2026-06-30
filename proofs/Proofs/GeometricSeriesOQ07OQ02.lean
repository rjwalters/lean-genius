import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Proofs.GeometricSeriesOQ07

/-
# The Geometric Distribution: Mean, Second Moment, and Variance

This file answers the **probabilistic corollary** open question of the verified
parent `geometric-series-oq-07` (*The Second Moment of the Geometric Series*,
`∑ n² rⁿ = r(1+r)/(1-r)³`).

Let `0 ≤ r < 1` and consider the random variable `X` on `ℕ` with probability mass
function

  `P(X = n) = (1 - r) · rⁿ`.

This is the geometric distribution (number of failures before the first success,
with success probability `1 - r`). From the closed-form moment sums of the parent
we read off, by a single multiplication by `(1 - r)` and elementary field algebra:

  * **Normalisation**  `∑ₙ (1-r)·rⁿ = 1`            (`P` is a genuine pmf),
  * **Mean**           `E[X] = r / (1-r)`,
  * **Second moment**  `E[X²] = r(1+r) / (1-r)²`,
  * **Variance**       `Var(X) = E[X²] − E[X]² = r / (1-r)²`,

and finally we verify that the *centred* second moment — the honest definition of
the variance, `∑ₙ (n − E[X])²·P(X=n)` — also equals `r/(1-r)²`, obtained by
linearity of `HasSum` from the three moment sums.

Everything is a black-box consequence of the parent's `hasSum_sq_mul_geometric`
together with Mathlib's `hasSum_geometric_of_norm_lt_one` and
`hasSum_coe_mul_geometric_of_norm_lt_one`. No new analysis is performed: the
content is the translation of the analytic moment formulas into the language of a
probability distribution, plus the cancellation that produces the variance.

## Main results

* `geometric_pmf_hasSum`     — `HasSum (fun n => (1-r)·rⁿ) 1`.
* `geometric_expectation`    — `HasSum (fun n => n·(1-r)·rⁿ) (r/(1-r))`.
* `geometric_second_moment`  — `HasSum (fun n => n²·(1-r)·rⁿ) (r(1+r)/(1-r)²)`.
* `geometric_variance_identity` — `r(1+r)/(1-r)² − (r/(1-r))² = r/(1-r)²`.
* `geometric_variance`       — `HasSum (fun n => (n − r/(1-r))²·(1-r)·rⁿ) (r/(1-r)²)`.
-/

open scoped Topology

namespace GeometricSeriesOQ07OQ02

variable {r : ℝ}

/-- From `0 ≤ r < 1` we have `‖r‖ < 1`, the hypothesis the moment sums need. -/
lemma norm_lt_one (hr0 : 0 ≤ r) (hr1 : r < 1) : ‖r‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1

/-- `1 - r ≠ 0` whenever `r < 1`. -/
lemma one_sub_ne_zero (hr1 : r < 1) : (1 : ℝ) - r ≠ 0 := by
  have : (0 : ℝ) < 1 - r := by linarith
  exact ne_of_gt this

/-- **Normalisation.** `P(X = n) = (1-r)·rⁿ` is a genuine probability mass
function: the masses sum to `1`. This is the geometric series `∑ rⁿ = (1-r)⁻¹`
scaled by `(1-r)`. -/
theorem geometric_pmf_hasSum (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (1 - r) * r ^ n) 1 := by
  have h := (hasSum_geometric_of_norm_lt_one (norm_lt_one hr0 hr1)).mul_left (1 - r)
  have hval : (1 - r) * (1 - r)⁻¹ = (1 : ℝ) :=
    mul_inv_cancel₀ (one_sub_ne_zero hr1)
  rwa [hval] at h

/-- **Mean / first moment.** `E[X] = ∑ₙ n·(1-r)·rⁿ = r/(1-r)`, the parent's
first moment `∑ n·rⁿ = r/(1-r)²` scaled by `(1-r)`. -/
theorem geometric_expectation (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (n : ℝ) * ((1 - r) * r ^ n)) (r / (1 - r)) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one
    (norm_lt_one hr0 hr1)).mul_left (1 - r)
  -- `h : HasSum (fun n => (1-r) * (n * rⁿ)) ((1-r) * (r/(1-r)²))`
  have hne := one_sub_ne_zero hr1
  have hfun : (fun n : ℕ => (1 - r) * ((n : ℝ) * r ^ n))
      = (fun n : ℕ => (n : ℝ) * ((1 - r) * r ^ n)) := by
    funext n; ring
  have hval : (1 - r) * (r / (1 - r) ^ 2) = r / (1 - r) := by
    field_simp
  rw [hfun, hval] at h
  exact h

/-- **Second moment.** `E[X²] = ∑ₙ n²·(1-r)·rⁿ = r(1+r)/(1-r)²`, the parent's
second moment `∑ n²·rⁿ = r(1+r)/(1-r)³` scaled by `(1-r)`. -/
theorem geometric_second_moment (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * ((1 - r) * r ^ n))
      (r * (1 + r) / (1 - r) ^ 2) := by
  have h := (GeometricSeriesOQ07.hasSum_sq_mul_geometric
    (norm_lt_one hr0 hr1)).mul_left (1 - r)
  have hne := one_sub_ne_zero hr1
  have hfun : (fun n : ℕ => (1 - r) * ((n : ℝ) ^ 2 * r ^ n))
      = (fun n : ℕ => (n : ℝ) ^ 2 * ((1 - r) * r ^ n)) := by
    funext n; ring
  have hval : (1 - r) * (r * (1 + r) / (1 - r) ^ 3) = r * (1 + r) / (1 - r) ^ 2 := by
    field_simp
  rw [hfun, hval] at h
  exact h

/-- **Variance, algebraic form.** `Var(X) = E[X²] − E[X]² = r/(1-r)²`. This is the
pure field cancellation `r(1+r)/(1-r)² − (r/(1-r))² = r/(1-r)²`. -/
theorem geometric_variance_identity (hr1 : r < 1) :
    r * (1 + r) / (1 - r) ^ 2 - (r / (1 - r)) ^ 2 = r / (1 - r) ^ 2 := by
  have h := one_sub_ne_zero hr1
  field_simp
  ring

/-- **Variance, centred second moment.** The honest definition of the variance,
`Var(X) = ∑ₙ (n − E[X])²·P(X=n)`, also equals `r/(1-r)²`. Obtained from the three
moment sums by linearity of `HasSum`, using `(n − μ)² = n² − 2μ·n + μ²`. -/
theorem geometric_variance (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) - r / (1 - r)) ^ 2 * ((1 - r) * r ^ n))
      (r / (1 - r) ^ 2) := by
  set μ : ℝ := r / (1 - r) with hμ
  -- The three moment sums.
  have hE2 := geometric_second_moment hr0 hr1
  have hE1 := geometric_expectation hr0 hr1
  have hE0 := geometric_pmf_hasSum hr0 hr1
  -- Linear combination: E[X²] − 2μ·E[X] + μ²·1.
  have h := (hE2.sub (hE1.mul_left (2 * μ))).add (hE0.mul_left (μ ^ 2))
  -- Rewrite the summand into the centred form `(n − μ)²·P(n)`.
  have hfun :
      (fun n : ℕ => (n : ℝ) ^ 2 * ((1 - r) * r ^ n)
          - 2 * μ * ((n : ℝ) * ((1 - r) * r ^ n)) + μ ^ 2 * ((1 - r) * r ^ n))
      = (fun n : ℕ => ((n : ℝ) - μ) ^ 2 * ((1 - r) * r ^ n)) := by
    funext n; ring
  -- Rewrite the total into `r/(1-r)²`.
  have hval :
      r * (1 + r) / (1 - r) ^ 2 - 2 * μ * (r / (1 - r)) + μ ^ 2 * 1
        = r / (1 - r) ^ 2 := by
    rw [hμ]
    have hne := one_sub_ne_zero hr1
    field_simp
    ring
  rw [hfun, hval] at h
  exact h

end GeometricSeriesOQ07OQ02
