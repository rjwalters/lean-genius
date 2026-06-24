import Mathlib
import Proofs.SylvesterSequenceOQ01

/-!
# Sylvester's sequence, oq-01-oq-01: the reciprocal sum converges to `1` as a `Tendsto`

The parent entry `sylvester-sequence-oq-01` proved the closed form for the partial
reciprocal sums of Sylvester's sequence `a₀ = 2`, `a_{n+1} = aₙ² - aₙ + 1`:

  `syl_partial_sum` :  `∑_{k=0}^{n} 1/aₖ = 1 - 1/(a_{n+1} - 1)`     (an identity in `ℚ`).

That identity *informally* gives `∑_{k} 1/aₖ = 1` "since `a_{n+1} - 1 → ∞`", but the
parent stopped at the algebraic closed form and never discharged the analytic limit.

This entry **promotes that observation to a formal statement of convergence**, working in
`ℝ`:

  `syl_reciprocal_sum_tendsto` :
      `Tendsto (fun n => ∑_{k=0}^{n} 1/aₖ) atTop (𝓝 1)`,

and packages it as the Egyptian-fraction `HasSum` / `tsum` statement

  `syl_hasSum_one` :  `HasSum (fun k => 1/aₖ) 1`,
  `syl_tsum_one`   :  `∑' k, 1/aₖ = 1`.

## Method

The genuinely new content is the analytic tail estimate that the parent omitted.  Two
ingredients:

* **Linear growth** (`add_two_le_syl`):  `n + 2 ≤ aₙ`.  Each step satisfies
  `a_{n+1} = aₙ² - aₙ + 1 ≥ aₙ + 1` (because `(aₙ - 1)² ≥ 1`), so the sequence increases by
  at least `1` per step from `a₀ = 2`.  This already forces `a_{n+1} - 1 → ∞`.

* **Vanishing tail** (`tendsto_syl_recip_zero`):  from `a_{n+1} - 1 ≥ n` and
  `tendsto_inv_atTop_zero`, the tail `1/(a_{n+1} - 1) → 0`.

Casting the parent's `ℚ` closed form to `ℝ` (`syl_partial_sum_real`) and subtracting the
vanishing tail from `1` (`Tendsto.const_sub`) yields the limit.  Since the terms are
nonnegative, `hasSum_iff_tendsto_nat_of_nonneg` upgrades the partial-sum limit to a
genuine `HasSum`, hence `∑' = 1`.

No axioms, no sorries.
-/

namespace SylvesterSequenceOQ01OQ01

open SylvesterSequenceOQ01
open Filter Topology

/-! ## Linear growth of the sequence -/

/-- **Linear lower bound.**  `n + 2 ≤ aₙ`.  Each step grows by at least `1`
(`a_{n+1} ≥ aₙ + 1`, since `aₙ² ≥ 2aₙ` for `aₙ ≥ 2`), starting from `a₀ = 2`. -/
theorem add_two_le_syl (n : ℕ) : n + 2 ≤ syl n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h2 := two_le_syl k
    have hsq : 2 * syl k ≤ syl k ^ 2 := by nlinarith [h2]
    rw [syl_succ]
    omega

/-! ## The real-valued closed form and the vanishing tail -/

/-- The parent's closed form, transported to `ℝ`:
`∑_{k=0}^{n} 1/aₖ = 1 - 1/(a_{n+1} - 1)`. -/
theorem syl_partial_sum_real (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (syl k : ℝ)
      = 1 - 1 / ((syl (n + 1) : ℝ) - 1) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (syl_partial_sum n)
  push_cast at h
  exact h

/-- The denominators `a_{n+1} - 1` tend to `+∞`: they dominate the diagonal `n` because
`a_{n+1} - 1 ≥ aₙ ≥ n + 2 ≥ n`. -/
theorem tendsto_syl_sub_one_atTop :
    Tendsto (fun n => (syl (n + 1) : ℝ) - 1) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) ?_ tendsto_natCast_atTop_atTop
  intro n
  have h : n + 2 ≤ syl (n + 1) := le_trans (by omega) (add_two_le_syl (n + 1))
  have : (n : ℝ) + 2 ≤ (syl (n + 1) : ℝ) := by exact_mod_cast h
  linarith

/-- **Vanishing tail.**  `1/(a_{n+1} - 1) → 0`. -/
theorem tendsto_syl_recip_zero :
    Tendsto (fun n => 1 / ((syl (n + 1) : ℝ) - 1)) atTop (𝓝 0) := by
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp tendsto_syl_sub_one_atTop

/-! ## Convergence of the reciprocal sum -/

/-- **The reciprocal sum converges to `1`.**  The partial sums
`∑_{k=0}^{n} 1/aₖ` tend to `1` as `n → ∞`.  This is the formal `Tendsto` promotion of the
parent's closed-form observation. -/
theorem syl_reciprocal_sum_tendsto :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (syl k : ℝ))
      atTop (𝓝 1) := by
  have hfun : (fun n => ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (syl k : ℝ))
      = fun n => 1 - 1 / ((syl (n + 1) : ℝ) - 1) := funext syl_partial_sum_real
  rw [hfun]
  have := (tendsto_syl_recip_zero).const_sub (1 : ℝ)
  simpa using this

/-! ## Egyptian-fraction form: `HasSum` and `tsum` -/

/-- Each reciprocal term is nonnegative. -/
theorem syl_recip_nonneg (k : ℕ) : 0 ≤ (1 : ℝ) / (syl k : ℝ) := by
  positivity

/-- **Egyptian-fraction identity (`HasSum` form).**  `∑ₖ 1/aₖ = 1`.  Sylvester's sequence
is the greedy Egyptian-fraction expansion of `1`. -/
theorem syl_hasSum_one : HasSum (fun k => (1 : ℝ) / (syl k : ℝ)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg syl_recip_nonneg]
  -- the `range n` partial sums tend to `1`; reindex from the `range (n+1)` limit
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa using syl_reciprocal_sum_tendsto

/-- **Egyptian-fraction identity (`tsum` form).**  `∑' k, 1/aₖ = 1`. -/
theorem syl_tsum_one : ∑' k, (1 : ℝ) / (syl k : ℝ) = 1 :=
  syl_hasSum_one.tsum_eq

end SylvesterSequenceOQ01OQ01
