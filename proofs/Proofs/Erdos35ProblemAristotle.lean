/-
  Aristotle targets for Erdos35Problem
  (Schnirelmann Density and Additive Bases: Plünnecke Inequality Support)
  Routine supporting lemmas for automated proof search.
  See Erdos35Problem.lean for the main formalization.

  These lemmas provide building blocks for:
  - The key algebraic bridge from Plünnecke's inequality to the Erdős conjecture
  - Real-power monotonicity on the unit interval [0, 1]
-/
import Mathlib

namespace Erdos35.Aristotle

open Real

/-- For α ∈ [0,1] and r ∈ [0,1], α^r ≥ α.
    This holds because x ↦ α^x is decreasing when α ≤ 1 (log α ≤ 0),
    so r ≤ 1 implies α^r ≥ α^1 = α. -/
theorem rpow_ge_self_of_le_one (α : ℝ) (r : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    α ^ r ≥ α := by
  rcases eq_or_lt_of_le hα0 with rfl | hα_pos
  · -- α = 0: 0^r ≥ 0
    apply Real.rpow_nonneg; linarith
  · -- α ∈ (0,1]: exponent decreases (r ≤ 1), so α^r ≥ α^1 = α
    have h := Real.rpow_le_rpow_of_exponent_ge hα_pos hα1 hr1
    rwa [Real.rpow_one] at h

/-- Key algebraic step in deriving the Erdős conjecture from Plünnecke's inequality:
    for α ∈ [0,1] and k ≥ 1, α^{1-1/k} ≥ α + α(1-α)/k.
    Proof via Bernoulli inequality for negative exponents:
    reduce to (1-t)^(-1/k) ≥ 1+t/k via log(1-t) ≤ -t and exp(x) ≥ 1+x. -/
theorem power_bound_implies_erdos_ari (α : ℝ) (k : ℕ) (hk : k ≥ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α ^ (1 - 1 / (k : ℝ)) ≥ α + α * (1 - α) / k := by
  -- Case 1: α = 0
  by_cases hα_zero : α = 0
  · subst hα_zero; simp only [zero_mul, add_zero, zero_div, ge_iff_le]
    exact Real.rpow_nonneg le_rfl _
  have hα_pos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hα_zero)
  -- Case 2: k = 1 (exponent = 0, LHS = 1 ≥ RHS = α(2-α))
  by_cases hk1 : k = 1
  · subst hk1; simp only [ge_iff_le, Nat.cast_one, div_one, sub_self, Real.rpow_zero]
    nlinarith [sq_nonneg (1 - α)]
  -- Case 3: α ∈ (0,1], k ≥ 2
  have hk2 : k ≥ 2 := by omega
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show k > 0 by omega)
  set t := 1 - α with ht_def
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t < 1 := by linarith
  have h1t_pos : 0 < 1 - t := by linarith
  have hexp_split : (1 : ℝ) - 1 / k = 1 + -(1 / k) := by ring
  rw [ge_iff_le, hexp_split, Real.rpow_add hα_pos, Real.rpow_one]
  have hrhs_eq : α + α * (1 - α) / k = α * (1 + t / k) := by rw [ht_def]; ring
  rw [hrhs_eq]
  apply mul_le_mul_of_nonneg_left _ hα_pos.le
  rw [show α = 1 - t from by linarith [ht_def]]
  have hlog_bound : Real.log (1 - t) ≤ -t := by
    calc Real.log (1 - t)
        ≤ Real.log (Real.exp (-t)) := by
          apply Real.log_le_log h1t_pos
          have := Real.add_one_le_exp (-t)
          linarith
      _ = -t := Real.log_exp _
  have harg : t / k ≤ (-(1 / k)) * Real.log (1 - t) := by
    have h_neg_log : t ≤ -Real.log (1 - t) := by linarith [hlog_bound]
    calc t / k = t * (1 / k) := by ring
        _ ≤ (-Real.log (1 - t)) * (1 / k) :=
            mul_le_mul_of_nonneg_right h_neg_log (by positivity)
        _ = (-(1 / k)) * Real.log (1 - t) := by ring
  have hdef : (1 - t) ^ (-(1 / k)) = Real.exp (Real.log (1 - t) * -(1 / k)) :=
    Real.rpow_def_of_pos h1t_pos _
  rw [hdef, mul_comm]
  have h_exp := Real.add_one_le_exp (-(1 / k) * Real.log (1 - t))
  linarith

end Erdos35.Aristotle
