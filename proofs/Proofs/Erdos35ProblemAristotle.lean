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
    exact Real.rpow_nonneg (le_refl 0) _
  · -- α ∈ (0,1]: x ↦ α^x is decreasing (log α ≤ 0), so r ≤ 1 implies α^r ≥ α^1 = α
    have h := Real.rpow_le_rpow_of_exponent_ge hα_pos hα1 hr1
    rwa [Real.rpow_one] at h

/-- Key algebraic step in deriving the Erdős conjecture from Plünnecke's inequality:
    for α ∈ [0,1] and k ≥ 1, α^{1-1/k} ≥ α + α(1-α)/k.
    Proof: α^{1-1/k} = α·exp(-log α/k) ≥ α·(1+(1-α)/k) via ln x ≤ x-1 and e^x ≥ 1+x. -/
theorem power_bound_implies_erdos_ari (α : ℝ) (k : ℕ) (hk : k ≥ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α ^ (1 - 1 / (k : ℝ)) ≥ α + α * (1 - α) / k := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  rcases eq_or_lt_of_le hα0 with rfl | hα_pos
  · have hrhs : (0 : ℝ) + 0 * (1 - 0) / (k : ℝ) = 0 := by ring
    rw [ge_iff_le, hrhs]; exact Real.rpow_nonneg (le_refl 0) _
  · have hlog_le : Real.log α ≤ α - 1 := by
      have h := Real.add_one_le_exp (Real.log α)
      rw [Real.exp_log hα_pos] at h; linarith
    have hstep2 : (1 - α) / (k : ℝ) ≤ -(Real.log α / (k : ℝ)) := by
      have h : 1 - α ≤ -Real.log α := by linarith
      have h2 := (div_le_div_right hk_pos).mpr h
      rwa [neg_div] at h2
    have hstep3 : 1 + (1 - α) / (k : ℝ) ≤ Real.exp (-(Real.log α / (k : ℝ))) :=
      by linarith [Real.add_one_le_exp (-(Real.log α / (k : ℝ)))]
    have hrpow : α ^ (1 - 1 / (k : ℝ)) = α * Real.exp (-(Real.log α / (k : ℝ))) := by
      rw [Real.rpow_def_of_pos hα_pos]
      have heq : Real.log α * (1 - 1 / (k : ℝ)) =
                 Real.log α + -(Real.log α / (k : ℝ)) := by ring
      rw [heq, Real.exp_add, Real.exp_log hα_pos]
    rw [hrpow, ge_iff_le,
        show α + α * (1 - α) / (k : ℝ) = α * (1 + (1 - α) / (k : ℝ)) from by ring]
    exact mul_le_mul_of_nonneg_left hstep3 (le_of_lt hα_pos)

end Erdos35.Aristotle
