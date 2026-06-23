/-
Erdős Problem #100 — Open Question: Distance Set Diameter Growth Rate

Is the minimum diameter of n-point integer distance sets Θ(n) (linear growth)
or Θ(n/log n) (matching the current best bound from Guth-Katz)?

The gap between what's known and what's conjectured is exactly a factor of log n.

Status: OPEN

Key results formalized here:
1. The strong conjecture (diam ≥ n-1) implies a linear lower bound with c = 1/2
2. The current Guth-Katz bound cn/log n is strictly sublinear

Reference: https://erdosproblems.com/100
-/

import Proofs.Erdos100Problem

open Erdos100 Filter Set

namespace Erdos100OQ02

/-! ## Connection Between Conjectures -/

/--
**The strong conjecture implies a linear lower bound with constant 1/2.**

If every n-point integer distance set has diameter ≥ n-1 (the strong conjecture),
then every such set has diameter ≥ n/2. This follows from n - 1 ≥ n/2 for n ≥ 2.
-/
theorem strong_implies_half_linear :
    Erdos100StrongConjecture →
    ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      hasIntegerDistances S → S.card ≥ 2 →
      (S.card : ℝ) / 2 ≤ diam S := by
  intro h S hint hcard
  have hstrong := h S hint hcard
  have hge2 : (S.card : ℝ) ≥ 2 := by exact_mod_cast hcard
  linarith

/-! ## The Gap: cn/log n vs cn -/

/--
**The current Guth-Katz bound is strictly weaker than a linear bound.**

For any c > 0, the bound cn/log n is eventually strictly less than cn.
This quantifies the gap: if the linear conjecture holds, the Guth-Katz
route loses exactly a factor of log n.
-/
theorem gk_bound_strictly_sublinear (c : ℝ) (hc : c > 0) :
    ∀ᶠ n : ℕ in atTop,
      c * ↑n / Real.log ↑n < c * ↑n := by
  filter_upwards [n_over_log_sublinear 1 (by norm_num)] with n hn
  rw [mul_one] at hn
  rw [mul_div_assoc]
  exact mul_lt_mul_of_pos_left hn hc


end Erdos100OQ02
