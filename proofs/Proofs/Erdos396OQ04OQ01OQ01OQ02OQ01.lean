/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-02 → OQ-01: the exponential growth rate of the Catalan numbers is exactly `4`

The parent `Erdos396OQ04OQ01OQ01OQ02` isolates the **sub-exponential** correction
to Catalan growth: it pins the polynomial exponent `3/2` in the asymptotic
`catalan n ∼ 4^n / (n^{3/2} √π)` by telescoping the recurrence ratio through the
logarithm.  That is the *fine* structure — the deviation of `catalan n / 4^n` from
a constant.

This follow-up nails the *coarse* structure: the **leading exponential rate**.
We show

  **`catalan_log_div_tendsto_log_four`** :
    `(1/n)·log (catalan n) → log 4`,

i.e. `catalan n = 4^{(1 + o(1)) n}`.  Equivalently, taking `n`-th roots,

  **`catalan_rpow_tendsto_four`** :
    `(catalan n)^{1/n} → 4`.

This is the Cauchy–Hadamard statement that the **Catalan generating function**
`∑ catalan n · xⁿ` has radius of convergence exactly `1/4`: the exponential rate
`4` is the reciprocal of that radius, and the polynomial factor `n^{-3/2}` from the
parent does not affect it.

The proof needs only two elementary brackets on the central binomial coefficient,
both already in Mathlib:

* an **upper** bound `catalan n ≤ 4^n`, from
  `(n+1)·catalan n = centralBinom n = (2n choose n) ≤ 2^{2n} = 4^n`
  (`Nat.choose_le_two_pow`);
* a **lower** bound `4^n ≤ 2 n² · catalan n` for `n ≥ 4`, from Erdős's
  `Nat.four_pow_lt_mul_centralBinom : 4^n < n · centralBinom n` together with
  `n(n+1) ≤ 2n²`.

Passing to logarithms turns these into `log 4 − O((log n)/n) ≤ (log catalan n)/n ≤ log 4`,
and the squeeze `(log n)/n → 0` (Mathlib's `Real.isLittleO_log_id_atTop`) forces the
limit `log 4`.  No Stirling estimate is used.

Reference: https://erdosproblems.com/396
-/

import Mathlib

open Nat Filter Topology

namespace Erdos396OQ04OQ01OQ01OQ02OQ01

/-! ## Positivity and the two elementary brackets -/

/-- Every Catalan number is positive (`(n+1)·catalan n = centralBinom n > 0`). -/
theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hc := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | hp
  · rw [h0, Nat.mul_zero] at h; omega
  · exact hp

/-- **Upper bracket.**  `catalan n ≤ 4^n` for every `n`: the central binomial
coefficient `(2n choose n)` is bounded by the row sum `2^{2n} = 4^n`, and
`catalan n ≤ centralBinom n`. -/
theorem catalan_le_four_pow (n : ℕ) : (catalan n : ℝ) ≤ 4 ^ n := by
  have hcat_le_cb : catalan n ≤ Nat.centralBinom n := by
    calc catalan n ≤ (n + 1) * catalan n :=
          le_mul_of_one_le_left (Nat.zero_le _) (by omega)
      _ = Nat.centralBinom n := succ_mul_catalan_eq_centralBinom n
  have hcb_le : Nat.centralBinom n ≤ 4 ^ n := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    calc (2 * n).choose n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  have : catalan n ≤ 4 ^ n := le_trans hcat_le_cb hcb_le
  exact_mod_cast this

/-- **Lower bracket.**  For `n ≥ 4`, `4^n ≤ 2 n² · catalan n`.  From Erdős's bound
`4^n < n · centralBinom n = n(n+1)·catalan n` and `n(n+1) ≤ 2n²`. -/
theorem four_pow_le_two_sq_mul_catalan (n : ℕ) (hn : 4 ≤ n) :
    (4 : ℝ) ^ n ≤ 2 * (n : ℝ) ^ 2 * catalan n := by
  have h := Nat.four_pow_lt_mul_centralBinom n hn
  have hcb := succ_mul_catalan_eq_centralBinom n
  have hcat0 : (0 : ℝ) ≤ (catalan n : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hR : (4 : ℝ) ^ n ≤ (n : ℝ) * (Nat.centralBinom n : ℝ) := by exact_mod_cast h.le
  have hcbR : (Nat.centralBinom n : ℝ) = ((n : ℝ) + 1) * (catalan n : ℝ) := by
    exact_mod_cast hcb.symm
  rw [hcbR] at hR
  -- `hR : 4^n ≤ n·(n+1)·catalan n`; combine with `n(n+1) ≤ 2n²` (uses `n ≥ 1`).
  nlinarith [hR, hcat0, hn1,
    mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) by linarith)
      (show (0 : ℝ) ≤ (n : ℝ) - 1 by linarith)) hcat0]

/-! ## The exponential growth rate -/

/-- **The exponential growth rate of the Catalan numbers is `4`.**
`(1/n)·log (catalan n) → log 4`.  This is the Cauchy–Hadamard statement that the
Catalan generating function has radius of convergence `1/4`. -/
theorem catalan_log_div_tendsto_log_four :
    Tendsto (fun n : ℕ => Real.log (catalan n) / n) atTop (𝓝 (Real.log 4)) := by
  -- Core analytic input: `(log n)/n → 0`.
  have hlog : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
    simpa using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  -- Lower flank `log 4 − (log 2)/n − 2·(log n)/n → log 4`.
  have hlower : Tendsto
      (fun n : ℕ => Real.log 4 - Real.log 2 / n - 2 * (Real.log n / n))
      atTop (𝓝 (Real.log 4)) := by
    have h1 : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (𝓝 0) := by
      simpa [mul_one_div] using tendsto_one_div_atTop_nhds_zero_nat.const_mul (Real.log 2)
    have h2 : Tendsto (fun n : ℕ => 2 * (Real.log n / n)) atTop (𝓝 0) := by
      simpa using hlog.const_mul 2
    have := ((tendsto_const_nhds (x := Real.log 4)).sub h1).sub h2
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · -- lower flank ≤ `(log catalan n)/n`
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hcpos : (0 : ℝ) < (catalan n : ℝ) := by exact_mod_cast catalan_pos n
    have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hnpos 2
    have h2n2pos : (0 : ℝ) < 2 * (n : ℝ) ^ 2 := mul_pos (by norm_num) hn2pos
    have hle := four_pow_le_two_sq_mul_catalan n hn
    have hlog_ineq : Real.log ((4 : ℝ) ^ n) ≤ Real.log (2 * (n : ℝ) ^ 2 * catalan n) :=
      Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at hlog_ineq
    have hexpand : Real.log (2 * (n : ℝ) ^ 2 * catalan n)
        = Real.log 2 + 2 * Real.log n + Real.log (catalan n) := by
      rw [Real.log_mul h2n2pos.ne' hcpos.ne', Real.log_mul (by norm_num) hn2pos.ne',
        Real.log_pow]
      push_cast; ring
    rw [hexpand] at hlog_ineq
    rw [← sub_nonneg]
    have hrw : Real.log (catalan n) / ↑n
          - (Real.log 4 - Real.log 2 / ↑n - 2 * (Real.log ↑n / ↑n))
        = (Real.log (catalan n) - ↑n * Real.log 4 + Real.log 2 + 2 * Real.log ↑n) / ↑n := by
      field_simp; ring
    rw [hrw]
    apply div_nonneg _ hnpos.le
    linarith [hlog_ineq]
  · -- `(log catalan n)/n ≤ log 4`
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hcpos : (0 : ℝ) < (catalan n : ℝ) := by exact_mod_cast catalan_pos n
    have hle := catalan_le_four_pow n
    have hlog_ineq : Real.log (catalan n) ≤ ↑n * Real.log 4 := by
      have := Real.log_le_log hcpos hle
      rwa [Real.log_pow] at this
    rw [div_le_iff₀ hnpos]
    linarith [hlog_ineq, mul_comm (n : ℝ) (Real.log 4)]

/-- **`n`-th root form.**  `(catalan n)^{1/n} → 4`: the Catalan numbers grow like
`4ⁿ` to leading exponential order.  Equivalently, the radius of convergence of
`∑ catalan n · xⁿ` is `1/4`. -/
theorem catalan_rpow_tendsto_four :
    Tendsto (fun n : ℕ => (catalan n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 4) := by
  have hmain := catalan_log_div_tendsto_log_four
  have hexp := (Real.continuous_exp.tendsto (Real.log 4)).comp hmain
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hexp
  refine hexp.congr (fun n => ?_)
  simp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos (by exact_mod_cast catalan_pos n), mul_one_div]

end Erdos396OQ04OQ01OQ01OQ02OQ01
