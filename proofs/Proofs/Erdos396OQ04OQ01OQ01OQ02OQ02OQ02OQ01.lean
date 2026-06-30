/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-02 → OQ-02 → OQ-02 → OQ-01:
  the exact Wallis constant `1/√π` in the `1/2` exponent of the central binomial coefficient

The grandparent thread pins the *critical exponent* `1/2` of the central binomial
coefficient `C(2n,n)`: from the recurrence alone,
`C(2n,n)/4^n ∼ n^{-1/2}` (entry `…OQ02OQ02`).  Its child `…OQ02OQ02OQ02`
("explicit constants") sharpens this to a two-sided *bracket* on the leading
constant of the normalised sequence `C(2n,n)·√n / 4^n`, placing it between `1/2`
and `1/√3`, equivalently `3 < π < 4`.

This file closes the bracket to a single point: the normalised central binomial
coefficient converges to the **exact** Wallis constant

    `C(2n,n)·√n / 4^n → 1/√π`        (`centralBinom_mul_sqrt_div_tendsto`),

equivalently `C(2n,n) ∼ 4^n/√(π n)` (`centralBinom_mul_sqrt_pi_div_tendsto_one`).
The parent's bracket `1/2 ≤ 1/√π ≤ 1/√3` is recovered as the squeeze of this
limit between its two endpoints (`sqrt_pi_inv_mem_bracket`).

## Method

The proof routes through Mathlib's Stirling sequence
`stirlingSeq n = n! / (√(2n)·(n/e)^n)`, which converges to `√π`
(`Stirling.tendsto_stirlingSeq_sqrt_pi`).  The bridge is a single *square-root
free* algebraic identity (for `n ≥ 1`):

    **`cb_sq_identity`** :
      `C(2n,n)²·n / 16^n = stirlingSeq (2n)² / stirlingSeq n⁴`.

Squaring is what removes every square root: `stirlingSeq (2n)²` contains
`(√(4n))² = 4n` and `stirlingSeq n⁴` contains `(√(2n))⁴ = (2n)²`, so the whole
identity is purely polynomial once `(2n)! = C(2n,n)·(n!)²` and the cancellation
`((2n)/e)^{2n} = 4^n·((n/e)^n)²` are substituted.  As `n → ∞` the right side
tends to `(√π)² / (√π)⁴ = π/π² = 1/π`, and a final square root (the normalised
sequence is non-negative) transports the limit to `1/√π`.

No Stirling *estimate* is hand-rolled — the limit `1/√π` is exactly the constant
the elementary bracket of the parent could only sandwich.

Reference: https://erdosproblems.com/396
-/

import Mathlib

open Nat Filter Topology Finset Real Stirling

namespace Erdos396OQ01OQ01OQ02OQ02OQ02OQ01

/-! ## The factorial identity `(2n)! = C(2n,n)·(n!)²` -/

/-- `(2n)! = C(2n,n)·(n!)²`, cast to `ℝ`.  This is the central-binomial
specialisation of `Nat.choose_mul_factorial_mul_factorial`. -/
theorem two_mul_factorial_eq (n : ℕ) :
    ((2 * n)! : ℝ) = (centralBinom n : ℝ) * ((n ! : ℝ) * (n ! : ℝ)) := by
  have h : centralBinom n * (n ! * n !) = (2 * n)! := by
    have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h2
    rw [show (2 * n).choose n = centralBinom n from rfl, mul_assoc] at h2
    exact h2
  exact_mod_cast h.symm

/-! ## The square-root free identity -/

/-- **Bridge identity.** For `n ≥ 1`,
`C(2n,n)²·n / 16^n = stirlingSeq (2n)² / stirlingSeq n⁴`.
Squaring removes every square root from the Stirling sequence, leaving a purely
algebraic identity. -/
theorem cb_sq_identity (n : ℕ) (hn : 1 ≤ n) :
    (centralBinom n : ℝ) ^ 2 * n / 16 ^ n
      = stirlingSeq (2 * n) ^ 2 / stirlingSeq n ^ 4 := by
  have hm : (0 : ℝ) < n := by exact_mod_cast hn
  -- closed form for `stirlingSeq n ^ 4`
  have hSn : stirlingSeq n ^ 4
      = (n ! : ℝ) ^ 4
          / ((2 * (n : ℝ)) ^ 2 * ((n : ℝ) / Real.exp 1) ^ (4 * n)) := by
    have e1 : (√(2 * (n : ℝ))) ^ 4 = (2 * (n : ℝ)) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
    have e2 : (((n : ℝ) / Real.exp 1) ^ n) ^ 4 = ((n : ℝ) / Real.exp 1) ^ (4 * n) := by
      rw [← pow_mul, mul_comm n 4]
    rw [stirlingSeq, div_pow, mul_pow, e1, e2]
  -- closed form for `stirlingSeq (2n) ^ 2`
  have hS2n : stirlingSeq (2 * n) ^ 2
      = ((centralBinom n : ℝ) * ((n ! : ℝ) * (n ! : ℝ))) ^ 2
          / ((2 * (2 * (n : ℝ)))
              * (16 ^ n * ((n : ℝ) / Real.exp 1) ^ (4 * n))) := by
    have e3 : (√(2 * ((2 * n : ℕ) : ℝ))) ^ 2 = 2 * (2 * (n : ℝ)) := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have e4 : ((((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)) ^ 2
        = 16 ^ n * ((n : ℝ) / Real.exp 1) ^ (4 * n) := by
      rw [← pow_mul, show (2 * n) * 2 = 4 * n by ring]
      push_cast
      rw [show (2 * (n : ℝ)) / Real.exp 1 = 2 * ((n : ℝ) / Real.exp 1) by ring, mul_pow,
          pow_mul (2 : ℝ) 4 n, show (2 : ℝ) ^ 4 = 16 by norm_num]
    rw [stirlingSeq, div_pow, mul_pow, e3, e4, two_mul_factorial_eq n]
  -- assemble
  have hfac : (n ! : ℝ) ≠ 0 := by exact_mod_cast n.factorial_pos.ne'
  have hnne : (n : ℝ) ≠ 0 := hm.ne'
  have hPne : ((n : ℝ) / Real.exp 1) ^ (4 * n) ≠ 0 := by positivity
  have h16 : (16 : ℝ) ^ n ≠ 0 := by positivity
  rw [hS2n, hSn]
  field_simp

/-! ## The exact limit -/

/-- **The exact Wallis constant.** The normalised central binomial coefficient
converges to `1/√π`:
`C(2n,n)·√n / 4^n → 1/√π`. -/
theorem centralBinom_mul_sqrt_div_tendsto :
    Tendsto (fun n => (centralBinom n : ℝ) * √n / 4 ^ n) atTop (𝓝 (1 / √π)) := by
  -- `n ↦ 2n` tends to `atTop`
  have htends2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by show n ≤ 2 * n; omega) tendsto_id
  have h2 : Tendsto (fun n : ℕ => stirlingSeq (2 * n)) atTop (𝓝 (√π)) :=
    tendsto_stirlingSeq_sqrt_pi.comp htends2n
  have h2sq : Tendsto (fun n : ℕ => stirlingSeq (2 * n) ^ 2) atTop (𝓝 π) := by
    have := h2.pow 2
    rwa [Real.sq_sqrt Real.pi_nonneg] at this
  have h4 : Tendsto (fun n : ℕ => stirlingSeq n ^ 4) atTop (𝓝 (π ^ 2)) := by
    have := tendsto_stirlingSeq_sqrt_pi.pow 4
    rwa [show (√π) ^ 4 = π ^ 2 by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt Real.pi_nonneg]] at this
  have hπ2 : (π : ℝ) ^ 2 ≠ 0 := by positivity
  have hratio : Tendsto (fun n : ℕ => stirlingSeq (2 * n) ^ 2 / stirlingSeq n ^ 4)
      atTop (𝓝 (π / π ^ 2)) := h2sq.div h4 hπ2
  have hval : (π : ℝ) / π ^ 2 = 1 / π := by
    rw [sq, ← div_div, div_self Real.pi_ne_zero]
  rw [hval] at hratio
  -- transfer the limit to the square of the target sequence
  have hfsq : Tendsto (fun n : ℕ => ((centralBinom n : ℝ) * √n / 4 ^ n) ^ 2)
      atTop (𝓝 (1 / π)) := by
    refine hratio.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← cb_sq_identity n hn, div_pow, mul_pow, Real.sq_sqrt (by positivity),
        show ((4 : ℝ) ^ n) ^ 2 = 16 ^ n by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  -- square root: the target sequence is non-negative
  have hf := hfsq.sqrt
  have hsv : √(1 / π) = 1 / √π := by rw [one_div, Real.sqrt_inv, one_div]
  rw [hsv] at hf
  exact hf.congr (fun n => Real.sqrt_sq (by positivity))

/-! ## Consequences -/

/-- **Equivalent normalisation.** `C(2n,n)·√(π n) / 4^n → 1`, i.e.
`C(2n,n) ∼ 4^n/√(π n)`. -/
theorem centralBinom_mul_sqrt_pi_div_tendsto_one :
    Tendsto (fun n => (centralBinom n : ℝ) * √(π * n) / 4 ^ n) atTop (𝓝 1) := by
  have hf := centralBinom_mul_sqrt_div_tendsto
  have hmul := (tendsto_const_nhds (x := √π) (f := (atTop : Filter ℕ))).mul hf
  rw [show √π * (1 / √π) = 1 by
        rw [mul_one_div, div_self (Real.sqrt_ne_zero'.mpr Real.pi_pos)]] at hmul
  refine hmul.congr (fun n => ?_)
  rw [Real.sqrt_mul Real.pi_nonneg]
  ring

/-- **Bracket recovery.** The exact constant `1/√π` lies inside the parent's
two-sided bracket `[1/2, 1/√3]`; equivalently `3 ≤ π ≤ 4`. -/
theorem sqrt_pi_inv_mem_bracket : 1 / 2 ≤ 1 / √π ∧ 1 / √π ≤ 1 / √3 := by
  have hub : √π ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (le_of_lt Real.pi_lt_four)
  have hlb : √3 ≤ √π := Real.sqrt_le_sqrt (le_of_lt Real.pi_gt_three)
  refine ⟨?_, ?_⟩
  · exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr Real.pi_pos) hub
  · exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) hlb

end Erdos396OQ01OQ01OQ02OQ02OQ02OQ01
