/-
The Central Binomial Asymptotic from Wallis:  C(2n,n) · √(πn) / 4ⁿ → 1

Source: Open question from stirling-formula-oq-03 (the standalone Wallis limit)
Status: VERIFIED (0 axioms, 0 sorries)

The parent entry `StirlingFormulaOQ03` isolates Wallis' product as a standalone
limit `∏ 4k²/(4k²−1) → π/2`. Mathlib records the same limit through its internal
sequence `Real.Wallis.W` and, crucially, the *exact factorial form*

  `W n = 2^(4n) · (n!)⁴ / ((2n)!² · (2n+1))`   (`Real.Wallis.W_eq_factorial_ratio`).

This file turns that exact identity into the **asymptotics of the central
binomial coefficient** `C(2n,n) = Nat.centralBinom n`. The bridge is the
elementary factorial factorization `(2n)! = C(2n,n) · (n!)²`
(`Nat.choose_mul_factorial_mul_factorial`), which collapses Wallis' ratio to

  **`four_pow_div_centralBinom_sq`**:
    `(4ⁿ / C(2n,n))² = W n · (2n+1)`.

Since `W n → π/2`, the right side, divided by `n`, tends to `π`, giving the three
classical asymptotic forms:

  * `centralBinom_sq_div_tendsto`:  `(4ⁿ / C(2n,n))² / n → π`
  * `four_pow_div_centralBinom_sqrt_tendsto`:  `4ⁿ / (C(2n,n)·√n) → √π`
  * `centralBinom_asymptotic`:  `C(2n,n) · √(πn) / 4ⁿ → 1`

The last is the textbook statement `C(2n,n) ~ 4ⁿ/√(πn)`.

## Relation to Mathlib

Mathlib has central binomial *bounds* (`Nat.four_pow_lt_mul_centralBinom`,
`Bertrand`) and the Wallis/Stirling machinery, but it does **not** state the
asymptotic equivalent of the central binomial coefficient. We assemble it from
`Real.Wallis.W_eq_factorial_ratio` and `Real.Wallis.tendsto_W_nhds_pi_div_two`.
-/

import Mathlib

open Filter Topology Nat
open scoped Real

namespace StirlingFormulaOQ03OQ02

/-- Real-valued central binomial coefficient, for convenience. -/
noncomputable def cb (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ)

theorem cb_pos (n : ℕ) : 0 < cb n := by
  unfold cb; exact_mod_cast Nat.centralBinom_pos n

theorem cb_ne_zero (n : ℕ) : cb n ≠ 0 := (cb_pos n).ne'

/-! ## Part I: The exact Wallis-to-central-binomial identity -/

/-- The factorial factorization of the doubled factorial through the central
binomial coefficient, cast to `ℝ`:  `(2n)! = C(2n,n) · (n!)²`. -/
theorem factorial_two_mul (n : ℕ) :
    ((2 * n)! : ℝ) = cb n * (n ! : ℝ) ^ 2 := by
  have hnat : (Nat.centralBinom n) * n ! * n ! = (2 * n)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    -- `(2n).choose n * n ! * (2n - n)! = (2n)!`, and `2n - n = n`
    rwa [← Nat.centralBinom_eq_two_mul_choose, show 2 * n - n = n by omega] at h
  have hcast := congrArg (Nat.cast : ℕ → ℝ) hnat
  push_cast at hcast
  rw [cb]; linear_combination -hcast

/-- **The exact Wallis identity for the central binomial coefficient.**
`(4ⁿ / C(2n,n))² = W n · (2n+1)`. -/
theorem four_pow_div_centralBinom_sq (n : ℕ) :
    ((4 : ℝ) ^ n / cb n) ^ 2 = Real.Wallis.W n * (2 * n + 1) := by
  have hcb := cb_ne_zero n
  have hfac : (n ! : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hodd : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h16 : ((4 : ℝ) ^ n) ^ 2 = (2 : ℝ) ^ (4 * n) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    ring_nf
  rw [Real.Wallis.W_eq_factorial_ratio, factorial_two_mul, ← h16]
  field_simp

/-! ## Part II: The asymptotics -/

/-- `(4ⁿ / C(2n,n))² / n → π`.  Dividing the exact identity by `n`, the right
side is `W n · (2n+1)/n = W n · (2 + 1/n) → (π/2)·2 = π`. -/
theorem centralBinom_sq_div_tendsto :
    Tendsto (fun n : ℕ => ((4 : ℝ) ^ n / cb n) ^ 2 / n) atTop (𝓝 π) := by
  -- target sequence equals `W n * (2 + 1/n)` eventually
  have hW : Tendsto (fun n : ℕ => Real.Wallis.W n * (2 + 1 / (n : ℝ))) atTop (𝓝 (π / 2 * 2)) := by
    refine Real.Wallis.tendsto_W_nhds_pi_div_two.mul ?_
    have : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds.add this)
  have hπ : π / 2 * 2 = π := by ring
  rw [hπ] at hW
  refine hW.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [four_pow_div_centralBinom_sq]
  field_simp

/-- `4ⁿ / (C(2n,n)·√n) → √π`.  Square root of the previous limit. -/
theorem four_pow_div_centralBinom_sqrt_tendsto :
    Tendsto (fun n : ℕ => (4 : ℝ) ^ n / (cb n * Real.sqrt n)) atTop (𝓝 (Real.sqrt π)) := by
  have h := centralBinom_sq_div_tendsto.sqrt
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  -- `√((4ⁿ/cb)²/n) = 4ⁿ/(cb·√n)`
  rw [Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (div_nonneg (by positivity) (cb_pos n).le), div_div]

/-- **Central binomial asymptotic.** `C(2n,n) · √(πn) / 4ⁿ → 1`, i.e.
`C(2n,n) ~ 4ⁿ / √(πn)`. -/
theorem centralBinom_asymptotic :
    Tendsto (fun n : ℕ => cb n * Real.sqrt (π * n) / (4 : ℝ) ^ n) atTop (𝓝 1) := by
  have hsπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  -- `√π / (4ⁿ/(cb·√n)) → √π/√π = 1`
  have h := (tendsto_const_nhds (x := Real.sqrt π)).div
    four_pow_div_centralBinom_sqrt_tendsto hsπ
  rw [div_self hsπ] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have ha : (0 : ℝ) < cb n := cb_pos n
  have hq : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  -- `cb · √(πn) / 4ⁿ = √π / (4ⁿ/(cb·√n))`
  simp only [Pi.div_apply]
  rw [Real.sqrt_mul Real.pi_nonneg]
  field_simp

end StirlingFormulaOQ03OQ02
