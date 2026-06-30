/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-02 → OQ-02 → OQ-01: the central binomial coefficient as a telescoping Wallis product

The parent `Erdos396OQ04OQ01OQ01OQ02OQ02` extracts the `1/2` critical exponent
of the central binomial coefficient `C(2n,n)` from its two-term recurrence by
the *additive* route: writing each normalised step `s k / 4 = 1 − (1/2)/(k+1)`,
the inequality `log y ≤ y − 1` telescopes the **logarithm** of the recurrence to
`log (C(2n,n)/4^n) = ∑_{k<n} log (s k / 4) ≤ −(1/2)·H_n`.

This file is the *multiplicative* twin — the same relationship to the parent
that the Catalan telescoping product `Erdos396OQ04OQ01OQ01OQ01` bears to the
Catalan `3/2`-exponent file.  Instead of taking logs we keep the product:
Mathlib's recurrence `(n+1)·C(2(n+1),n+1) = 2·(2n+1)·C(2n,n)` multiplies the
sequence by `s n = (4n+2)/(n+1)` at every step, so it collapses to a finite
product

  **`centralBinom_eq_prod`** : `(C(2n,n) : ℝ) = ∏_{k<n} s k`.

Normalising each factor by the limiting rate `4` turns this into the classical
**Wallis partial product** in closed form,

  `s k / 4 = (2k+1)/(2k+2)`,
  **`centralBinom_div_eq_wallis_prod`** : `C(2n,n)/4^n = ∏_{k<n} (2k+1)/(2k+2)`.

This is exactly `(2n−1)!! / (2n)!!`, the truncation of Wallis' product for
`2/π`.  Every factor `(2k+1)/(2k+2)` lies strictly in `(0,1)`, so the normalised
sequence is **strictly decreasing** (`centralBinom_div_strictAnti`); evaluated at
`0` the product is `1`, so for `n ≥ 1`

  **`centralBinom_lt_four_pow`** : `C(2n,n) < 4^n`,

the elementary `4^n` upper bound recovered *purely from the product*, with no
appeal to `(2n).choose n ≤ 2^{2n}`.  Taking logs of the product recovers the
parent's additive bridge (`log_centralBinom_eq_sum`), tying the two views
together.

No Stirling estimate and no asymptotic input is used.

Reference: https://erdosproblems.com/396
-/

import Mathlib

open Nat Finset

namespace Erdos396OQ01OQ01OQ02OQ02OQ01

/-! ## The central-binomial recurrence ratio `s n` -/

/-- The ratio of consecutive central binomial coefficients implied by Mathlib's
    recurrence `(n+1)·C(2(n+1),n+1) = 2·(2n+1)·C(2n,n)`:
    `s n = (4n+2)/(n+1)`. -/
noncomputable def cbRatio (n : ℕ) : ℝ := (4 * n + 2) / ((n : ℝ) + 1)

/-- `s n` is strictly positive. -/
theorem cbRatio_pos (n : ℕ) : 0 < cbRatio n := by
  rw [cbRatio]; positivity

/-- **The recurrence as a ratio.** `C(2(n+1),n+1) = s n · C(2n,n)` over `ℝ`,
    the normalised reading of `Nat.succ_mul_centralBinom_succ`. -/
theorem centralBinom_succ_eq_ratio_mul (n : ℕ) :
    (centralBinom (n + 1) : ℝ) = cbRatio n * centralBinom n := by
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.succ_mul_centralBinom_succ n)
  push_cast at h
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [cbRatio]
  field_simp
  linear_combination h

/-! ## The telescoping product -/

/-- **Telescoping product.** `(C(2n,n) : ℝ) = ∏_{k<n} s k`.

    The recurrence multiplies the sequence by `s n` at each step, so the product
    collapses; one-line induction via `Finset.prod_range_succ`. -/
theorem centralBinom_eq_prod (n : ℕ) :
    (centralBinom n : ℝ) = ∏ k ∈ Finset.range n, cbRatio k := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih, centralBinom_succ_eq_ratio_mul, mul_comm]

/-- **Log bridge to the additive view.** `log (C(2n,n)) = ∑_{k<n} log (s k)`.

    Taking logs of `centralBinom_eq_prod` turns the product into the sum that the
    parent file telescopes; the two views are the same identity read
    multiplicatively versus additively. -/
theorem log_centralBinom_eq_sum (n : ℕ) :
    Real.log (centralBinom n : ℝ) = ∑ k ∈ Finset.range n, Real.log (cbRatio k) := by
  rw [centralBinom_eq_prod, Real.log_prod]
  intro k _
  exact ne_of_gt (cbRatio_pos k)

/-! ## The normalised factor is the Wallis term `(2k+1)/(2k+2)` -/

/-- The recurrence ratio normalised by the limiting growth rate is the Wallis
    factor: `s k / 4 = (2k+1)/(2k+2)`. -/
theorem cbRatioQuarter_eq_wallis (k : ℕ) :
    cbRatio k / 4 = (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2) := by
  rw [cbRatio]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- Each Wallis factor is strictly positive. -/
theorem wallisFactor_pos (k : ℕ) : 0 < (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2) := by
  positivity

/-- Each Wallis factor is strictly less than `1`: `(2k+1)/(2k+2) < 1`. -/
theorem wallisFactor_lt_one (k : ℕ) : (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2) < 1 := by
  rw [div_lt_one (by positivity)]
  linarith

/-- The normalised step `s k / 4` lies strictly in `(0,1)`. -/
theorem cbRatioQuarter_lt_one (k : ℕ) : cbRatio k / 4 < 1 := by
  rw [cbRatioQuarter_eq_wallis]; exact wallisFactor_lt_one k

/-! ## The Wallis product form of `C(2n,n)/4^n` -/

/-- **Headline: the Wallis partial product.**
    `C(2n,n)/4^n = ∏_{k<n} (2k+1)/(2k+2)`.

    Dividing the telescoping product by `4^n = ∏_{k<n} 4` distributes over the
    product factor-by-factor; each factor becomes the Wallis term `(2k+1)/(2k+2)`.
    The right-hand side is `(2n−1)!!/(2n)!!`, the truncation of Wallis' product. -/
theorem centralBinom_div_eq_wallis_prod (n : ℕ) :
    (centralBinom n : ℝ) / 4 ^ n
      = ∏ k ∈ Finset.range n, (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2) := by
  have h4 : (4 : ℝ) ^ n = ∏ _k ∈ Finset.range n, (4 : ℝ) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [centralBinom_eq_prod, h4, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  exact cbRatioQuarter_eq_wallis k

/-! ## Strict monotonicity of the normalised sequence -/

/-- The normalised sequence is strictly positive. -/
theorem centralBinom_div_pos (n : ℕ) : 0 < (centralBinom n : ℝ) / 4 ^ n := by
  have := Nat.centralBinom_pos n; positivity

/-- **The normalised sequence is strictly decreasing.**
    `C(2(n+1),n+1)/4^{n+1} < C(2n,n)/4^n`, because the multiplicative step is the
    Wallis factor `s n / 4 < 1`. -/
theorem centralBinom_div_strictAnti :
    StrictAnti (fun n => (centralBinom n : ℝ) / 4 ^ n) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hstep : ((centralBinom (n + 1) : ℝ) / 4 ^ (n + 1))
      = (cbRatio n / 4) * ((centralBinom n : ℝ) / 4 ^ n) := by
    rw [centralBinom_succ_eq_ratio_mul]
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
    ring
  rw [hstep]
  calc (cbRatio n / 4) * ((centralBinom n : ℝ) / 4 ^ n)
      < 1 * ((centralBinom n : ℝ) / 4 ^ n) := by
        apply mul_lt_mul_of_pos_right (cbRatioQuarter_lt_one n) (centralBinom_div_pos n)
    _ = (centralBinom n : ℝ) / 4 ^ n := one_mul _

/-! ## The elementary `4^n` upper bound, recovered from the product -/

/-- **`C(2n,n) < 4^n` for `n ≥ 1`, purely from the product.**

    The normalised sequence starts at `C(0,0)/4^0 = 1` and strictly decreases, so
    `C(2n,n)/4^n < 1` for every `n ≥ 1`.  No `(2n).choose n ≤ 2^{2n}` is used. -/
theorem centralBinom_lt_four_pow {n : ℕ} (hn : 1 ≤ n) :
    (centralBinom n : ℝ) < 4 ^ n := by
  have h0 : (centralBinom 0 : ℝ) / 4 ^ 0 = 1 := by simp [Nat.centralBinom_zero]
  have hlt : (centralBinom n : ℝ) / 4 ^ n < 1 := by
    simpa only [h0] using centralBinom_div_strictAnti (show 0 < n from hn)
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  rw [div_lt_one h4] at hlt
  linarith

/-- **Natural-number form.** `C(2n,n) < 4^n` for `n ≥ 1`, transported from the
    real bound by casting. -/
theorem centralBinom_lt_four_pow_nat {n : ℕ} (hn : 1 ≤ n) :
    centralBinom n < 4 ^ n := by
  have h := centralBinom_lt_four_pow hn
  have hcast : ((4 ^ n : ℕ) : ℝ) = (4 : ℝ) ^ n := by push_cast; ring
  rw [← hcast] at h
  exact_mod_cast h

/-! ## Sanity checks -/

/-- The empty product is `1`, matching `C(0,0) = 1`. -/
example : (centralBinom 0 : ℝ) = ∏ k ∈ Finset.range 0, cbRatio k := centralBinom_eq_prod 0

/-- At `k = 0` the Wallis factor is `1/2`. -/
example : (2 * (0 : ℝ) + 1) / (2 * (0 : ℝ) + 2) = 1 / 2 := by norm_num

/-- `C(2,1) = 2`, and the Wallis product over `range 1` is `1/2`, so
    `2/4 = 1/2`. -/
example : (centralBinom 1 : ℝ) / 4 ^ 1 = 1 / 2 := by
  rw [centralBinom_div_eq_wallis_prod, Finset.prod_range_one]; norm_num

/-- The first strict drop: `C(2,1)/4 = 1/2 < 1 = C(0,0)/4^0`. -/
example : (centralBinom 1 : ℝ) / 4 ^ 1 < (centralBinom 0 : ℝ) / 4 ^ 0 :=
  centralBinom_div_strictAnti (by norm_num)

/-- `C(4,2) = 6 < 16 = 4^2`. -/
example : centralBinom 2 < 4 ^ 2 := centralBinom_lt_four_pow_nat (by norm_num)

end Erdos396OQ01OQ01OQ02OQ02OQ01
