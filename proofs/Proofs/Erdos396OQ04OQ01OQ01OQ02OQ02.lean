/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-02 → OQ-02: the `1/2` critical exponent of the central binomial coefficient

The sibling `Erdos396OQ04OQ01OQ01OQ02` extracts the `3/2` critical exponent of
the Catalan numbers from their two-term recurrence: writing each normalised step
`r k / 4 = 1 − (3/2)/(k+2)`, the elementary logarithm bound `log y ≤ y − 1`
telescopes to `catalan n / 4^n ≤ exp(−(3/2)·(H_{n+1} − 1)) ∼ n^{−3/2}`.

That entry's closing open question asked whether the *same* recurrence-level
machinery applied to the **central binomial coefficient** `C(2n,n)` recovers its
`1/2` exponent.  This file answers it affirmatively.  Mathlib's recurrence
`(n+1)·C(2(n+1),n+1) = 2·(2n+1)·C(2n,n)` reads as a ratio statement
`s n = (4n+2)/(n+1) = 4 − 2/(n+1)`, whose deficit `2/(n+1)` is the **un-shifted**
harmonic tail (compare the Catalan deficit `6/(n+2)`).  Normalising by the
limiting rate,

  `s k / 4 = 1 − (1/2)/(k+1)`,

the same `log y ≤ y − 1` gives `log (s k / 4) ≤ −(1/2)/(k+1)`, and telescoping
the recurrence through the logarithm yields

  `log (C(2n,n) / 4^n) = ∑_{k<n} log (s k / 4) ≤ −(1/2)·H_n`,

so

  **`centralBinom_div_le_exp`** : `C(2n,n) / 4^n ≤ exp(−(1/2)·H_n)`.

Because `H_n ∼ log n`, the right-hand side is `∼ n^{−1/2}`: the coefficient
`1/2` is exactly the critical exponent of the classical asymptotic
`C(2n,n) ∼ 4^n / √(π n)`.  Applying the inequality to the reciprocal gives the
matching lower bracket `log (s k / 4) ≥ −1/(2k+1)`, so `log (C(2n,n)/4^n)` is
pinned between two harmonic-type sums *both* carrying leading coefficient `1/2`.

The exponents of the two threads are tied together cleanly by
`C(2n,n) = (n+1)·catalan n` (**`centralBinom_eq_succ_mul_catalan`**): the extra
linear factor `n+1` is *exactly* the difference between the `1/2` exponent here
and the `3/2` exponent of the Catalan numbers — `3/2 = 1/2 + 1` at the level of
the polynomial decay rate.

Squeezing `0 ≤ C(2n,n)/4^n ≤ exp(−(1/2)·H_n) → 0` gives an independent,
rate-quantified proof that the normalised central binomial coefficients vanish
(**`centralBinom_div_tendsto_zero`**).  No Stirling estimate is used.

Reference: https://erdosproblems.com/396
-/

import Mathlib
import Proofs.Erdos396OQ04OQ01OQ01

open Nat Filter Topology Finset

namespace Erdos396OQ01OQ01OQ02OQ02

open Erdos396OQ01OQ01

/-! ## The central-binomial recurrence ratio `s n` -/

/-- The ratio of consecutive central binomial coefficients implied by Mathlib's
    recurrence `(n+1)·C(2(n+1),n+1) = 2·(2n+1)·C(2n,n)`:
    `s n = (4n+2)/(n+1) = 4 − 2/(n+1)`. -/
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

/-! ## The normalised step `s k / 4` and its logarithm -/

/-- The recurrence ratio normalised by the limiting growth rate:
    `s k / 4 = 1 − (1/2)/(k+1)`. -/
theorem cbRatioQuarter_eq (k : ℕ) :
    cbRatio k / 4 = 1 - (1 / 2) / ((k : ℝ) + 1) := by
  rw [cbRatio]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The normalised step is strictly positive. -/
theorem cbRatioQuarter_pos (k : ℕ) : 0 < cbRatio k / 4 := by
  have := cbRatio_pos k; positivity

/-- **Upper bound on the log step.** `log (s k / 4) ≤ −(1/2)/(k+1)`.

    The elementary inequality `log y ≤ y − 1` at `y = s k / 4`, where
    `y − 1 = −(1/2)/(k+1)` is (a quarter of) the deficit `2/(k+1)`. -/
theorem log_cbRatioQuarter_le (k : ℕ) :
    Real.log (cbRatio k / 4) ≤ -(1 / 2) / ((k : ℝ) + 1) := by
  have h := Real.log_le_sub_one_of_pos (cbRatioQuarter_pos k)
  have he : cbRatio k / 4 - 1 = -(1 / 2) / ((k : ℝ) + 1) := by
    rw [cbRatioQuarter_eq]; ring
  rw [he] at h; exact h

/-- **Lower bound on the log step.** `log (s k / 4) ≥ −1/(2k+1)`.

    The same Mathlib inequality applied to the reciprocal:
    `(s k / 4)⁻¹ − 1 = 1/(2k+1)`. -/
theorem log_cbRatioQuarter_ge (k : ℕ) :
    -(1 / ((2 * (k : ℝ) + 1))) ≤ Real.log (cbRatio k / 4) := by
  have hpos := cbRatioQuarter_pos k
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hnum : (4 * (k : ℝ) + 2) ≠ 0 := by positivity
  have hden : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have he : (cbRatio k / 4)⁻¹ - 1 = 1 / (2 * (k : ℝ) + 1) := by
    rw [cbRatio]; field_simp; ring
  rw [he] at h
  linarith

/-! ## Telescoping the recurrence through the logarithm -/

/-- **Log-telescoping.** `log (C(2n,n) / 4^n) = ∑_{k<n} log (s k / 4)`.

    Each step multiplies by `s n`, so normalised by `4` the product collapses;
    taking logs turns the product into the sum. -/
theorem normLog_eq_sum (n : ℕ) :
    Real.log ((centralBinom n : ℝ) / 4 ^ n)
      = ∑ k ∈ Finset.range n, Real.log (cbRatio k / 4) := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ m ih =>
    have hcb : (0 : ℝ) < (centralBinom m : ℝ) / 4 ^ m := by
      have := Nat.centralBinom_pos m; positivity
    have hstep : ((centralBinom (m + 1) : ℝ) / 4 ^ (m + 1))
        = (cbRatio m / 4) * ((centralBinom m : ℝ) / 4 ^ m) := by
      rw [centralBinom_succ_eq_ratio_mul]
      have h4 : (4 : ℝ) ^ m ≠ 0 := by positivity
      field_simp
      ring
    rw [Finset.sum_range_succ, ← ih, hstep,
      Real.log_mul (ne_of_gt (cbRatioQuarter_pos m)) (ne_of_gt hcb)]
    ring

/-! ## The `1/2`-exponent bound -/

/-- **Quantitative upper bound on the log.**
    `log (C(2n,n) / 4^n) ≤ −(1/2)·H_n`. -/
theorem normLog_le (n : ℕ) :
    Real.log ((centralBinom n : ℝ) / 4 ^ n) ≤ -(1 / 2) * realHarmonic n := by
  rw [normLog_eq_sum]
  have hsum_le : ∑ k ∈ Finset.range n, Real.log (cbRatio k / 4)
      ≤ ∑ k ∈ Finset.range n, (-(1 / 2) / ((k : ℝ) + 1)) :=
    Finset.sum_le_sum (fun k _ => log_cbRatioQuarter_le k)
  have hval : ∑ k ∈ Finset.range n, (-(1 / 2) / ((k : ℝ) + 1))
      = -(1 / 2) * realHarmonic n := by
    rw [realHarmonic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [← hval]; exact hsum_le

/-- **Headline: the `1/2`-exponent decay bound.**
    `C(2n,n) / 4^n ≤ exp(−(1/2)·H_n)`.

    Since `H_n ∼ log n`, the bound is `∼ n^{−1/2}`: the recurrence alone forces
    the critical exponent `1/2` of `C(2n,n) ∼ 4^n / √(π n)`. -/
theorem centralBinom_div_le_exp (n : ℕ) :
    (centralBinom n : ℝ) / 4 ^ n ≤ Real.exp (-(1 / 2) * realHarmonic n) := by
  have hpos : (0 : ℝ) < (centralBinom n : ℝ) / 4 ^ n := by
    have := Nat.centralBinom_pos n; positivity
  calc (centralBinom n : ℝ) / 4 ^ n
      = Real.exp (Real.log ((centralBinom n : ℝ) / 4 ^ n)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (-(1 / 2) * realHarmonic n) := Real.exp_le_exp.mpr (normLog_le n)

/-- **Multiplicative form.** `C(2n,n) ≤ 4^n · exp(−(1/2)·H_n)`. -/
theorem centralBinom_le_exp_mul (n : ℕ) :
    (centralBinom n : ℝ) ≤ 4 ^ n * Real.exp (-(1 / 2) * realHarmonic n) := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have h := centralBinom_div_le_exp n
  rw [div_le_iff₀ h4] at h
  linarith [h]

/-- **Two-sided log bracket.** The recurrence pins `log (C(2n,n) / 4^n)` between
    two harmonic-type sums, *both* with leading coefficient `1/2`:
    `−∑_{k<n} 1/(2k+1) ≤ log (C(2n,n) / 4^n) ≤ −(1/2)·H_n`. -/
theorem normLog_bracket (n : ℕ) :
    -(∑ k ∈ Finset.range n, 1 / (2 * (k : ℝ) + 1)) ≤ Real.log ((centralBinom n : ℝ) / 4 ^ n)
      ∧ Real.log ((centralBinom n : ℝ) / 4 ^ n) ≤ -(1 / 2) * realHarmonic n := by
  refine ⟨?_, normLog_le n⟩
  rw [normLog_eq_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum (fun k _ => log_cbRatioQuarter_ge k)

/-! ## Structural link to the Catalan `3/2` exponent -/

/-- **`C(2n,n) = (n+1)·catalan n`** over `ℝ`.  The linear factor `n+1` is exactly
    the difference between the `1/2` exponent of `C(2n,n)` proved here and the
    `3/2` exponent of `catalan n` proved in the sibling: `3/2 = 1/2 + 1` at the
    level of polynomial decay. -/
theorem centralBinom_eq_succ_mul_catalan (n : ℕ) :
    (centralBinom n : ℝ) = ((n : ℝ) + 1) * catalan n := by
  have h := congrArg (Nat.cast (R := ℝ)) (succ_mul_catalan_eq_centralBinom n)
  push_cast at h
  linarith [h]

/-- The normalised Catalan ratio is the normalised central-binomial ratio divided
    by the linear factor: `catalan n / 4^n = (C(2n,n)/4^n) / (n+1)`. -/
theorem catalan_div_eq_centralBinom_div (n : ℕ) :
    (catalan n : ℝ) / 4 ^ n = ((centralBinom n : ℝ) / 4 ^ n) / ((n : ℝ) + 1) := by
  rw [centralBinom_eq_succ_mul_catalan]
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ## Independent convergence with explicit rate -/

/-- The exponential bound vanishes: `exp(−(1/2)·H_n) → 0`, driven by the
    divergence of the harmonic series `H_n → ∞`. -/
theorem expBound_tendsto_zero :
    Tendsto (fun n => Real.exp (-(1 / 2) * realHarmonic n)) atTop (𝓝 0) := by
  have hbot : Tendsto (fun n => -(1 / 2) * realHarmonic n) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)
      realHarmonic_tendsto_atTop
  exact Real.tendsto_exp_atBot.comp hbot

/-- **Independent, rate-quantified proof that the normalised central binomial
    coefficients vanish.** `C(2n,n) / 4^n → 0`, squeezed by the explicit
    `1/2`-exponent bound rather than by Stirling. -/
theorem centralBinom_div_tendsto_zero :
    Tendsto (fun n => (centralBinom n : ℝ) / 4 ^ n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) centralBinom_div_le_exp expBound_tendsto_zero

/-! ## Sanity checks -/

/-- At `k = 0` the normalised step is `s 0 / 4 = 1/2`. -/
example : cbRatio 0 / 4 = 1 / 2 := by rw [cbRatioQuarter_eq]; norm_num

/-- The per-step upper bound at `k = 0` is `−(1/2)/1 = −1/2`. -/
example : (-(1 / 2) / ((0 : ℝ) + 1)) = -(1 / 2) := by norm_num

/-- `C(0,0) = 1`, `catalan 0 = 1`, so the structural identity reads `1 = 1·1`. -/
example : (centralBinom 0 : ℝ) = ((0 : ℝ) + 1) * catalan 0 := by
  rw [centralBinom_eq_succ_mul_catalan]; norm_num

/-- `C(2,1) = 2 = (1+1)·catalan 1 = 2·1`. -/
example : (centralBinom 1 : ℝ) = ((1 : ℝ) + 1) * catalan 1 := by
  rw [centralBinom_eq_succ_mul_catalan]; norm_num

end Erdos396OQ01OQ01OQ02OQ02
