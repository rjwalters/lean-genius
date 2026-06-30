import Mathlib

/-
# Arithmetic Series OQ-04 / OQ-02: Generating functions for Bernoulli and power sums

## The Open Question (parent OQ-04, second open question)

Faulhaber's formula (OQ-04) writes the power sum `∑_{k=1}^n k^p` as a polynomial in `n` with
Bernoulli-number coefficients.  The engine behind it is the **exponential generating function**
of the Bernoulli numbers:
$$\sum_{n=0}^{\infty} B_n \frac{x^n}{n!} \;=\; \frac{x}{e^x - 1}.$$

> **Can we formalize this generating-function identity for the Bernoulli sums in Lean 4?**

## Answer

**Yes.**  As a formal power series over `ℚ`, the identity reads
`bernoulliPowerSeries ℚ * (exp ℚ - 1) = X`, which is Mathlib's
`bernoulliPowerSeries_mul_exp_sub_one`.  We restate it as `bernoulli_egf` to record the direct
answer.

The interesting content of this leaf is to take that generating function and make the
**Faulhaber bridge** completely explicit at the level of generating functions — a derivation that
is *not* in Mathlib:

* `powerSum_egf` / `powerSum_egf'` — the **exponential generating function of the power sums**
  `S_p(n) = ∑_{k=0}^{n-1} k^p`:
  $$\Big(\sum_{p=0}^{\infty} S_p(n)\,\tfrac{x^p}{p!}\Big)\,(e^x - 1) \;=\; e^{nx} - 1,
    \qquad\text{i.e.}\qquad \sum_{p} S_p(n)\,\tfrac{x^p}{p!} = \frac{e^{nx}-1}{e^x-1}.$$
  This is the geometric-series identity `(∑_{k<n} (e^x)^k)(e^x - 1) = (e^x)^n - 1` read off
  coefficient-by-coefficient via Mathlib's `exp_pow_sum`.

* `faulhaber_bernoulli_egf` — multiplying the power-sum generating function by `x` equals
  `(e^{nx} - 1)` times the **Bernoulli** generating function:
  $$\Big(\sum_p S_p(n)\,\tfrac{x^p}{p!}\Big)\,x \;=\; (e^{nx} - 1)\,\frac{x}{e^x-1}.$$
  This is the precise generating-function statement of "power sums = Bernoulli sums": it follows
  purely formally from the two product identities above, with no series inversion required (the
  factor `e^x - 1` is shared, so it cancels at the level of products in the commutative ring of
  power series).

## Why this is not just an alias

`bernoulliPowerSeries_mul_exp_sub_one` is the *Bernoulli* generating function.  The power-sum
generating function and the bridge connecting the two are assembled here from Mathlib's
`exp_pow_sum`, `geom_sum_mul`, `exp_pow_eq_rescale_exp`, and `coeff_rescale`; neither the
power-sum EGF nor the bridge is a Mathlib lemma.  Concrete coefficients (`S_1(4) = 6`,
`S_2(4)/2! = 7`) are checked to ground the abstraction.

## Convention

`S_p(n) := ∑_{k ∈ range n} k^p = 0^p + 1^p + ⋯ + (n-1)^p` (upper index exclusive), matching the
`Finset.range` convention used by Mathlib's `sum_range_pow_eq_bernoulli_sub`.  In particular
`0^0 = 1`, so `S_0(n) = n`.

Tags: number-theory, generating-functions, bernoulli, power-sums, faulhaber, power-series
-/

noncomputable section

open Finset BigOperators PowerSeries Nat

namespace ArithmeticSeriesOQ04OQ02

/-
═══════════════════════════════════════════════════════════════════════════════
  1. The Bernoulli generating function (the direct answer)
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **The exponential generating function of the Bernoulli numbers.**
As a formal power series over `ℚ`,
`(∑ B_n X^n / n!) · (exp - 1) = X`, i.e. `∑ B_n X^n/n! = X/(exp - 1)`.
This is the formalization asked for by the open question; it is Mathlib's
`bernoulliPowerSeries_mul_exp_sub_one`, restated here as the headline answer. -/
theorem bernoulli_egf :
    bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) = (PowerSeries.X : PowerSeries ℚ) :=
  bernoulliPowerSeries_mul_exp_sub_one ℚ

/-
═══════════════════════════════════════════════════════════════════════════════
  2. The exponential generating function of the power sums S_p(n)
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The power-sum power series `∑_p S_p(n) X^p/p!` equals the finite geometric sum
`∑_{k<n} (exp)^k`. This is exactly Mathlib's `exp_pow_sum`, with the `algebraMap ℚ ℚ`
simplified away. -/
theorem powerSumSeries_eq_geom (n : ℕ) :
    (PowerSeries.mk fun p => ∑ k ∈ Finset.range n, (k : ℚ) ^ p / p !)
      = ∑ k ∈ Finset.range n, PowerSeries.exp ℚ ^ k := by
  rw [PowerSeries.exp_pow_sum]
  simp [div_eq_mul_inv]

/-- **Exponential generating function of the power sums (product form).**
`(∑_p S_p(n) X^p/p!) · (exp - 1) = exp^n - 1`. -/
theorem powerSum_egf (n : ℕ) :
    (PowerSeries.mk fun p => ∑ k ∈ Finset.range n, (k : ℚ) ^ p / p !) * (PowerSeries.exp ℚ - 1)
      = PowerSeries.exp ℚ ^ n - 1 := by
  rw [powerSumSeries_eq_geom]
  exact geom_sum_mul (PowerSeries.exp ℚ) n

/-- **Exponential generating function of the power sums (closed form).**
`(∑_p S_p(n) X^p/p!) · (exp - 1) = (∑_p n^p X^p/p!) - 1`, i.e.
`∑_p S_p(n) X^p/p! = (e^{nx} - 1)/(e^x - 1)`. -/
theorem powerSum_egf' (n : ℕ) :
    (PowerSeries.mk fun p => ∑ k ∈ Finset.range n, (k : ℚ) ^ p / p !) * (PowerSeries.exp ℚ - 1)
      = (PowerSeries.mk fun p => (n : ℚ) ^ p / p !) - 1 := by
  rw [powerSum_egf]
  congr 1
  ext p
  rw [PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    PowerSeries.coeff_mk]
  simp [div_eq_mul_inv]

/-
═══════════════════════════════════════════════════════════════════════════════
  3. The Faulhaber bridge: power sums = Bernoulli sums (generating-function form)
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **The Faulhaber bridge at the level of generating functions.**
Multiplying the power-sum generating function by `X` equals `(e^{nx} - 1)` times the Bernoulli
generating function:
`(∑_p S_p(n) X^p/p!) · X = ((∑_p n^p X^p/p!) - 1) · (∑_m B_m X^m/m!)`.

This is the precise statement that the power sums are "Bernoulli sums": it follows purely formally
from `bernoulli_egf` and `powerSum_egf'` — the common factor `exp - 1` cancels at the level of
products, so no power-series inversion is needed. -/
theorem faulhaber_bernoulli_egf (n : ℕ) :
    (PowerSeries.mk fun p => ∑ k ∈ Finset.range n, (k : ℚ) ^ p / p !) * PowerSeries.X
      = ((PowerSeries.mk fun p => (n : ℚ) ^ p / p !) - 1) * bernoulliPowerSeries ℚ := by
  have hB := bernoulli_egf
  have hS := powerSum_egf' n
  rw [← hB, ← hS]
  ring

/-
═══════════════════════════════════════════════════════════════════════════════
  4. Concrete coefficients (grounding the abstraction)
═══════════════════════════════════════════════════════════════════════════════
  The coefficient of X^p in the power-sum generating function is S_p(n)/p!.
  For n = 4: S_1(4) = 0+1+2+3 = 6 and S_2(4) = 0+1+4+9 = 14, so the X^2 coefficient is 14/2 = 7.
-/

/-- The `X^1` coefficient of the power-sum series for `n = 4` is `S_1(4)/1! = 6`. -/
theorem coeff_one_powerSum_four :
    (PowerSeries.coeff (R := ℚ) 1) (PowerSeries.mk fun p => ∑ k ∈ Finset.range 4, (k : ℚ) ^ p / p !) = 6 := by
  rw [PowerSeries.coeff_mk]
  norm_num [Finset.sum_range_succ]

/-- The `X^2` coefficient of the power-sum series for `n = 4` is `S_2(4)/2! = 14/2 = 7`. -/
theorem coeff_two_powerSum_four :
    (PowerSeries.coeff (R := ℚ) 2) (PowerSeries.mk fun p => ∑ k ∈ Finset.range 4, (k : ℚ) ^ p / p !) = 7 := by
  rw [PowerSeries.coeff_mk]
  norm_num [Finset.sum_range_succ]

/-- `S_0(n) = n`: the constant-coefficient (`X^0`) power sum counts the terms. -/
theorem coeff_zero_powerSum (n : ℕ) :
    (PowerSeries.coeff (R := ℚ) 0) (PowerSeries.mk fun p => ∑ k ∈ Finset.range n, (k : ℚ) ^ p / p !) = n := by
  rw [PowerSeries.coeff_mk]
  simp

end ArithmeticSeriesOQ04OQ02
