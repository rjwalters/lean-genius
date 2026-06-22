/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-02: the `3/2` critical exponent of Catalan growth emerges from the recurrence

The grandparent `Erdos396OQ04OQ01` reads the two-term Catalan recurrence as a
statement about the ratio of consecutive Catalan numbers,
`r n = (4n+2)/(n+2) = 4 − 6/(n+2)`, and the parent `Erdos396OQ04OQ01OQ01` shows
the **deficit** `δ n = 4 − r n = 6/(n+2)` is the tail of a harmonic series, with
`∑_{k<n} δ k = 6·(H_{n+1} − 1)` diverging.  That qualitative observation explains
*why* `catalan n` is sub-`4^n` by a polynomial factor.

This follow-up makes the polynomial factor **quantitative** and, crucially,
extracts its exponent.  Writing each multiplicative step normalised by the
limiting rate, `r k / 4 = 1 − (3/2)/(k+2)`, the elementary logarithm bound
`log y ≤ y − 1` gives `log (r k / 4) ≤ −(3/2)/(k+2)`.  Telescoping the recurrence
through the logarithm,

  `log (catalan n / 4^n) = ∑_{k<n} log (r k / 4) ≤ −(3/2)·(H_{n+1} − 1)`,

so the normalised Catalan numbers obey the explicit bound

  **`catalan_div_le_exp`** : `catalan n / 4^n ≤ exp(−(3/2)·(H_{n+1} − 1))`.

Because `H_{n+1} − 1 ∼ log n`, the right-hand side is `∼ n^{−3/2}`: the
coefficient `3/2` is *exactly* the critical exponent appearing in the classical
asymptotic `catalan n ∼ 4^n / (n^{3/2} √π)`.  The same Mathlib inequality applied
to the reciprocal yields a matching lower bound `log (r k / 4) ≥ −3/(2k+1)`, so
the recurrence pins `log (catalan n / 4^n)` between two harmonic-type sums *both*
carrying the leading coefficient `3/2` — the exponent is forced by the recurrence,
not an artefact of one estimate.

Squeezing `0 ≤ catalan n / 4^n ≤ exp(−(3/2)(H_{n+1} − 1)) → 0` gives an
**independent, rate-quantified proof** that the normalised Catalan numbers vanish
(**`catalan_div_tendsto_zero`**), driven entirely by the divergence of the
harmonic deficit sum from the parent.

No Stirling estimate is used; everything follows from the recurrence ratio, the
parent's harmonic deficit identity, and `Real.log_le_sub_one_of_pos`.

Reference: https://erdosproblems.com/396
-/

import Mathlib
import Proofs.Erdos396OQ04OQ01OQ01

open Nat Filter Topology Finset

namespace Erdos396OQ01OQ01OQ02

open Erdos396OQ01 Erdos396OQ01OQ01

/-! ## The normalised step `r k / 4` and its logarithm -/

/-- The recurrence ratio normalised by the limiting growth rate:
    `r k / 4 = 1 − (3/2)/(k+2)`. -/
theorem ratioQuarter_eq (k : ℕ) :
    catalanRatio k / 4 = 1 - (3 / 2) / ((k : ℝ) + 2) := by
  rw [ratio_eq_four_sub]; ring

/-- The normalised step is strictly positive. -/
theorem ratioQuarter_pos (k : ℕ) : 0 < catalanRatio k / 4 := by
  have := ratio_pos k; positivity

/-- **Upper bound on the log step.** `log (r k / 4) ≤ −(3/2)/(k+2)`.

    This is the elementary inequality `log y ≤ y − 1` at `y = r k / 4`, where
    `y − 1 = −(3/2)/(k+2)` is (a quarter of) the parent's deficit. -/
theorem log_ratioQuarter_le (k : ℕ) :
    Real.log (catalanRatio k / 4) ≤ -(3 / 2) / ((k : ℝ) + 2) := by
  have h := Real.log_le_sub_one_of_pos (ratioQuarter_pos k)
  have he : catalanRatio k / 4 - 1 = -(3 / 2) / ((k : ℝ) + 2) := by
    rw [ratioQuarter_eq]; ring
  rw [he] at h; exact h

/-- **Lower bound on the log step.** `log (r k / 4) ≥ −3/(2k+1)`.

    The same Mathlib inequality applied to the reciprocal `(r k / 4)⁻¹ = 4 / r k`:
    `log ((r k/4)⁻¹) ≤ (r k/4)⁻¹ − 1`, and `(r k/4)⁻¹ − 1 = 3/(2k+1)`. -/
theorem log_ratioQuarter_ge (k : ℕ) :
    -(3 / ((2 * (k : ℝ) + 1))) ≤ Real.log (catalanRatio k / 4) := by
  have hpos := ratioQuarter_pos k
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  -- `(r k / 4)⁻¹ − 1 = 3/(2k+1)`
  have hr : catalanRatio k = (4 * k + 2) / ((k : ℝ) + 2) := rfl
  have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  have hnum : (4 * (k : ℝ) + 2) ≠ 0 := by positivity
  have he : (catalanRatio k / 4)⁻¹ - 1 = 3 / (2 * (k : ℝ) + 1) := by
    rw [hr]; field_simp; ring
  rw [he] at h
  linarith

/-! ## Telescoping the recurrence through the logarithm -/

/-- **Log-telescoping.** `log (catalan n / 4^n) = ∑_{k<n} log (r k / 4)`.

    Each Catalan step multiplies by `r n`, so normalised by `4` at each step the
    product collapses; taking logs turns the product into the sum. -/
theorem normLog_eq_sum (n : ℕ) :
    Real.log ((catalan n : ℝ) / 4 ^ n)
      = ∑ k ∈ Finset.range n, Real.log (catalanRatio k / 4) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hcat : (0 : ℝ) < (catalan m : ℝ) / 4 ^ m := by
      have := catalan_pos m; positivity
    have hstep : ((catalan (m + 1) : ℝ) / 4 ^ (m + 1))
        = (catalanRatio m / 4) * ((catalan m : ℝ) / 4 ^ m) := by
      rw [catalan_succ_eq_ratio_mul]
      have h4 : (4 : ℝ) ^ m ≠ 0 := by positivity
      field_simp
      ring
    rw [Finset.sum_range_succ, ← ih, hstep,
      Real.log_mul (ne_of_gt (ratioQuarter_pos m)) (ne_of_gt hcat)]
    ring

/-! ## The `3/2`-exponent bound -/

/-- **Quantitative upper bound on the log.**
    `log (catalan n / 4^n) ≤ −(3/2)·(H_{n+1} − 1)`.

    Summing the per-step bound and recognising `∑_{k<n} (3/2)/(k+2)` as a quarter
    of the parent's harmonic deficit sum `∑ δ k = 6·(H_{n+1} − 1)`. -/
theorem normLog_le (n : ℕ) :
    Real.log ((catalan n : ℝ) / 4 ^ n) ≤ -(3 / 2) * (realHarmonic (n + 1) - 1) := by
  rw [normLog_eq_sum]
  -- bound the sum termwise
  have hsum_le : ∑ k ∈ Finset.range n, Real.log (catalanRatio k / 4)
      ≤ ∑ k ∈ Finset.range n, (-(3 / 2) / ((k : ℝ) + 2)) :=
    Finset.sum_le_sum (fun k _ => log_ratioQuarter_le k)
  -- evaluate the comparison sum via the parent's deficit identity
  have hval : ∑ k ∈ Finset.range n, (-(3 / 2) / ((k : ℝ) + 2))
      = -(3 / 2) * (realHarmonic (n + 1) - 1) := by
    have hterm : ∀ k ∈ Finset.range n,
        (-(3 / 2) / ((k : ℝ) + 2)) = (-(1 / 4)) * catalanDeficit k := by
      intro k _
      rw [deficit_eq]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, deficit_sum_eq]
    ring
  rw [← hval]; exact hsum_le

/-- **Headline: the `3/2`-exponent decay bound.**
    `catalan n / 4^n ≤ exp(−(3/2)·(H_{n+1} − 1))`.

    Since `H_{n+1} − 1 ∼ log n`, the bound is `∼ n^{−3/2}`: the recurrence alone
    forces the critical exponent `3/2` of `catalan n ∼ 4^n / (n^{3/2} √π)`. -/
theorem catalan_div_le_exp (n : ℕ) :
    (catalan n : ℝ) / 4 ^ n ≤ Real.exp (-(3 / 2) * (realHarmonic (n + 1) - 1)) := by
  have hpos : (0 : ℝ) < (catalan n : ℝ) / 4 ^ n := by
    have := catalan_pos n; positivity
  calc (catalan n : ℝ) / 4 ^ n
      = Real.exp (Real.log ((catalan n : ℝ) / 4 ^ n)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (-(3 / 2) * (realHarmonic (n + 1) - 1)) :=
        Real.exp_le_exp.mpr (normLog_le n)

/-- **Multiplicative form.**
    `catalan n ≤ 4^n · exp(−(3/2)·(H_{n+1} − 1))`. -/
theorem catalan_le_exp_mul (n : ℕ) :
    (catalan n : ℝ) ≤ 4 ^ n * Real.exp (-(3 / 2) * (realHarmonic (n + 1) - 1)) := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have h := catalan_div_le_exp n
  rw [div_le_iff₀ h4] at h
  linarith [h]

/-- **Two-sided log bracket.** The recurrence pins `log (catalan n / 4^n)` between
    two harmonic-type sums, *both* with leading coefficient `3/2`:
    `−∑_{k<n} 3/(2k+1) ≤ log (catalan n / 4^n) ≤ −(3/2)·(H_{n+1} − 1)`.

    The exponent `3/2` is therefore forced from both sides, not an artefact of a
    single estimate. -/
theorem normLog_bracket (n : ℕ) :
    -(∑ k ∈ Finset.range n, 3 / (2 * (k : ℝ) + 1)) ≤ Real.log ((catalan n : ℝ) / 4 ^ n)
      ∧ Real.log ((catalan n : ℝ) / 4 ^ n) ≤ -(3 / 2) * (realHarmonic (n + 1) - 1) := by
  refine ⟨?_, normLog_le n⟩
  rw [normLog_eq_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum (fun k _ => log_ratioQuarter_ge k)

/-! ## Independent convergence with explicit rate -/

/-- The exponential bound vanishes: `exp(−(3/2)·(H_{n+1} − 1)) → 0`.

    Driven entirely by the divergence of the parent's harmonic deficit sum. -/
theorem expBound_tendsto_zero :
    Tendsto (fun n => Real.exp (-(3 / 2) * (realHarmonic (n + 1) - 1))) atTop (𝓝 0) := by
  have hH : Tendsto (fun n => realHarmonic (n + 1)) atTop atTop :=
    realHarmonic_tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hsub : Tendsto (fun n => realHarmonic (n + 1) - 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (-1) hH
  have hbot : Tendsto (fun n => -(3 / 2) * (realHarmonic (n + 1) - 1)) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by norm_num : -(3 / 2 : ℝ) < 0) hsub
  exact Real.tendsto_exp_atBot.comp hbot

/-- **Independent, rate-quantified proof that the normalised Catalan numbers
    vanish.** `catalan n / 4^n → 0`, squeezed by the explicit `3/2`-exponent
    bound rather than by Stirling. -/
theorem catalan_div_tendsto_zero :
    Tendsto (fun n => (catalan n : ℝ) / 4 ^ n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) catalan_div_le_exp expBound_tendsto_zero

/-! ## Sanity checks -/

/-- At `k = 0` the normalised step is `r 0 / 4 = 1/4`, and the upper bound there
    is `−(3/2)/2 = −3/4`. -/
example : catalanRatio 0 / 4 = 1 / 4 := by rw [ratioQuarter_eq]; norm_num

/-- `−(3/2)/(0+2) = −3/4` matches the per-step bound at `k = 0`. -/
example : (-(3 / 2) / ((0 : ℝ) + 2)) = -(3 / 4) := by norm_num

/-- The `n = 1` bound: `log (catalan 1 / 4) = log (1/4) ≤ −(3/2)(H₂ − 1) = −3/4`.
    Here `H₂ = 1 + 1/2`, so the right side is `−(3/2)(1/2) = −3/4`. -/
example : -(3 / 2 : ℝ) * (realHarmonic 2 - 1) = -(3 / 4) := by
  rw [realHarmonic_succ, realHarmonic_one]; norm_num

end Erdos396OQ01OQ01OQ02
