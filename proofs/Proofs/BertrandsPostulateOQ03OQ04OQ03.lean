import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Proofs.PrimeNumberTheorem
import Proofs.BertrandsPostulateOQ03
import Proofs.BertrandsPostulateOQ03OQ04

/-
# PNT Density Asymptotic for Prime Gaps: Filter Algebra Proof

## Open Question: bertrands-postulate-oq-03-oq-04-oq-03

The previous entry (OQ-04) proved `long_interval_density_from_pnt` with filter algebra
steps embedded inline. A natural follow-up question is:

**Can we isolate the key filter algebra steps as standalone, sorry-free lemmas?**

This file answers YES by cleanly separating the two structural filter compositions and
proving them independently.

### The Two Filter Algebra Steps

1. **PNT rescaling** (`pnt_at_scaled_point`): π((1+c)x)·log(x)/((1+c)x) → 1.
   Proof: compose PNT at (1+c)x with log(x)/log((1+c)x) → 1 (multiplication of limits).

2. **Density from PNT** (`pnt_density_long_interval`): (π((1+c)x) - π(x))·log(x)/(cx) → 1.
   Proof: algebraic decomposition as (1+c)/c × [step 1] - 1/c × [PNT], both → 1.

### Key Algebraic Identity

  (π((1+c)x) - π(x)) / (cx)
    = (1+c)/c · π((1+c)x)/((1+c)x)   — density up to (1+c)x
    - 1/c   · π(x)/x                  — density up to x

Both terms → 1/log(x) by PNT, so their combination → 1/log(x) with coefficient
(1+c)/c - 1/c = 1. This is the filter-algebraic identity underlying the long-interval
density result.

### Relationship to Open Problem

For h = cx (proportional to x), density follows from PNT alone — proved here.
For h = x^θ with θ < 1, density is open unconditionally. The filter algebra proof
for proportional intervals does not extend to sublinear intervals, which require
zero-density estimates beyond current Mathlib capabilities.
-/

noncomputable section

open Filter Topology Real
open PrimeNumberTheorem (primePi primeApprox primeNumberTheorem)

namespace BertrandsPostulateOQ03OQ04OQ03

-- ============================================================
-- PART 1: Log Ratio Lemma (local version)
-- ============================================================

/-- **log(x)/log((1+c)x) → 1** as x → ∞ for any fixed c > 0.

    Write log((1+c)x) = log(1+c) + log(x), so
    log(x)/log((1+c)x) = 1/(1 + log(1+c)/log(x)) → 1/(1+0) = 1.

    This is the key "change of logarithm" step connecting PNT at (1+c)x
    (which naturally uses log((1+c)x)) to expressions using log(x). -/
private lemma log_ratio_tendsto_one (c : ℝ) (hc : c > 0) :
    Tendsto (fun x : ℝ => Real.log x / Real.log ((1 + c) * x)) atTop (𝓝 1) := by
  have h1c_pos : (1 + c) > 0 := by linarith
  -- Write as 1/(1 + log(1+c)/log(x)) for large x (where log x > 0)
  have hsimp : ∀ᶠ x in atTop, Real.log x / Real.log ((1 + c) * x) =
      1 / (1 + Real.log (1 + c) / Real.log x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx_pos : (0 : ℝ) < x := by linarith
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    rw [Real.log_mul (ne_of_gt h1c_pos) (ne_of_gt hx_pos)]
    field_simp; ring
  -- log(1+c)/log(x) → 0 since log(x) → ∞
  have hdiv_zero : Tendsto (fun x : ℝ => Real.log (1 + c) / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  -- 1 + log(1+c)/log(x) → 1
  have hadd_one : Tendsto (fun x : ℝ => 1 + Real.log (1 + c) / Real.log x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hdiv_zero
  -- 1/(1 + log(1+c)/log(x)) → 1/1 = 1
  have hdiv_one : Tendsto (fun x : ℝ => (1 : ℝ) / (1 + Real.log (1 + c) / Real.log x)) atTop (𝓝 1) := by
    have h : Tendsto (fun x : ℝ => (1 : ℝ) / (1 + Real.log (1 + c) / Real.log x)) atTop
        (𝓝 (1 / 1)) := tendsto_const_nhds.div hadd_one one_ne_zero
    simp only [div_one] at h; exact h
  rw [Filter.tendsto_congr' hsimp]
  exact hdiv_one

-- ============================================================
-- PART 2: PNT at a Scaled Point with the Original Logarithm
-- ============================================================

/-- **PNT rescaling lemma**: π((1+c)x)·log(x)/((1+c)x) → 1 as x → ∞.

    The PNT states π(x)·log(x)/x → 1. Applied to (1+c)x:
    π((1+c)x)·log((1+c)x)/((1+c)x) → 1.

    Since log(x)/log((1+c)x) → 1, multiplying gives:
    π((1+c)x)·log(x)/((1+c)x) → 1.

    This is the "change of evaluation point" step — expressing PNT at (1+c)x
    but using log(x) rather than log((1+c)x). The two logarithms differ by o(log x),
    so their ratio → 1 and the overall limit is unchanged. -/
theorem pnt_at_scaled_point (c : ℝ) (hc : c > 0) :
    Tendsto (fun x : ℝ =>
      (primePi ((1 + c) * x) : ℝ) * Real.log x / ((1 + c) * x)) atTop (𝓝 1) := by
  have h1c_pos : (0 : ℝ) < 1 + c := by linarith
  -- PNT applied at (1+c)x via composition with the scaling map x ↦ (1+c)·x
  have pnt_1c : Tendsto (fun x : ℝ =>
      (primePi ((1 + c) * x) : ℝ) * Real.log ((1 + c) * x) / ((1 + c) * x)) atTop (𝓝 1) :=
    primeNumberTheorem.comp (Filter.Tendsto.const_mul_atTop h1c_pos tendsto_id)
  -- log(x)/log((1+c)x) → 1
  have hlog_ratio := log_ratio_tendsto_one c hc
  -- Multiply: [π·log((1+c)x)/((1+c)x)] × [log(x)/log((1+c)x)] → 1×1 = 1
  have hmul := pnt_1c.mul hlog_ratio
  rw [mul_one] at hmul
  -- Show these functions are eventually equal (log((1+c)x) cancels)
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx_pos : (0 : ℝ) < x := by linarith
  have h1cx_pos : (0 : ℝ) < (1 + c) * x := mul_pos h1c_pos hx_pos
  have hlog1cx_ne : Real.log ((1 + c) * x) ≠ 0 :=
    ne_of_gt (Real.log_pos (by nlinarith))
  -- Algebraic identity: [π·log(y)/y] × [log(x)/log(y)] = π·log(x)/y
  -- holds when log(y) ≠ 0 and y ≠ 0
  field_simp
  ring

-- ============================================================
-- PART 3: PNT Density for Long Intervals
-- ============================================================

/-- **PNT density for long intervals**: (π((1+c)x) - π(x))·log(x)/(cx) → 1.

    For any fixed c > 0, the interval (x, (1+c)x] contains approximately cx/log(x)
    primes as x → ∞, matching the PNT prediction that primes near x have local
    density 1/log(x).

    **Algebraic decomposition**:

      (π((1+c)x) - π(x))·log(x)/(cx)
        = (1+c)/c · [π((1+c)x)·log(x)/((1+c)x)]   [→ (1+c)/c by pnt_at_scaled_point]
        - 1/c   · [π(x)·log(x)/x]                  [→ 1/c by PNT]
        = (1+c)/c - 1/c = 1.

    This is the filter-algebraic identity: interval density = difference of two
    PNT estimates at the endpoints, with coefficients summing to 1. -/
theorem pnt_density_long_interval (c : ℝ) (hc : c > 0) :
    Tendsto (fun x : ℝ =>
      ((primePi ((1 + c) * x) : ℝ) - (primePi x : ℝ)) * Real.log x / (c * x))
      atTop (𝓝 1) := by
  have h1c_pos : (0 : ℝ) < 1 + c := by linarith
  have hc_ne : c ≠ 0 := ne_of_gt hc
  -- Step 1: π((1+c)x)·log(x)/((1+c)x) → 1
  have pnt_1c_logx := pnt_at_scaled_point c hc
  -- Step 2: π(x)·log(x)/x → 1 (Prime Number Theorem)
  have pnt_x := primeNumberTheorem
  -- Scale step 1 by (1+c)/c
  have h1 : Tendsto (fun x : ℝ =>
      (1 + c) / c * ((primePi ((1 + c) * x) : ℝ) * Real.log x / ((1 + c) * x)))
      atTop (𝓝 ((1 + c) / c * 1)) :=
    pnt_1c_logx.const_mul ((1 + c) / c)
  -- Scale step 2 by 1/c
  have h2 : Tendsto (fun x : ℝ =>
      1 / c * ((primePi x : ℝ) * Real.log x / x))
      atTop (𝓝 (1 / c * 1)) :=
    pnt_x.const_mul (1 / c)
  -- Subtract: (1+c)/c × 1 - 1/c × 1 = 1
  have h3 := h1.sub h2
  rw [show (1 + c) / c * 1 - 1 / c * 1 = (1 : ℝ) by field_simp; ring] at h3
  -- Match function to goal statement via algebraic identity
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hcx_ne : c * x ≠ 0 := mul_ne_zero hc_ne hx_ne
  have h1cx_ne : (1 + c) * x ≠ 0 := mul_ne_zero (ne_of_gt h1c_pos) hx_ne
  -- Algebraic identity: (1+c)/c·[A·B/((1+c)·x)] - 1/c·[C·B/x] = (A-C)·B/(c·x)
  field_simp
  ring

-- ============================================================
-- PART 4: Connection to Open Problem and Summary
-- ============================================================

/-- **The density gap**: long intervals vs short intervals.

    Part (1): For h = cx (proportional to x), density follows from PNT via filter algebra.
    Part (2): For h = x^θ with θ < 1, density requires `ShortIntervalPNT θ`, which is
              an open conjecture for θ < 1/2 (and conditional on RH for 1/2 < θ < 1).
    Part (3): Density (count asymptotic) implies existence (at least one prime) in all cases.

    This theorem summarizes the structural gap between the proved long-interval case
    and the open short-interval case. -/
theorem pnt_density_gap_summary :
    -- (1) Density for proportional intervals: proved unconditionally from PNT
    (∀ c : ℝ, c > 0 →
      Tendsto (fun x : ℝ =>
        ((primePi ((1 + c) * x) : ℝ) - (primePi x : ℝ)) * Real.log x / (c * x))
        atTop (𝓝 1)) ∧
    -- (2) Density for short intervals is the open conjecture (only stated, not proved here)
    (∀ θ : ℝ, 0 < θ →
      BertrandsPostulateOQ03OQ04.ShortIntervalPNT θ →
        ∀ᶠ x in atTop, ∃ p : ℕ, Nat.Prime p ∧ (x : ℝ) < p ∧ (p : ℝ) ≤ x + x ^ θ) :=
  ⟨fun c hc => pnt_density_long_interval c hc,
   fun θ hθ h =>
     BertrandsPostulateOQ03OQ04.shortIntervalPNT_implies_primeGapConjecture_eventually hθ h⟩

end BertrandsPostulateOQ03OQ04OQ03

end -- noncomputable section
