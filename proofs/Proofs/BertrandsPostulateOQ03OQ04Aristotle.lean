/-
  Aristotle targets for Bertrand's Postulate OQ-03 OQ-04 (Prime Density in Short Intervals)
  Routine filter/limit algebra lemmas for automated proof search.
  See BertrandsPostulateOQ03OQ04.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (ShortIntervalPNT for θ < 1 unconditionally)
  - Routine limit algebra from Mathlib Filter API
  - Clean theorem statements with no definition sorries
  - No axiom declarations

  Status: 0 sorries — all proofs complete.
  Proofs mirror BertrandsPostulateOQ03OQ04OQ03.lean (pnt_at_scaled_point, pnt_density_long_interval).
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Proofs.PrimeNumberTheorem
import Proofs.BertrandsPostulateOQ03

open Filter Topology Real
open PrimeNumberTheorem (primePi primeApprox primeNumberTheorem)

namespace BertrandsPostulateOQ03OQ04Aristotle

noncomputable section

/-- Helper (proved): log(x) / log((1+c)*x) → 1 as x → ∞ for any fixed c > 0.

    Proof: log((1+c)*x) = log(1+c) + log(x), so
    log(x)/log((1+c)*x) = 1/(1 + log(1+c)/log(x)) → 1/(1+0) = 1 -/
lemma log_ratio_tendsto_one (c : ℝ) (hc : c > 0) :
    Tendsto (fun x : ℝ => Real.log x / Real.log ((1 + c) * x)) atTop (𝓝 1) := by
  have h1c_pos : (1 + c) > 0 := by linarith
  have hsimp : ∀ᶠ x in atTop, Real.log x / Real.log ((1 + c) * x) =
      1 / (1 + Real.log (1 + c) / Real.log x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx_pos : (0 : ℝ) < x := by linarith
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    rw [Real.log_mul (ne_of_gt h1c_pos) (ne_of_gt hx_pos)]
    field_simp; ring
  have hdiv_zero : Tendsto (fun x : ℝ => Real.log (1 + c) / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hadd_one : Tendsto (fun x : ℝ => 1 + Real.log (1 + c) / Real.log x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hdiv_zero
  have hdiv_one : Tendsto (fun x : ℝ => (1:ℝ) / (1 + Real.log (1 + c) / Real.log x)) atTop (𝓝 1) := by
    have h : Tendsto (fun x : ℝ => (1:ℝ) / (1 + Real.log (1 + c) / Real.log x)) atTop
        (𝓝 (1 / 1)) := tendsto_const_nhds.div hadd_one one_ne_zero
    simp only [div_one] at h; exact h
  rw [Filter.tendsto_congr' hsimp]
  exact hdiv_one

/-- Aristotle target: Combining PNT for (1+c)x with log ratio gives π((1+c)x)*log(x)/((1+c)x) → 1.

    Key steps:
    - pnt_1c: Tendsto (π((1+c)x) * log((1+c)x) / ((1+c)x)) → 1 (PNT composed with scaling)
    - log_ratio_tendsto_one: Tendsto (log x / log((1+c)x)) → 1
    - Multiply: product → 1*1 = 1, and log((1+c)x) cancels algebraically
    - Use filter_upwards to handle log((1+c)x) ≠ 0 for large x -/
lemma pnt_1c_logx_tendsto (c : ℝ) (hc : c > 0) :
    Tendsto (fun x : ℝ =>
      (primePi ((1 + c) * x) : ℝ) * Real.log x / ((1 + c) * x)) atTop (𝓝 1) := by
  have h1c_pos : (0 : ℝ) < 1 + c := by linarith
  -- PNT at (1+c)x via composition with scaling x ↦ (1+c)x
  have pnt_1c : Tendsto (fun x : ℝ =>
      (primePi ((1 + c) * x) : ℝ) * Real.log ((1 + c) * x) / ((1 + c) * x)) atTop (𝓝 1) :=
    primeNumberTheorem.comp (Filter.Tendsto.const_mul_atTop h1c_pos tendsto_id)
  -- log(x)/log((1+c)x) → 1
  have hlog_ratio := log_ratio_tendsto_one c hc
  -- Product: [π·log(y)/y] · [log(x)/log(y)] → 1·1 = 1, then log(y) cancels
  have hmul := pnt_1c.mul hlog_ratio
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx_pos : (0 : ℝ) < x := by linarith
  have h1cx_pos : (0 : ℝ) < (1 + c) * x := mul_pos h1c_pos hx_pos
  have hlog1cx_ne : Real.log ((1 + c) * x) ≠ 0 :=
    ne_of_gt (Real.log_pos (by nlinarith))
  field_simp
  ring

/-- Aristotle target: Density asymptotic for intervals of length cx from PNT.

    Key steps:
    - pnt_1c_logx: Tendsto (π((1+c)x) * logx / ((1+c)x)) → 1
    - pnt_x = primeNumberTheorem: Tendsto (π(x) * logx / x) → 1
    - Rewrite goal as: (1+c)/c * pnt_1c_logx_term - 1/c * pnt_x_term
    - Apply Tendsto.sub + Tendsto.const_mul: → (1+c)/c * 1 - 1/c * 1 = 1 -/
lemma long_interval_density_from_pnt' (c : ℝ) (hc : c > 0) :
    Tendsto (fun x : ℝ =>
      ((primePi ((1 + c) * x) : ℝ) - (primePi x : ℝ)) * Real.log x / (c * x))
      atTop (𝓝 1) := by
  have h1c_pos : (0 : ℝ) < 1 + c := by linarith
  have hc_ne : c ≠ 0 := ne_of_gt hc
  -- π((1+c)x)·log(x)/((1+c)x) → 1
  have pnt_1c_logx := pnt_1c_logx_tendsto c hc
  -- π(x)·log(x)/x → 1 (PNT)
  have pnt_x := primeNumberTheorem
  -- Scale pnt_1c_logx by (1+c)/c
  have h1 : Tendsto (fun x : ℝ =>
      (1 + c) / c * ((primePi ((1 + c) * x) : ℝ) * Real.log x / ((1 + c) * x)))
      atTop (𝓝 ((1 + c) / c * 1)) :=
    pnt_1c_logx.const_mul ((1 + c) / c)
  -- Scale pnt_x by 1/c
  have h2 : Tendsto (fun x : ℝ =>
      1 / c * ((primePi x : ℝ) * Real.log x / x))
      atTop (𝓝 (1 / c * 1)) :=
    pnt_x.const_mul (1 / c)
  -- Subtract: (1+c)/c·1 - 1/c·1 = 1
  have h3 := h1.sub h2
  rw [show (1 + c) / c * 1 - 1 / c * 1 = (1 : ℝ) by field_simp; ring] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hcx_ne : c * x ≠ 0 := mul_ne_zero hc_ne hx_ne
  have h1cx_ne : (1 + c) * x ≠ 0 := mul_ne_zero (ne_of_gt h1c_pos) hx_ne
  field_simp
  ring

end

end BertrandsPostulateOQ03OQ04Aristotle
