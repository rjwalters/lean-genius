/-
  Isoperimetric Inequality: Fourier Analysis Infrastructure
  Open Question: area-of-circle-oq-01-oq-02-oq-02

  This file proves the IBP lemma for Fourier coefficients of periodic functions:

    ĉₙ(f') = in · ĉₙ(f)

  References:
  - Hurwitz (1901): Fourier proof of the isoperimetric inequality
  - Mathlib: Analysis.Fourier.AddCircle (fourierCoeffOn_of_hasDerivAt)
  - AreaOfCircleOQ01OQ03.lean (uses this lemma in the isoperimetric proof)
-/

import Mathlib

open Real Filter Topology Complex MeasureTheory

noncomputable section

namespace IsoperimetricFourier

-- ============================================================
-- SECTION I: IBP for Fourier Coefficients of Periodic Functions
-- ============================================================

/-- The derivative of (ofReal ∘ f) is (ofReal ∘ deriv f) for C¹ real functions.
    Chain rule: ofReal has HasDerivAt with derivative 1, composed with f gives
    HasDerivAt (ofReal ∘ f) (1 • deriv f x) x = HasDerivAt (ofReal ∘ f) (ofReal(deriv f x)) x. -/
theorem hasDerivAt_ofReal_comp_real (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x : ℝ) :
    HasDerivAt (ofReal ∘ f) ((ofReal ∘ deriv f) x) x := by
  have hd : HasDerivAt f (deriv f x) x := (hf.differentiable le_rfl x).hasDerivAt
  -- ofRealCLM : ℝ →L[ℝ] ℂ has HasDerivAt ofReal (ofRealCLM 1) at any point
  -- ofRealCLM 1 = ofReal 1 = 1
  have hg : HasDerivAt (⇑ofRealCLM) (ofRealCLM 1) (f x) :=
    ContinuousLinearMap.hasDerivAt ofRealCLM
  -- Chain rule (scomp): HasDerivAt (g ∘ f) (f' • g') x
  -- f' = deriv f x : ℝ, g' = ofRealCLM 1 = 1 : ℂ
  -- f' • g' = (deriv f x) • (1 : ℂ) = ofReal(deriv f x)
  have h := hg.scomp x hd
  -- h : HasDerivAt (ofReal ∘ f) ((deriv f x) • ofRealCLM 1) x
  -- Convert to the desired form
  convert h using 1
  -- Goal: (ofReal ∘ deriv f) x = (deriv f x) • ofRealCLM 1
  simp [Function.comp, ofReal_one, mul_one]

/-- IBP for Fourier coefficients: ĉₙ(f') = in · ĉₙ(f) for periodic C¹ functions.

    For a C¹ function f with period 2π and n ≠ 0, the Fourier coefficient of
    the derivative equals i·n times the Fourier coefficient of f.

    Proof: Apply Mathlib's fourierCoeffOn_of_hasDerivAt. The boundary term
    f(2π) - f(0) vanishes by periodicity, leaving a clean algebraic identity. -/
theorem fourierCoeffOn_deriv_periodic (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv f) n =
    I * ↑n * fourierCoeffOn hab (ofReal ∘ f) n := by
  -- Step 1: Establish derivative hypothesis
  have hderiv : ∀ x ∈ Set.uIcc 0 (2 * π),
      HasDerivAt (ofReal ∘ f) ((ofReal ∘ deriv f) x) x :=
    fun x _ => hasDerivAt_ofReal_comp_real f hf x
  -- Step 2: Integrability
  have hint : IntervalIntegrable (ofReal ∘ deriv f) MeasureTheory.volume 0 (2 * π) :=
    (continuous_ofReal.comp (hf.continuous_deriv le_rfl)).intervalIntegrable 0 (2 * π)
  -- Step 3: Apply Mathlib's IBP formula
  have hibp := fourierCoeffOn_of_hasDerivAt hab hn hderiv hint
  -- Step 4: Periodicity kills the boundary term
  have hfp : f (2 * π) = f 0 := by have h := hperiod 0; rwa [zero_add] at h
  -- Step 5: Rewrite and simplify
  rw [hibp]
  simp only [Function.comp_apply, hfp, sub_self, mul_zero, zero_sub,
             ofReal_zero, sub_zero]
  -- Goal: D = I * ↑n * (1/c * (-T * D)) where c, T involve π, I, n
  have h1 : (↑π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt pi_pos)
  have h2 : (I : ℂ) ≠ 0 := I_ne_zero
  have h3 : (↑n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  field_simp
  push_cast
  ring

end IsoperimetricFourier
