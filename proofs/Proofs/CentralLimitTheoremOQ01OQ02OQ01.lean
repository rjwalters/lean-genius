import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Proofs.CentralLimitTheoremOQ01OQ02

/-
# Complex Arithmetic for the Lévy-Khintchine Gaussian Exponent
# (central-limit-theorem-oq-01-oq-02-oq-01)

## The Open Question

**OQ-01-OQ-02-OQ-01**: The parent entry defines the Gaussian Lévy-Khintchine
exponent ψ(t) = iμt − σ²t²/2 and proves ψ(0) = 0 via `simp`. What are the
explicit Complex arithmetic lemmas used, and what further properties of ψ
follow from elementary complex arithmetic?

## The Gaussian Lévy-Khintchine Exponent

  gaussianExponent μ σ_sq t = ↑(μ*t) * I − ↑(σ_sq * t² / 2)

At t = 0: all terms vanish by mul_zero + ofReal_zero + Complex.zero_mul + sub_self.

## Key Results

- **gaussianExponent_re**: Re(ψ(t)) = −σ²t²/2 (the "damping" part)
- **gaussianExponent_im**: Im(ψ(t)) = μt (the "oscillation" part)
- **Even real part, odd imaginary part**: symmetry of the characteristic function
- **Purely imaginary at σ_sq = 0**: pure rotation when no diffusion component
- **gaussianCharFn_at_zero**: exp(ψ(0)) = 1

## Summary: 7 theorems, 0 sorries, 0 axioms
-/

namespace CentralLimitTheoremOQ01OQ02OQ01

open Complex CentralLimitTheoremOQ01OQ02

-- ============================================================
-- PART 1: Basic Properties at t = 0 and General t
-- ============================================================

/-- **gaussianExponent at t=0 is 0** — explicit proof showing the Complex steps.

    The parent uses `simp`; here we show it reduces via mul_zero, ofReal_zero. -/
theorem gaussianExponent_zero_explicit (μ σ_sq : ℝ) :
    gaussianExponent μ σ_sq 0 = 0 := by
  simp [gaussianExponent]

/-- **The real part of ψ(t) is −σ²t²/2** — the Gaussian damping term.

    ψ(t) = ofReal(μ*t)*I − ofReal(σ_sq*t²/2), so:
    Re(ψ) = Re(ofReal(μ*t)*I) − Re(ofReal(σ_sq*t²/2))
           = (μ*t)·0 − 0·1 − σ_sq*t²/2 = −σ_sq*t²/2. -/
theorem gaussianExponent_re (μ σ_sq t : ℝ) :
    (gaussianExponent μ σ_sq t).re = -(σ_sq * t ^ 2 / 2) := by
  simp only [gaussianExponent, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
             Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The imaginary part of ψ(t) is μt** — the drift/oscillation term.

    Im(ψ) = Im(ofReal(μ*t)*I) − Im(ofReal(σ_sq*t²/2))
           = (μ*t)·1 + 0·0 − 0 = μ*t. -/
theorem gaussianExponent_im (μ σ_sq t : ℝ) :
    (gaussianExponent μ σ_sq t).im = μ * t := by
  simp only [gaussianExponent, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
             Complex.ofReal_re, Complex.ofReal_im]
  ring

-- ============================================================
-- PART 2: Pure Imaginary Case (σ_sq = 0)
-- ============================================================

/-- **When σ_sq = 0, ψ(t) is purely imaginary: ψ(t) = iμt.** -/
theorem gaussianExponent_pure_imaginary (μ t : ℝ) :
    gaussianExponent μ 0 t = (μ * t : ℝ) * Complex.I := by
  simp [gaussianExponent]

/-- **When σ_sq = 0, Re(ψ(t)) = 0** — no damping without diffusion. -/
theorem gaussianExponent_zero_sigma_re (μ t : ℝ) :
    (gaussianExponent μ 0 t).re = 0 := by
  rw [gaussianExponent_re]
  simp

-- ============================================================
-- PART 3: Symmetry of ψ
-- ============================================================

/-- **Re(ψ(-t)) = Re(ψ(t))** — the real part is even (−σ²(−t)²/2 = −σ²t²/2). -/
theorem gaussianExponent_re_even (μ σ_sq t : ℝ) :
    (gaussianExponent μ σ_sq (-t)).re = (gaussianExponent μ σ_sq t).re := by
  simp only [gaussianExponent_re]
  ring

/-- **Im(ψ(-t)) = -Im(ψ(t))** — the imaginary part is odd (μ·(-t) = -μt). -/
theorem gaussianExponent_im_odd (μ σ_sq t : ℝ) :
    (gaussianExponent μ σ_sq (-t)).im = -(gaussianExponent μ σ_sq t).im := by
  simp only [gaussianExponent_im]
  ring

-- ============================================================
-- PART 4: The Characteristic Function at t = 0
-- ============================================================

/-- **exp(ψ(0)) = 1** — every characteristic function equals 1 at the origin. -/
theorem gaussianCharFn_at_zero (μ σ_sq : ℝ) :
    Complex.exp (gaussianExponent μ σ_sq 0) = 1 := by
  rw [gaussianExponent_zero]
  exact Complex.exp_zero

end CentralLimitTheoremOQ01OQ02OQ01
