/-
  Isoperimetric Inequality: the Hurwitz area bound from Wirtinger
  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-02-oq-02

  The sibling file `AreaOfCircleOQ01OQ02OQ02OQ02` proves the analytic
  Wirtinger inequality for a `C¹` periodic mean-zero function `f`,

      ∫₀^{2π} f²  ≤  ∫₀^{2π} (f')².

  This file assembles it into the analytic heart of Hurwitz's Fourier proof of
  the isoperimetric inequality.  Parametrise a closed curve `γ(t) = (x(t), y(t))`
  by (constant-speed / arc-length) with period `2π`, so that its length is
  `L = ∫₀^{2π} √(x'² + y'²) = 2π`, equivalently — in the arc-length
  normalisation — `∫₀^{2π} (x'² + y'²) = 2π`.  Center the curve so that the
  first coordinate has zero mean, `∫₀^{2π} x = 0`.  By Green's theorem the
  enclosed (signed) area is

      A = ∮ x dy = ∫₀^{2π} x · y'.

  The theorem below shows `A ≤ π`, i.e. `A ≤ L² / (4π)` in this normalisation —
  the isoperimetric inequality, with the circle the unique extremiser.

  Hurwitz's one-line computation: expanding the nonnegative integral of the
  square `(y' − x)² ≥ 0` gives

      0 ≤ ∫ (y' − x)²  =  ∫ y'²  − 2 ∫ x y'  + ∫ x²,

  hence `2A = 2∫ x y' ≤ ∫ y'² + ∫ x²`.  Wirtinger replaces `∫ x²` by the larger
  `∫ x'²`, and the arc-length normalisation collapses `∫ x'² + ∫ y'² = 2π`, so
  `2A ≤ 2π`.  Equality forces `y' = x` and (Wirtinger's equality case) only the
  first harmonic to survive — the circle.

  References:
  - Hurwitz (1901): Fourier proof of the isoperimetric inequality
  - AreaOfCircleOQ01OQ02OQ02OQ02.lean (the Wirtinger inequality, reused here)
-/

import Mathlib
import Proofs.AreaOfCircleOQ01OQ02OQ02OQ02

open Real Filter Topology Complex MeasureTheory IsoperimetricFourier

noncomputable section

namespace IsoperimetricFourier

-- ============================================================
-- SECTION IV: Hurwitz's isoperimetric area bound
-- ============================================================

/-- **Hurwitz's isoperimetric bound** (arc-length normalised form).  Let a closed
    curve `γ(t) = (x(t), y(t))` be `C¹` and `2π`-periodic in its first coordinate,
    centered so that `∫₀^{2π} x = 0`, and normalised to length `2π` in the sense
    that `∫₀^{2π} (x'² + y'²) = 2π` (which holds for any arc-length / constant-speed
    parametrisation of a curve of length `2π`).  Then the enclosed signed area
    `A = ∫₀^{2π} x · y'` satisfies

        A ≤ π   ( = L² / (4π) with L = 2π).

    This is the isoperimetric inequality in normalised coordinates; the general
    scale-invariant form `L² ≥ 4πA` follows by rescaling.  The proof is Hurwitz's:
    `∫ (y' − x)² ≥ 0` bounds `2A` by `∫ y'² + ∫ x²`, Wirtinger
    (`wirtinger_inequality`) upgrades `∫ x²` to `∫ x'²`, and the length
    normalisation turns `∫ x'² + ∫ y'²` into `2π`. -/
theorem hurwitz_area_bound (x y : ℝ → ℝ)
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hxper : ∀ t, x (t + 2 * π) = x t)
    (hmean : ∫ t in (0 : ℝ)..(2 * π), x t = 0)
    (harc : ∫ t in (0 : ℝ)..(2 * π), ((deriv x t) ^ 2 + (deriv y t) ^ 2) = 2 * π) :
    ∫ t in (0 : ℝ)..(2 * π), x t * deriv y t ≤ π := by
  -- Continuity of the three building blocks.
  have hxc : Continuous x := hx.continuous
  have hdxc : Continuous (deriv x) := hx.continuous_deriv le_rfl
  have hdyc : Continuous (deriv y) := hy.continuous_deriv le_rfl
  -- Interval-integrability of every integrand that appears.
  have iX2 : IntervalIntegrable (fun t => (x t) ^ 2) volume 0 (2 * π) :=
    (hxc.pow 2).intervalIntegrable 0 (2 * π)
  have iDX2 : IntervalIntegrable (fun t => (deriv x t) ^ 2) volume 0 (2 * π) :=
    (hdxc.pow 2).intervalIntegrable 0 (2 * π)
  have iDY2 : IntervalIntegrable (fun t => (deriv y t) ^ 2) volume 0 (2 * π) :=
    (hdyc.pow 2).intervalIntegrable 0 (2 * π)
  have iXY2 : IntervalIntegrable (fun t => 2 * (x t * deriv y t)) volume 0 (2 * π) :=
    ((continuous_const.mul (hxc.mul hdyc))).intervalIntegrable 0 (2 * π)
  -- Split the length normalisation into the two squared-derivative integrals.
  have harc' : (∫ t in (0 : ℝ)..(2 * π), (deriv x t) ^ 2)
      + (∫ t in (0 : ℝ)..(2 * π), (deriv y t) ^ 2) = 2 * π := by
    rw [← intervalIntegral.integral_add iDX2 iDY2]; exact harc
  -- The nonnegative square `(y' − x)²` expands by linearity of the integral.
  have hexp : (fun t => (deriv y t - x t) ^ 2)
      = (fun t => (deriv y t) ^ 2 - 2 * (x t * deriv y t) + (x t) ^ 2) := by
    funext t; ring
  have hval : (∫ t in (0 : ℝ)..(2 * π), (deriv y t - x t) ^ 2)
      = (∫ t in (0 : ℝ)..(2 * π), (deriv y t) ^ 2)
        - 2 * (∫ t in (0 : ℝ)..(2 * π), x t * deriv y t)
        + (∫ t in (0 : ℝ)..(2 * π), (x t) ^ 2) := by
    rw [hexp,
        intervalIntegral.integral_add (iDY2.sub iXY2) iX2,
        intervalIntegral.integral_sub iDY2 iXY2,
        intervalIntegral.integral_const_mul]
  -- The integral of a square is nonnegative.
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..(2 * π), (deriv y t - x t) ^ 2 := by
    apply intervalIntegral.integral_nonneg (by positivity)
    intro t _; positivity
  rw [hval] at hnn
  -- Wirtinger: `∫ x² ≤ ∫ x'²`.
  have hw := wirtinger_inequality x hx hxper hmean
  -- Assemble: `2A ≤ ∫ y'² + ∫ x² ≤ ∫ y'² + ∫ x'² = 2π`, so `A ≤ π`.
  linarith [hnn, hw, harc']

end IsoperimetricFourier
