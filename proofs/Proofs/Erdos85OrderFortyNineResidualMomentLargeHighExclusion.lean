import Proofs.Erdos85OrderFortyNineResidualRootMoments

/-!
# Large-high-count residual moment exclusions

For `h = 19` or `h = 21`, the exact residual moments are incompatible
with the squared Perron lower bound and Cauchy--Schwarz on the remaining
residual roots.  These denominator-free arithmetic terminals isolate the
last two analytic inputs needed by the graph-level consumer.
-/

namespace Erdos85

/-- The `h = 19` residual profile is impossible once `x = ρ²` satisfies
the degree-square Rayleigh lower bound and the remaining-root Cauchy bound. -/
theorem false_of_orderFortyNine_h19_residualMoment_bounds
    (x : ℝ)
    (hrayleigh : (2686 : ℝ) / 49 ≤ x)
    (hcauchy : (110 - x) ^ 2 ≤ 12 * (3246 - x ^ 2)) : False := by
  nlinarith [sq_nonneg (x - (2686 : ℝ) / 49)]

/-- The analogous arithmetic terminal for `h = 21`. -/
theorem false_of_orderFortyNine_h21_residualMoment_bounds
    (x : ℝ)
    (hrayleigh : (2716 : ℝ) / 49 ≤ x)
    (hcauchy : (84 - x) ^ 2 ≤ 8 * (3108 - x ^ 2)) : False := by
  nlinarith [sq_nonneg (x - (2716 : ℝ) / 49)]

/-- Uniform wrapper for the two high-count cases eliminated by the fourth
residual moment. -/
theorem false_of_orderFortyNine_h19_or_h21_residualMoment_bounds
    (h : ℕ) (hh : h = 19 ∨ h = 21) (x : ℝ)
    (hrayleigh :
      (if h = 19 then (2686 : ℝ) / 49 else (2716 : ℝ) / 49) ≤ x)
    (hcauchy :
      if h = 19 then
        (110 - x) ^ 2 ≤ 12 * (3246 - x ^ 2)
      else
        (84 - x) ^ 2 ≤ 8 * (3108 - x ^ 2)) : False := by
  rcases hh with rfl | rfl
  · exact false_of_orderFortyNine_h19_residualMoment_bounds x
      (by simpa using hrayleigh) (by simpa using hcauchy)
  · exact false_of_orderFortyNine_h21_residualMoment_bounds x
      (by simpa using hrayleigh) (by simpa using hcauchy)

end Erdos85
