/-
  Aristotle targets for AreaOfCircleOQ05OQ01 (Polar-Coordinate Proof of Gaussian Integral)
  These are the 2 remaining proof obligations — both product-measure integrability conditions.

  Proved so far (no longer sorried in main file):
    - angular_integral (∫_{-π}^π 1 = 2π): proved via set_integral_const + volume_Ioo
    - double_integral_eq_polar: proved via integral_comp_polarCoord_symm + set_integral_congr
    - gaussian_sq_eq_double_integral: proved structurally via integral_prod + ring
    - polar_integral_factorization: proved structurally via restrict_prod + integral_prod + ring

  Remaining sorries (both are product integrability conditions):
    TARGET 1: gaussian_product_integrable — exp(-x²)·exp(-y²) integrable on ℝ² product measure
    TARGET 2: radial_product_integrable  — r·exp(-r²) integrable on Ioi(0) × Ioo(-π,π)
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic
import Proofs.AreaOfCircleOQ05

open MeasureTheory Real Set Filter Prod
open scoped NNReal ENNReal

noncomputable section

namespace AreaOfCircleOQ05OQ01Aristotle

/-
TARGET 1
exp(-x²)·exp(-y²) is integrable on ℝ² with the product Lebesgue measure.

This is needed for the Fubini step:
  ∫∫ exp(-x²-y²) dxdy = (∫ exp(-x²) dx)²

Strategy: Use Integrable.prod_mul or Integrable.comp_fst/comp_snd:
  - hf : Integrable (fun x => rexp (-(x^2)))
  - Then (fun p => rexp(-p.1^2) * rexp(-p.2^2)) is integrable on volume.prod volume
    via Integrable.prod_mul (or Measurable.integrable on product, or norm-based bound).
Context: integrable_exp_neg_mul_sq gives integrability of each factor separately.
-/
theorem gaussian_product_integrable :
    Integrable (fun p : ℝ × ℝ => rexp (-(p.1 ^ 2)) * rexp (-(p.2 ^ 2)))
      (volume.prod volume) := by
  have hf : Integrable (fun x : ℝ => rexp (-(x ^ 2))) := by
    have h := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    simp_rw [one_mul] at h; exact h
  sorry

/-
TARGET 2
r·exp(-r²) is integrable on Ioi(0) × Ioo(-π,π) with the product of restricted measures.

This is needed for the Fubini step in polar_integral_factorization:
  ∫_{Ioi(0) × Ioo(-π,π)} r·exp(-r²) d(r,θ) = (∫_{Ioi 0} r·exp(-r²) dr) · (∫_{Ioo(-π,π)} 1 dθ)

Strategy:
  - hrad : Integrable (fun r => r * rexp (-(r^2))) (volume.restrict (Ioi 0))
    (proved by contradiction: integral_undef h ▸ radial_integral_eq ▸ norm_num)
  - volume (Ioo (-π) π) < ∞ (it equals ENNReal.ofReal (2π))
  - So the product is integrable via Integrable.prod_mul or Integrable.of_finite_measure
    combined with hrad
-/
theorem radial_product_integrable :
    Integrable (fun p : ℝ × ℝ => p.1 * rexp (-(p.1 ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  have hrad : Integrable (fun r : ℝ => r * rexp (-(r ^ 2))) (volume.restrict (Ioi 0)) := by
    by_contra h
    have := GaussianIntegralCircle.radial_integral
    simp only [integral_undef h] at this
    norm_num at this
  have h_fin : (volume (Ioo (-Real.pi) Real.pi)) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  sorry

end AreaOfCircleOQ05OQ01Aristotle

end
