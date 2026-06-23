import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic

/-
# The Second Moment of the Gaussian  (area-of-circle-oq-07-oq-05)

## Open Question (area-of-circle-oq-07-oq-05)
"What is the value of the *second moment* of the Gaussian weight, i.e. the
integral of `x²` against `e^{-x²}` over the whole real line?"

$$ \int_{-\infty}^{\infty} x^2\, e^{-x^2}\, dx = \tfrac{\sqrt{\pi}}{2}. $$

## Answer: it is exactly half of the zeroth moment `√π`.

The parent entry `area-of-circle-oq-07` evaluates the **zeroth moment**
`∫_{-∞}^{∞} e^{-x²} dx = √π` (Mathlib's `integral_gaussian`).  The siblings
oq-01 … oq-04 study the complex parameter, the half-line, and the squared
value.  This entry adds the **first nontrivial moment**: weighting the Gaussian
by `x²`.

The value `√π/2` is obtained by **integration by parts on the whole line**
(`MeasureTheory.integral_mul_deriv_eq_deriv_mul`).  Writing the integrand as
`x · (x e^{-x²})` and noting that `x e^{-x²}` is the derivative of
`-½ e^{-x²}`, the boundary term `x · (-½ e^{-x²})` vanishes at `±∞` (Gaussian
decay beats the linear factor, `tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact`),
leaving

  `∫ x² e^{-x²} = -∫ 1 · (-½ e^{-x²}) = ½ ∫ e^{-x²} = ½ · √π = √π/2`.

Equivalently this is `½·Γ(3/2)·2 = √π/2`, the Gamma-function shadow of the
second moment.  No new axioms: every step is a routine consequence of existing
Mathlib results (the parent value `integral_gaussian`, the IBP lemma, and the
Gaussian-decay tendsto).
-/

open Real MeasureTheory Filter Topology Set

namespace AreaOfCircleOQ07OQ05

/-- **Gaussian decay of the boundary factor.** The function `x ↦ x e^{-x²}`
tends to `0` at both ends of the real line, because the Gaussian factor decays
faster than any power. This is the boundary term that vanishes in the
integration-by-parts computation of the second moment. -/
theorem tendsto_mul_gaussian_cocompact :
    Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1) one_pos 1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h.congr (fun x => ?_)
  rw [Real.rpow_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), neg_one_mul]

/-- **The second moment of the standard Gaussian.**
`∫_{-∞}^{∞} x² e^{-x²} dx = √π / 2`, obtained by integration by parts on the
whole real line. -/
theorem gaussian_second_moment :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
  -- Integration by parts with `u = x`, `v = -½ e^{-x²}`.
  -- `u' = 1`, `v' = x e^{-x²}`, so `u · v' = x²e^{-x²}` and `u' · v = -½ e^{-x²}`.
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := fun x => by
    simpa using hasDerivAt_id x
  have hv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => -(2 : ℝ)⁻¹ * Real.exp (-y ^ 2))
        (x * Real.exp (-x ^ 2)) x := by
    intro x
    have hsq : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).neg
    have hexp := hsq.exp
    have hfin := hexp.const_mul (-(2 : ℝ)⁻¹)
    convert hfin using 1
    ring
  -- Integrability of the two integrands.
  have huv' : Integrable (fun x : ℝ => x * (x * Real.exp (-x ^ 2))) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (2 : ℝ))
      (by norm_num)
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [neg_one_mul]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hu'v : Integrable (fun x : ℝ => (1 : ℝ) * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2))) := by
    have h := (integrable_exp_neg_mul_sq (b := 1) one_pos).const_mul (-(2 : ℝ)⁻¹)
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [neg_one_mul, one_mul]
  -- Boundary terms vanish at ±∞.
  have hbot : Tendsto (fun x : ℝ => x * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2)))
      atBot (𝓝 0) := by
    have hb : atBot ≤ cocompact ℝ := by rw [cocompact_eq_atBot_atTop]; exact le_sup_left
    have h := (tendsto_mul_gaussian_cocompact.mono_left hb).const_mul (-(2 : ℝ)⁻¹)
    rw [mul_zero] at h
    refine Filter.Tendsto.congr (fun x => ?_) h
    ring
  have htop : Tendsto (fun x : ℝ => x * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2)))
      atTop (𝓝 0) := by
    have ht : atTop ≤ cocompact ℝ := by rw [cocompact_eq_atBot_atTop]; exact le_sup_right
    have h := (tendsto_mul_gaussian_cocompact.mono_left ht).const_mul (-(2 : ℝ)⁻¹)
    rw [mul_zero] at h
    refine Filter.Tendsto.congr (fun x => ?_) h
    ring
  -- Apply integration by parts on (-∞, ∞).
  have key := integral_mul_deriv_eq_deriv_mul (a' := (0 : ℝ)) (b' := (0 : ℝ))
    hu hv huv' hu'v hbot htop
  -- Evaluate the remaining integral `∫ 1 · (-½ e^{-x²}) = -½ √π`.
  have hint : ∫ x : ℝ, (1 : ℝ) * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2))
      = -(2 : ℝ)⁻¹ * Real.sqrt Real.pi := by
    simp only [one_mul]
    rw [integral_const_mul]
    have hg : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
      have := integral_gaussian 1
      simpa [neg_one_mul, div_one] using this
    rw [hg]
  -- Assemble via integration by parts.
  calc ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2)
      = ∫ x : ℝ, x * (x * Real.exp (-x ^ 2)) := by
        apply integral_congr_ae; filter_upwards with x; ring
    _ = (0 : ℝ) - 0 - ∫ x : ℝ, (1 : ℝ) * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2)) := key
    _ = Real.sqrt Real.pi / 2 := by rw [hint]; ring

end AreaOfCircleOQ07OQ05
