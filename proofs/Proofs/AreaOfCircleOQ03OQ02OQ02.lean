/-
Dalzell-Niven Integral: Alternative Proof that π < 22/7

Open Question (area-of-circle-oq-03-oq-02-oq-02):
"Can we formalize the Dalzell-Niven integral proof that π < 22/7?"

The integral ∫₀¹ x⁴(1-x)⁴/(1+x²) dx = 22/7 - π provides an elegant proof
that π < 22/7, since the integrand is strictly positive on (0,1).

Key identity: x⁴(1-x)⁴ = (1+x²)(x⁶ - 4x⁵ + 5x⁴ - 4x² + 4) - 4

So x⁴(1-x)⁴/(1+x²) = x⁶ - 4x⁵ + 5x⁴ - 4x² + 4 - 4/(1+x²)

Antiderivative: F(x) = x⁷/7 - 2x⁶/3 + x⁵ - 4x³/3 + 4x - 4·arctan(x)
  F(1) = 1/7 - 2/3 + 1 - 4/3 + 4 - π = 22/7 - π
  F(0) = 0

References:
- D.P. Dalzell, "On 22/7", J. London Math. Soc. 19 (1944), 133-134
- I. Niven, "A simple proof that π is irrational", Bull. AMS 53 (1947), 509
- Mathlib: integral_pow, integral_inv_one_add_sq, arctan_one
-/

import Mathlib

namespace AreaOfCircleOQ03OQ02OQ02

open Real MeasureTheory Set intervalIntegral

-- ============================================================
-- PART I: Polynomial Identity
-- ============================================================

/-- Key algebraic identity: x⁴(1-x)⁴ = (1+x²)(x⁶ - 4x⁵ + 5x⁴ - 4x² + 4) - 4 -/
theorem dalzell_polynomial_identity (x : ℝ) :
    x ^ 4 * (1 - x) ^ 4 =
    (1 + x ^ 2) * (x ^ 6 - 4 * x ^ 5 + 5 * x ^ 4 - 4 * x ^ 2 + 4) - 4 := by
  ring

/-- The Dalzell-Niven integrand decomposition:
    x⁴(1-x)⁴/(1+x²) = x⁶ - 4x⁵ + 5x⁴ - 4x² + 4 - 4/(1+x²) -/
theorem dalzell_integrand_decomposition (x : ℝ) :
    x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) =
    x ^ 6 - 4 * x ^ 5 + 5 * x ^ 4 - 4 * x ^ 2 + 4 - 4 / (1 + x ^ 2) := by
  have h : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

-- ============================================================
-- PART II: Integrand Positivity
-- ============================================================

/-- The Dalzell-Niven integrand is non-negative on [0,1] -/
theorem dalzell_integrand_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) := by
  apply div_nonneg
  · apply mul_nonneg
    · positivity
    · apply pow_nonneg; linarith
  · positivity

/-- The Dalzell-Niven integrand is strictly positive on (0,1) -/
theorem dalzell_integrand_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) := by
  apply div_pos
  · apply mul_pos
    · positivity
    · apply pow_pos; linarith
  · positivity

-- ============================================================
-- PART III: Antiderivative and Integral Evaluation (FTC)
-- ============================================================

/-- The antiderivative F(x) = x⁷/7 - 2x⁶/3 + x⁵ - 4x³/3 + 4x - 4·arctan(x) -/
noncomputable def dalzellAntideriv (x : ℝ) : ℝ :=
  x ^ 7 / 7 - 2 * x ^ 6 / 3 + x ^ 5 - 4 * x ^ 3 / 3 + 4 * x - 4 * arctan x

/-- The decomposed integrand g(x) = x⁶ - 4x⁵ + 5x⁴ - 4x² + 4 - 4/(1+x²) -/
noncomputable def dalzellDecomposed (x : ℝ) : ℝ :=
  x ^ 6 - 4 * x ^ 5 + 5 * x ^ 4 - 4 * x ^ 2 + 4 - 4 / (1 + x ^ 2)

/-- F'(x) = g(x): the derivative of the antiderivative equals the decomposed integrand -/
theorem hasDerivAt_dalzellAntideriv (x : ℝ) :
    HasDerivAt dalzellAntideriv (dalzellDecomposed x) x := by
  unfold dalzellAntideriv dalzellDecomposed
  -- Individual term derivatives
  have h7 : HasDerivAt (fun x : ℝ => x ^ 7 / 7) (x ^ 6) x := by
    have := (hasDerivAt_pow 7 x).div_const (7 : ℝ)
    convert this using 1; push_cast; ring
  have h6 : HasDerivAt (fun x : ℝ => 2 * x ^ 6 / 3) (4 * x ^ 5) x := by
    have := ((hasDerivAt_pow 6 x).const_mul 2).div_const (3 : ℝ)
    convert this using 1; push_cast; ring
  have h5 : HasDerivAt (fun x : ℝ => x ^ 5) (5 * x ^ 4) x := by
    have := hasDerivAt_pow 5 x
    convert this using 1; push_cast; ring
  have h3 : HasDerivAt (fun x : ℝ => 4 * x ^ 3 / 3) (4 * x ^ 2) x := by
    have := ((hasDerivAt_pow 3 x).const_mul 4).div_const (3 : ℝ)
    convert this using 1; push_cast; ring
  have h1 : HasDerivAt (fun x : ℝ => 4 * x) (4 : ℝ) x := by
    have := (hasDerivAt_id x).const_mul (4 : ℝ)
    convert this using 1; simp
  have ha : HasDerivAt (fun x : ℝ => 4 * arctan x) (4 / (1 + x ^ 2)) x := by
    have := (hasDerivAt_arctan x).const_mul (4 : ℝ)
    convert this using 1; ring
  -- Chain: F = term1 - term2 + term3 - term4 + term5 - term6
  have hcomb := ((((h7.sub h6).add h5).sub h3).add h1).sub ha
  -- The chained function matches dalzellAntideriv (left-associative +/-)
  -- The derivative needs ring normalization
  convert hcomb using 1
  · rfl
  · ring

/-- The decomposed integrand is continuous -/
theorem continuous_dalzellDecomposed : Continuous dalzellDecomposed := by
  unfold dalzellDecomposed
  fun_prop

/-- F(0) = 0 -/
theorem dalzellAntideriv_zero : dalzellAntideriv 0 = 0 := by
  simp [dalzellAntideriv]

/-- F(1) = 22/7 - π -/
theorem dalzellAntideriv_one : dalzellAntideriv 1 = 22 / 7 - Real.pi := by
  unfold dalzellAntideriv
  rw [arctan_one]
  ring

/-- The integral of the decomposed form from 0 to 1 equals 22/7 - π via FTC -/
theorem dalzell_decomposed_integral :
    ∫ x in (0 : ℝ)..1, dalzellDecomposed x = 22 / 7 - Real.pi := by
  have h_deriv : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt dalzellAntideriv (dalzellDecomposed x) x :=
    fun x _ => hasDerivAt_dalzellAntideriv x
  have h_int : IntervalIntegrable dalzellDecomposed volume 0 1 :=
    continuous_dalzellDecomposed.intervalIntegrable 0 1
  rw [integral_eq_sub_of_hasDerivAt h_deriv h_int,
      dalzellAntideriv_one, dalzellAntideriv_zero, sub_zero]

-- ============================================================
-- PART IV: The Dalzell-Niven Integral Identity
-- ============================================================

/-- The original integrand equals the decomposed form -/
theorem dalzell_integrand_eq_decomposed (x : ℝ) :
    x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) = dalzellDecomposed x := by
  exact dalzell_integrand_decomposition x

/-- The original integrand is continuous -/
theorem continuous_dalzell_integrand :
    Continuous (fun x => x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2)) := by
  apply Continuous.div
  · exact (continuous_pow 4).mul ((continuous_const.sub continuous_id').pow 4)
  · exact continuous_const.add (continuous_pow 2)
  · intro x; positivity

/-- **Dalzell-Niven Integral Identity**:
    ∫₀¹ x⁴(1-x)⁴/(1+x²) dx = 22/7 - π -/
theorem dalzell_niven_integral :
    ∫ x in (0 : ℝ)..1, x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) = 22 / 7 - Real.pi := by
  have h_eq : (fun x => x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2)) = dalzellDecomposed := by
    ext x; exact dalzell_integrand_eq_decomposed x
  rw [show ∫ x in (0 : ℝ)..1, x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) =
      ∫ x in (0 : ℝ)..1, dalzellDecomposed x from by rw [← h_eq]]
  exact dalzell_decomposed_integral

-- ============================================================
-- PART V: π < 22/7 from the Integral
-- ============================================================

/-- **Main Result**: π < 22/7 via the Dalzell-Niven integral.
    The integrand is strictly positive on (0,1), so the integral is positive,
    giving 22/7 - π > 0, hence π < 22/7. -/
theorem pi_lt_twentytwo_over_seven : Real.pi < 22 / 7 := by
  have h_integral := dalzell_niven_integral
  have h_pos : 0 < ∫ x in (0 : ℝ)..1, x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) := by
    apply integral_pos (by norm_num : (0 : ℝ) < 1)
    · exact continuous_dalzell_integrand.continuousOn
    · intro x hx
      exact dalzell_integrand_nonneg (le_of_lt hx.1) hx.2
    · exact ⟨1/2, mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
        dalzell_integrand_pos (by norm_num) (by norm_num)⟩
  linarith

/-- Quantitative: 0 < 22/7 - π -/
theorem twentytwo_over_seven_minus_pi_pos : (0 : ℝ) < 22 / 7 - Real.pi := by
  linarith [pi_lt_twentytwo_over_seven]

-- ============================================================
-- PART VI: Bound on the Error
-- ============================================================

/-- Upper bound: x⁴(1-x)⁴/(1+x²) ≤ x⁴(1-x)⁴ on [0,1] -/
theorem dalzell_integrand_le_numerator {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) ≤ x ^ 4 * (1 - x) ^ 4 := by
  rw [div_le_iff (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  have h1 : 1 ≤ 1 + x ^ 2 := le_add_of_nonneg_right (sq_nonneg x)
  calc x ^ 4 * (1 - x) ^ 4
      = x ^ 4 * (1 - x) ^ 4 * 1 := (mul_one _).symm
    _ ≤ x ^ 4 * (1 - x) ^ 4 * (1 + x ^ 2) := by
        apply mul_le_mul_of_nonneg_left h1
        apply mul_nonneg <;> [positivity; apply pow_nonneg; linarith]

end AreaOfCircleOQ03OQ02OQ02
