import Mathlib
import Proofs.AreaOfCircleOQ03OQ02OQ02

/-
# Generalized Dalzell Integral: Sharper Rational Bounds on π

## Research Problem: area-of-circle-oq-03-oq-02-oq-02-oq-01

**Open Question** (from AreaOfCircleOQ03OQ02OQ02): Can the generalized Dalzell integral
∫₀¹ x^(4n)(1-x)^(4n)/(1+x²) dx be used to derive sharper rational bounds on π?

**Answer**: Yes. This file proves the n=2 case:

  ∫₀¹ x⁸(1-x)⁸/(1+x²) dx = 4π - 188684/15015

Since the integral is positive (the integrand is nonneg on [0,1]), we get:

  π > 47171/15015 ≈ 3.14156...

Combined with the n=1 result π < 22/7 ≈ 3.14286 (from parent proof), we obtain:

  **47171/15015 < π < 22/7**

## Mathematical Content

The key identity is:
  x⁸(1-x)⁸ = (1+x²) · Q(x) + 16
where Q(x) = x¹⁴ - 8x¹³ + 27x¹² - 48x¹¹ + 43x¹⁰ - 8x⁹ - 15x⁸ + 16x⁶ - 16x⁴ + 16x² - 16

Dividing by (1+x²):
  x⁸(1-x)⁸/(1+x²) = Q(x) + 16/(1+x²)

Integrating from 0 to 1:
  ∫₀¹ x⁸(1-x)⁸/(1+x²) dx = ∫₀¹ Q(x) dx + 16·arctan(1) = -188684/15015 + 4π

## Connection to Parent Proofs

- **AreaOfCircleOQ03OQ02OQ02**: Proves π < 22/7 via the n=1 Dalzell integral
- **This file**: Proves π > 47171/15015 via the n=2 case, establishing a two-sided bound

## Tags: pi, integral, rational-approximation, Dalzell, bounds
-/

namespace AreaOfCircleOQ03OQ02OQ02OQ01

open Real MeasureTheory Set intervalIntegral

-- ============================================================
-- Part I: Polynomial Identity (Remainder = +16)
-- ============================================================

/-- The n=2 Dalzell polynomial identity.
    When dividing x⁸(1-x)⁸ by (1+x²), the remainder is +16 (not -4 as for n=1).
    This means the n=2 integral gives a LOWER bound on π. -/
theorem dalzell2_polynomial_identity (x : ℝ) :
    x ^ 8 * (1 - x) ^ 8 =
    (1 + x ^ 2) * (x ^ 14 - 8 * x ^ 13 + 27 * x ^ 12 - 48 * x ^ 11 + 43 * x ^ 10 -
      8 * x ^ 9 - 15 * x ^ 8 + 16 * x ^ 6 - 16 * x ^ 4 + 16 * x ^ 2 - 16) + 16 := by
  ring

/-- The n=2 Dalzell integrand decomposes as Q(x) + 16/(1+x²) -/
theorem dalzell2_integrand_decomposition (x : ℝ) :
    x ^ 8 * (1 - x) ^ 8 / (1 + x ^ 2) =
    (x ^ 14 - 8 * x ^ 13 + 27 * x ^ 12 - 48 * x ^ 11 + 43 * x ^ 10 -
      8 * x ^ 9 - 15 * x ^ 8 + 16 * x ^ 6 - 16 * x ^ 4 + 16 * x ^ 2 - 16) +
    16 / (1 + x ^ 2) := by
  have h : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

-- ============================================================
-- Part II: Positivity of the Integrand
-- ============================================================

/-- The n=2 Dalzell integrand is nonneg on [0,1] -/
theorem dalzell2_integrand_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x ^ 8 * (1 - x) ^ 8 / (1 + x ^ 2) := by
  apply div_nonneg
  · apply mul_nonneg
    · positivity
    · apply pow_nonneg; linarith
  · positivity

/-- The n=2 Dalzell integrand is strictly positive on (0,1) -/
theorem dalzell2_integrand_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < x ^ 8 * (1 - x) ^ 8 / (1 + x ^ 2) := by
  apply div_pos
  · apply mul_pos
    · positivity
    · apply pow_pos; linarith
  · positivity

-- ============================================================
-- Part III: Antiderivative via FTC
-- ============================================================

/-- The antiderivative of the n=2 Dalzell integrand.
    F₂(x) = x¹⁵/15 - 4x¹⁴/7 + 27x¹³/13 - 4x¹² + 43x¹¹/11
            - 4x¹⁰/5 - 5x⁹/3 + 16x⁷/7 - 16x⁵/5 + 16x³/3 - 16x + 16·arctan(x) -/
noncomputable def dalzell2Antideriv (x : ℝ) : ℝ :=
  x ^ 15 / 15 - 4 * x ^ 14 / 7 + 27 * x ^ 13 / 13 - 4 * x ^ 12 + 43 * x ^ 11 / 11
  - 4 * x ^ 10 / 5 - 5 * x ^ 9 / 3 + 16 * x ^ 7 / 7 - 16 * x ^ 5 / 5 + 16 * x ^ 3 / 3
  - 16 * x + 16 * arctan x

/-- The decomposed form of the integrand (antiderivative's derivative) -/
noncomputable def dalzell2Decomposed (x : ℝ) : ℝ :=
  x ^ 14 - 8 * x ^ 13 + 27 * x ^ 12 - 48 * x ^ 11 + 43 * x ^ 10 -
  8 * x ^ 9 - 15 * x ^ 8 + 16 * x ^ 6 - 16 * x ^ 4 + 16 * x ^ 2 - 16 +
  16 / (1 + x ^ 2)

/-- F₂'(x) = dalzell2Decomposed(x): the antiderivative has the right derivative -/
theorem hasDerivAt_dalzell2Antideriv (x : ℝ) :
    HasDerivAt dalzell2Antideriv (dalzell2Decomposed x) x := by
  unfold dalzell2Antideriv dalzell2Decomposed
  have h15 : HasDerivAt (fun x : ℝ => x ^ 15 / 15) (x ^ 14) x := by
    have := (hasDerivAt_pow 15 x).div_const (15 : ℝ)
    convert this using 1; push_cast; ring
  have h14 : HasDerivAt (fun x : ℝ => 4 * x ^ 14 / 7) (8 * x ^ 13) x := by
    have := ((hasDerivAt_pow 14 x).const_mul 4).div_const (7 : ℝ)
    convert this using 1; push_cast; ring
  have h13 : HasDerivAt (fun x : ℝ => 27 * x ^ 13 / 13) (27 * x ^ 12) x := by
    have := ((hasDerivAt_pow 13 x).const_mul 27).div_const (13 : ℝ)
    convert this using 1; push_cast; ring
  have h12 : HasDerivAt (fun x : ℝ => 4 * x ^ 12) (48 * x ^ 11) x := by
    have := (hasDerivAt_pow 12 x).const_mul (4 : ℝ)
    convert this using 1; push_cast; ring
  have h11 : HasDerivAt (fun x : ℝ => 43 * x ^ 11 / 11) (43 * x ^ 10) x := by
    have := ((hasDerivAt_pow 11 x).const_mul 43).div_const (11 : ℝ)
    convert this using 1; push_cast; ring
  have h10 : HasDerivAt (fun x : ℝ => 4 * x ^ 10 / 5) (8 * x ^ 9) x := by
    have := ((hasDerivAt_pow 10 x).const_mul 4).div_const (5 : ℝ)
    convert this using 1; push_cast; ring
  have h9 : HasDerivAt (fun x : ℝ => 5 * x ^ 9 / 3) (15 * x ^ 8) x := by
    have := ((hasDerivAt_pow 9 x).const_mul 5).div_const (3 : ℝ)
    convert this using 1; push_cast; ring
  have h7 : HasDerivAt (fun x : ℝ => 16 * x ^ 7 / 7) (16 * x ^ 6) x := by
    have := ((hasDerivAt_pow 7 x).const_mul 16).div_const (7 : ℝ)
    convert this using 1; push_cast; ring
  have h5 : HasDerivAt (fun x : ℝ => 16 * x ^ 5 / 5) (16 * x ^ 4) x := by
    have := ((hasDerivAt_pow 5 x).const_mul 16).div_const (5 : ℝ)
    convert this using 1; push_cast; ring
  have h3 : HasDerivAt (fun x : ℝ => 16 * x ^ 3 / 3) (16 * x ^ 2) x := by
    have := ((hasDerivAt_pow 3 x).const_mul 16).div_const (3 : ℝ)
    convert this using 1; push_cast; ring
  have h1 : HasDerivAt (fun x : ℝ => 16 * x) (16 : ℝ) x := by
    have := (hasDerivAt_id x).const_mul (16 : ℝ)
    convert this using 1; simp
  have ha : HasDerivAt (fun x : ℝ => 16 * arctan x) (16 / (1 + x ^ 2)) x := by
    have := (hasDerivAt_arctan x).const_mul (16 : ℝ)
    convert this using 1; ring
  -- Chain all terms together (left-associative, matching the definition's parsing)
  have hcomb :=
    ((((((((((h15.sub h14).add h13).sub h12).add h11).sub h10).sub h9).add h7).sub h5).add h3).sub h1).add ha
  convert hcomb using 1
  · rfl
  · ring

/-- The decomposed integrand is continuous -/
theorem continuous_dalzell2Decomposed : Continuous dalzell2Decomposed := by
  unfold dalzell2Decomposed
  fun_prop

/-- F₂(0) = 0 -/
theorem dalzell2Antideriv_zero : dalzell2Antideriv 0 = 0 := by
  simp [dalzell2Antideriv]

/-- F₂(1) = 4π - 188684/15015 -/
theorem dalzell2Antideriv_one : dalzell2Antideriv 1 = 4 * Real.pi - 188684 / 15015 := by
  unfold dalzell2Antideriv
  rw [arctan_one]
  ring

/-- The integral of the decomposed form from 0 to 1 equals 4π - 188684/15015 -/
theorem dalzell2_decomposed_integral :
    ∫ x in (0 : ℝ)..1, dalzell2Decomposed x = 4 * Real.pi - 188684 / 15015 := by
  have h_deriv : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt dalzell2Antideriv (dalzell2Decomposed x) x :=
    fun x _ => hasDerivAt_dalzell2Antideriv x
  have h_int : IntervalIntegrable dalzell2Decomposed volume 0 1 :=
    continuous_dalzell2Decomposed.intervalIntegrable 0 1
  rw [integral_eq_sub_of_hasDerivAt h_deriv h_int,
      dalzell2Antideriv_one, dalzell2Antideriv_zero, sub_zero]

-- ============================================================
-- Part IV: The n=2 Dalzell Integral Identity
-- ============================================================

/-- The n=2 integrand is continuous -/
theorem continuous_dalzell2_integrand :
    Continuous (fun x => x ^ 8 * (1 - x) ^ 8 / (1 + x ^ 2)) := by
  apply Continuous.div
  · exact (continuous_pow 8).mul ((continuous_const.sub continuous_id').pow 8)
  · exact continuous_const.add (continuous_pow 2)
  · intro x; positivity

/-- The original integrand equals the decomposed form -/
theorem dalzell2_integrand_eq_decomposed :
    (fun x : ℝ => x ^ 8 * (1 - x) ^ 8 / (1 + x ^ 2)) = dalzell2Decomposed := by
  ext x; exact dalzell2_integrand_decomposition x

/-- **The n=2 Dalzell Integral Identity**:
    ∫₀¹ x⁸(1-x)⁸/(1+x²) dx = 4π - 188684/15015 -/
theorem dalzell2_integral :
    ∫ x in (0 : ℝ)..1, x ^ 8 * (1 - x) ^ 8 / (1 + x ^ 2) =
    4 * Real.pi - 188684 / 15015 := by
  rw [show ∫ x in (0 : ℝ)..1, x ^ 8 * (1 - x) ^ 8 / (1 + x ^ 2) =
      ∫ x in (0 : ℝ)..1, dalzell2Decomposed x from by
    congr 1; exact dalzell2_integrand_eq_decomposed]
  exact dalzell2_decomposed_integral

-- ============================================================
-- Part V: π > 47171/15015 from the Integral
-- ============================================================

/-- **Main Result**: π > 47171/15015 via the n=2 Dalzell integral.
    The n=2 integral gives a LOWER bound (opposite direction from n=1).
    The remainder for n=2 is +16 instead of -4, flipping the inequality. -/
theorem pi_gt_lower_bound : (47171 : ℝ) / 15015 < Real.pi := by
  have h_integral := dalzell2_integral
  have h_pos : 0 < ∫ x in (0 : ℝ)..1, x ^ 8 * (1 - x) ^ 8 / (1 + x ^ 2) := by
    apply integral_pos (by norm_num : (0 : ℝ) < 1)
    · exact continuous_dalzell2_integrand.continuousOn
    · intro x hx
      exact dalzell2_integrand_nonneg (le_of_lt hx.1) hx.2
    · exact ⟨1/2, mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
        dalzell2_integrand_pos (by norm_num) (by norm_num)⟩
  linarith

-- ============================================================
-- Part VI: The Two-Sided Rational Sandwich for π
-- ============================================================

/-- **Fundamental Sandwich**: 47171/15015 < π < 22/7.
    Combining the n=1 upper bound (from parent proof) with the n=2 lower bound.

    This gives a rigorous two-sided rational approximation to π:
    - Lower bound: 47171/15015 ≈ 3.14156...
    - True value:  π           ≈ 3.14159...
    - Upper bound: 22/7        ≈ 3.14286...

    The Dalzell integral sequence provides increasingly tight bounds:
    for larger n, the integrals ∫₀¹ x^(4n)(1-x)^(4n)/(1+x²) dx → 0,
    yielding sharper rational approximations to π. -/
theorem pi_rational_sandwich :
    (47171 : ℝ) / 15015 < Real.pi ∧ Real.pi < 22 / 7 :=
  ⟨pi_gt_lower_bound, AreaOfCircleOQ03OQ02OQ02.pi_lt_twentytwo_over_seven⟩

/-- Explicit lower bound: π > 3.141556... -/
theorem pi_gt_3141556 : (3141556 : ℝ) / 1000000 < Real.pi := by
  have h1 := pi_gt_lower_bound
  have h2 : (3141556 : ℝ) / 1000000 < 47171 / 15015 := by norm_num
  linarith

end AreaOfCircleOQ03OQ02OQ02OQ01
