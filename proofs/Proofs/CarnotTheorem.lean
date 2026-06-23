import Mathlib

/-
# Carnot's Theorem (angle form)

For a triangle with interior angles `A, B, C` (so `A + B + C = π`), Carnot's
theorem states that the signed distances from the circumcenter `O` to the three
sides sum to `R + r`, where `R` is the circumradius and `r` the inradius.
Dividing by `R` and using the standard chord-distance identity (the signed
distance from `O` to the side opposite an angle `θ` is `R cos θ`) this is
equivalent to the purely trigonometric statement

  `cos A + cos B + cos C = 1 + r / R`.

Since `r / R = 4 sin(A/2) sin(B/2) sin(C/2)` for any triangle (Euler's formula
for the inradius), the analytic core of Carnot's theorem is the identity

  `cos A + cos B + cos C = 1 + 4 sin(A/2) sin(B/2) sin(C/2)`,

valid for any reals with `A + B + C = π`. This file proves that identity
axiom-free from the FTC-free trigonometric primitives in Mathlib, together with
the companion fundamental cosine identity

  `cos²A + cos²B + cos²C + 2 cos A cos B cos C = 1`.

**No axioms, no sorries.**
-/

open Real

namespace CarnotTheorem

/-- Double-angle in the `1 - 2 sin²` form. -/
private theorem cos_two_mul_sin (x : ℝ) : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul']
  linear_combination Real.cos_sq_add_sin_sq x

/-- **Carnot's theorem (angle form).**  For any reals `A, B, C` with
`A + B + C = π`,
`cos A + cos B + cos C = 1 + 4 sin(A/2) sin(B/2) sin(C/2)`.

Equivalently `cos A + cos B + cos C = 1 + r/R` for a triangle with circumradius
`R` and inradius `r`, the form of Carnot's theorem obtained by summing the
signed circumcenter-to-side distances `R cos A + R cos B + R cos C = R + r`. -/
theorem carnot_cos_sum (A B C : ℝ) (h : A + B + C = π) :
    Real.cos A + Real.cos B + Real.cos C
      = 1 + 4 * Real.sin (A / 2) * Real.sin (B / 2) * Real.sin (C / 2) := by
  -- Express `sin (C/2)` through the half-angles of `A` and `B`.
  have hsc : Real.sin (C / 2)
      = Real.cos (A / 2) * Real.cos (B / 2) - Real.sin (A / 2) * Real.sin (B / 2) := by
    have hch : C / 2 = π / 2 - (A / 2 + B / 2) := by linarith
    rw [hch, Real.sin_pi_div_two_sub, Real.cos_add]
  -- Rewrite each cosine in `1 - 2 sin²(·/2)` form.
  have hcA : Real.cos A = 1 - 2 * Real.sin (A / 2) ^ 2 := by
    have h := cos_two_mul_sin (A / 2); rwa [show 2 * (A / 2) = A by ring] at h
  have hcB : Real.cos B = 1 - 2 * Real.sin (B / 2) ^ 2 := by
    have h := cos_two_mul_sin (B / 2); rwa [show 2 * (B / 2) = B by ring] at h
  have hcC : Real.cos C = 1 - 2 * Real.sin (C / 2) ^ 2 := by
    have h := cos_two_mul_sin (C / 2); rwa [show 2 * (C / 2) = C by ring] at h
  rw [hcA, hcB, hcC, hsc]
  linear_combination (-2 * Real.cos (B / 2) ^ 2) * Real.sin_sq_add_cos_sq (A / 2)
    + (2 * (Real.sin (A / 2) ^ 2 - 1)) * Real.sin_sq_add_cos_sq (B / 2)

/-- **Fundamental triangle cosine identity.**  For any reals `A, B, C` with
`A + B + C = π`,
`cos²A + cos²B + cos²C + 2 cos A cos B cos C = 1`.

This is the companion polynomial form of Carnot's theorem; it follows by writing
`C = π - A - B`, so `cos C = -cos(A+B)`, and a `ring` computation modulo the
Pythagorean identities for `A` and `B`. -/
theorem carnot_cos_sq_sum (A B C : ℝ) (h : A + B + C = π) :
    Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2
      + 2 * Real.cos A * Real.cos B * Real.cos C = 1 := by
  have hcC : Real.cos C = -(Real.cos A * Real.cos B - Real.sin A * Real.sin B) := by
    have hch : C = π - (A + B) := by linarith
    rw [hch, Real.cos_pi_sub, Real.cos_add]
  rw [hcC]
  linear_combination (1 - Real.cos B ^ 2) * Real.sin_sq_add_cos_sq A
    + (Real.sin A ^ 2) * Real.sin_sq_add_cos_sq B

end CarnotTheorem
