import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.RingTheory.Polynomial.Chebyshev

/-
# De Moivre OQ-01: Explicit Extraction of cos(nθ) and sin(nθ)

## Open Question

Given De Moivre's theorem, formalize the explicit extraction of cos(nθ) and sin(nθ)
as polynomial expressions in cos(θ) and sin(θ), obtained by comparing real and
imaginary parts of (cos θ + i sin θ)^n.

## Mathematical Content

De Moivre's theorem states:
  (cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)

Expanding the left side via the binomial theorem and comparing parts yields:
  cos(nθ) = Σ_{j=0}^{⌊n/2⌋} C(n,2j) (-1)^j cos^{n-2j}(θ) sin^{2j}(θ)
  sin(nθ) = Σ_{j=0}^{⌊(n-1)/2⌋} C(n,2j+1) (-1)^j cos^{n-2j-1}(θ) sin^{2j+1}(θ)

## Key Result (Chebyshev Polynomials)

The abstract pattern is captured by Chebyshev polynomials T_n and U_n:
  cos(nθ) = T_n(cos θ)
  sin((n+1)θ) = U_n(cos θ) · sin θ

These polynomials satisfy the recurrences:
  T_0 = 1,   T_1 = X,   T_{n+2} = 2X · T_{n+1} - T_n
  U_0 = 1,   U_1 = 2X,  U_{n+2} = 2X · U_{n+1} - U_n

The recurrences themselves follow from comparing real/imaginary parts in the
De Moivre identity (e^{iθ})^{n+2} = (2cos θ)(e^{iθ})^{n+1} - (e^{iθ})^n,
which holds since e^{iθ} + e^{-iθ} = 2cos θ.
-/

open Polynomial Polynomial.Chebyshev Real

namespace DeMoivreOQ01

-- ============================================================
-- PART 1: Main Extraction Theorems (wrappers around Mathlib)
-- ============================================================

/-- **Extraction Theorem (cos)**: cos(nθ) equals the nth Chebyshev polynomial of the first
kind evaluated at cos(θ). This captures the "real part extraction" from De Moivre's theorem.

Proof: The Chebyshev recurrence T_{n+2} = 2X T_{n+1} - T_n corresponds exactly to
the identity cos((n+2)θ) = 2cos(θ)cos((n+1)θ) - cos(nθ), which follows by comparing
real parts in De Moivre. -/
theorem cos_nsmul_chebyshev_T (θ : ℝ) (n : ℤ) :
    Real.cos ((↑n : ℝ) * θ) = (T ℝ n).eval (Real.cos θ) :=
  (Polynomial.Chebyshev.T_real_cos θ n).symm

/-- **Extraction Theorem (sin)**: sin((n+1)θ) equals the nth Chebyshev polynomial of the second
kind evaluated at cos(θ), times sin(θ). This captures the "imaginary part extraction".

The formula sin(nθ) = U_{n-1}(cos θ) · sin θ shows sin(nθ) is always sin(θ) times
a polynomial in cos(θ), arising from comparing imaginary parts in De Moivre. -/
theorem sin_nsmul_chebyshev_U (θ : ℝ) (n : ℤ) :
    Real.sin (((↑n : ℝ) + 1) * θ) = (U ℝ n).eval (Real.cos θ) * Real.sin θ :=
  (Polynomial.Chebyshev.U_real_cos θ n).symm

-- ============================================================
-- PART 2: Existence Theorem
-- ============================================================

/-- **Existence Theorem (cos)**: For every integer n, cos(nθ) can be expressed as a polynomial
in cos(θ). This is the core content of the "real part extraction" from De Moivre's theorem. -/
theorem cos_nsmul_is_poly_in_cos (n : ℤ) :
    ∃ P : ℝ[X], ∀ θ : ℝ, P.eval (Real.cos θ) = Real.cos ((↑n : ℝ) * θ) :=
  ⟨T ℝ n, fun θ => Polynomial.Chebyshev.T_real_cos θ n⟩

/-- **Existence Theorem (sin)**: For every integer n, sin((n+1)θ)/sin(θ) is a polynomial
in cos(θ) — when sin θ ≠ 0. This is the "imaginary part extraction" result. -/
theorem sin_nsmul_div_sin_is_poly_in_cos (n : ℤ) :
    ∃ Q : ℝ[X], ∀ θ : ℝ, Q.eval (Real.cos θ) * Real.sin θ = Real.sin (((↑n : ℝ) + 1) * θ) :=
  ⟨U ℝ n, fun θ => Polynomial.Chebyshev.U_real_cos θ n⟩

-- ============================================================
-- PART 3: Explicit Chebyshev Polynomial Computations
-- ============================================================

/-- T_3 = 4X³ - 3X  (i.e., cos(3θ) = 4cos³θ - 3cosθ) -/
theorem T_three : T ℝ 3 = 4 * X ^ 3 - 3 * X := by
  have h : T ℝ (1 + 2 : ℤ) = 2 * X * T ℝ (1 + 1 : ℤ) - T ℝ 1 := T_add_two (R := ℝ) 1
  simp only [show (1 + 2 : ℤ) = 3 from by decide, show (1 + 1 : ℤ) = 2 from by decide] at h
  rw [h, T_two, T_one]; ring

/-- T_4 = 8X⁴ - 8X² + 1  (i.e., cos(4θ) = 8cos⁴θ - 8cos²θ + 1) -/
theorem T_four : T ℝ 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 := by
  have h : T ℝ (2 + 2 : ℤ) = 2 * X * T ℝ (2 + 1 : ℤ) - T ℝ 2 := T_add_two (R := ℝ) 2
  simp only [show (2 + 2 : ℤ) = 4 from by decide, show (2 + 1 : ℤ) = 3 from by decide] at h
  rw [h, T_three, T_two]; ring

/-- T_5 = 16X⁵ - 20X³ + 5X  (i.e., cos(5θ) = 16cos⁵θ - 20cos³θ + 5cosθ) -/
theorem T_five : T ℝ 5 = 16 * X ^ 5 - 20 * X ^ 3 + 5 * X := by
  have h : T ℝ (3 + 2 : ℤ) = 2 * X * T ℝ (3 + 1 : ℤ) - T ℝ 3 := T_add_two (R := ℝ) 3
  simp only [show (3 + 2 : ℤ) = 5 from by decide, show (3 + 1 : ℤ) = 4 from by decide] at h
  rw [h, T_four, T_three]; ring

-- U_two : U R 2 = 4 * X ^ 2 - 1 is already in Mathlib

/-- U_3 = 8X³ - 4X  (i.e., sin(4θ) = (8cos³θ - 4cosθ) sinθ) -/
theorem U_three : U ℝ 3 = 8 * X ^ 3 - 4 * X := by
  have h : U ℝ (1 + 2 : ℤ) = 2 * X * U ℝ (1 + 1 : ℤ) - U ℝ 1 := U_add_two (R := ℝ) 1
  simp only [show (1 + 2 : ℤ) = 3 from by decide, show (1 + 1 : ℤ) = 2 from by decide] at h
  rw [h, U_two, U_one]; ring

/-- U_4 = 16X⁴ - 12X² + 1  (i.e., sin(5θ) = (16cos⁴θ - 12cos²θ + 1) sinθ) -/
theorem U_four : U ℝ 4 = 16 * X ^ 4 - 12 * X ^ 2 + 1 := by
  have h : U ℝ (2 + 2 : ℤ) = 2 * X * U ℝ (2 + 1 : ℤ) - U ℝ 2 := U_add_two (R := ℝ) 2
  simp only [show (2 + 2 : ℤ) = 4 from by decide, show (2 + 1 : ℤ) = 3 from by decide] at h
  rw [h, U_three, U_two]; ring

-- ============================================================
-- PART 4: Explicit Multiple Angle Formulas
-- (proved directly via cos_add/sin_add + Pythagorean identity)
-- ============================================================

-- Helper: shorthand for the Pythagorean identity
private lemma cos_sq_add_sin_sq (θ : ℝ) : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
  linarith [Real.sin_sq_add_cos_sq θ]

/-- **Double Angle (cos)**: cos(2θ) = 2cos²θ - 1

From De Moivre: real part of (cos θ + i sin θ)² = cos²θ - sin²θ = 2cos²θ - 1 -/
theorem cos_two_mul_eq (θ : ℝ) : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
  have hadd : Real.cos (θ + θ) = Real.cos θ * Real.cos θ - Real.sin θ * Real.sin θ :=
    Real.cos_add θ θ
  have hid := Real.sin_sq_add_cos_sq θ
  have hsc : Real.cos θ * Real.cos θ = Real.cos θ ^ 2 := by ring
  have hss : Real.sin θ * Real.sin θ = Real.sin θ ^ 2 := by ring
  rw [show (2 : ℝ) * θ = θ + θ from by ring, hadd]
  linarith

/-- **Double Angle (sin)**: sin(2θ) = 2 sin θ cos θ

From De Moivre: imaginary part of (cos θ + i sin θ)² = 2 cos θ sin θ -/
theorem sin_two_mul_eq (θ : ℝ) : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := by
  have hadd : Real.sin (θ + θ) = Real.sin θ * Real.cos θ + Real.cos θ * Real.sin θ :=
    Real.sin_add θ θ
  rw [show (2 : ℝ) * θ = θ + θ from by ring, hadd]; ring

/-- **Triple Angle (cos)**: cos(3θ) = 4cos³θ - 3cosθ -/
theorem cos_three_mul_eq (θ : ℝ) : Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := by
  rw [show (3 : ℝ) * θ = 2 * θ + θ from by ring, Real.cos_add, cos_two_mul_eq, sin_two_mul_eq]
  have hid := Real.sin_sq_add_cos_sq θ
  have hs2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
  calc (2 * Real.cos θ ^ 2 - 1) * Real.cos θ - 2 * Real.sin θ * Real.cos θ * Real.sin θ
      = (2 * Real.cos θ ^ 2 - 1) * Real.cos θ - 2 * Real.cos θ * Real.sin θ ^ 2 := by ring
    _ = (2 * Real.cos θ ^ 2 - 1) * Real.cos θ - 2 * Real.cos θ * (1 - Real.cos θ ^ 2) := by
        rw [hs2]
    _ = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := by ring

/-- **Triple Angle (sin)**: sin(3θ) = 3sinθ - 4sin³θ -/
theorem sin_three_mul_eq (θ : ℝ) : Real.sin (3 * θ) = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 := by
  rw [show (3 : ℝ) * θ = 2 * θ + θ from by ring, Real.sin_add, sin_two_mul_eq, cos_two_mul_eq]
  have hid := Real.sin_sq_add_cos_sq θ
  have hc2 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith
  calc 2 * Real.sin θ * Real.cos θ * Real.cos θ + (2 * Real.cos θ ^ 2 - 1) * Real.sin θ
      = 2 * Real.sin θ * Real.cos θ ^ 2 + (2 * Real.cos θ ^ 2 - 1) * Real.sin θ := by ring
    _ = 2 * Real.sin θ * (1 - Real.sin θ ^ 2) + (2 * (1 - Real.sin θ ^ 2) - 1) * Real.sin θ := by
        rw [hc2]
    _ = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 := by ring

/-- **Quadruple Angle (cos)**: cos(4θ) = 8cos⁴θ - 8cos²θ + 1

Proof: cos(4θ) = 2cos²(2θ) - 1 = 2(2cos²θ - 1)² - 1 -/
theorem cos_four_mul_eq (θ : ℝ) :
    Real.cos (4 * θ) = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by
  rw [show (4 : ℝ) * θ = 2 * (2 * θ) from by ring, cos_two_mul_eq, cos_two_mul_eq]
  ring

/-- **Quadruple Angle (sin)**: sin(4θ) = (8cos³θ - 4cosθ) sinθ -/
theorem sin_four_mul_eq (θ : ℝ) :
    Real.sin (4 * θ) = (8 * Real.cos θ ^ 3 - 4 * Real.cos θ) * Real.sin θ := by
  rw [show (4 : ℝ) * θ = 2 * (2 * θ) from by ring, sin_two_mul_eq, sin_two_mul_eq, cos_two_mul_eq]
  ring

/-- **Quintuple Angle (cos)**: cos(5θ) = 16cos⁵θ - 20cos³θ + 5cosθ -/
theorem cos_five_mul_eq (θ : ℝ) :
    Real.cos (5 * θ) = 16 * Real.cos θ ^ 5 - 20 * Real.cos θ ^ 3 + 5 * Real.cos θ := by
  rw [show (5 : ℝ) * θ = 4 * θ + θ from by ring, Real.cos_add, cos_four_mul_eq]
  rw [show Real.sin (4 * θ) = (8 * Real.cos θ ^ 3 - 4 * Real.cos θ) * Real.sin θ from
    sin_four_mul_eq θ]
  have hid := Real.sin_sq_add_cos_sq θ
  have hs2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
  calc (8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1) * Real.cos θ -
      (8 * Real.cos θ ^ 3 - 4 * Real.cos θ) * Real.sin θ * Real.sin θ
      = (8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1) * Real.cos θ -
        (8 * Real.cos θ ^ 3 - 4 * Real.cos θ) * Real.sin θ ^ 2 := by ring
    _ = (8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1) * Real.cos θ -
        (8 * Real.cos θ ^ 3 - 4 * Real.cos θ) * (1 - Real.cos θ ^ 2) := by rw [hs2]
    _ = 16 * Real.cos θ ^ 5 - 20 * Real.cos θ ^ 3 + 5 * Real.cos θ := by ring

/-- **Quintuple Angle (sin)**: sin(5θ) = (16cos⁴θ - 12cos²θ + 1) sinθ -/
theorem sin_five_mul_eq (θ : ℝ) :
    Real.sin (5 * θ) = (16 * Real.cos θ ^ 4 - 12 * Real.cos θ ^ 2 + 1) * Real.sin θ := by
  rw [show (5 : ℝ) * θ = 4 * θ + θ from by ring, Real.sin_add, sin_four_mul_eq, cos_four_mul_eq]
  ring

-- ============================================================
-- PART 5: Cosine Recurrence (from De Moivre)
-- ============================================================

/-- **Recurrence for cos**: cos((n+2)θ) = 2cos(θ)cos((n+1)θ) - cos(nθ).

This is the key identity arising from De Moivre: comparing real parts in
  (e^{iθ})^{n+2} = (2cos θ)(e^{iθ})^{n+1} - (e^{iθ})^n
gives the Chebyshev recurrence T_{n+2}(x) = 2x·T_{n+1}(x) - T_n(x). -/
theorem cos_nsmul_rec (θ : ℝ) (n : ℤ) :
    Real.cos ((↑(n + 2) : ℝ) * θ) =
    2 * Real.cos θ * Real.cos ((↑(n + 1) : ℝ) * θ) - Real.cos ((↑n : ℝ) * θ) := by
  -- Proof via product-to-sum: cos(A+B) + cos(A-B) = 2 cos A cos B
  -- with A = (n+1)θ, B = θ gives cos((n+2)θ) + cos(nθ) = 2cosθ·cos((n+1)θ)
  have h1 : Real.cos ((↑(n + 2) : ℝ) * θ) =
      Real.cos ((↑(n + 1) : ℝ) * θ) * Real.cos θ - Real.sin ((↑(n + 1) : ℝ) * θ) * Real.sin θ := by
    have := Real.cos_add ((↑(n + 1) : ℝ) * θ) θ
    convert this using 2
    push_cast; ring
  have h2 : Real.cos ((↑n : ℝ) * θ) =
      Real.cos ((↑(n + 1) : ℝ) * θ) * Real.cos θ + Real.sin ((↑(n + 1) : ℝ) * θ) * Real.sin θ := by
    have := Real.cos_sub ((↑(n + 1) : ℝ) * θ) θ
    convert this using 2
    push_cast; ring
  have hcomm : Real.cos ((↑(n + 1) : ℝ) * θ) * Real.cos θ =
      Real.cos θ * Real.cos ((↑(n + 1) : ℝ) * θ) := mul_comm _ _
  linarith

end DeMoivreOQ01
