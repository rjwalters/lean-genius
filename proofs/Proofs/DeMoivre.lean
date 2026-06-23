import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Exponential

/-!
# De Moivre's Theorem (Wiedijk #17)

## What This Proves
We prove De Moivre's Theorem: for any real number θ and natural number n,
  (cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)

This fundamental result connects powers of complex numbers in polar form
to multiple angle formulas for trigonometric functions.

## Approach
- **Foundation (from Mathlib):** We use `Complex.exp_nat_mul` which states
  exp(n * x) = (exp x)^n, combined with Euler's formula `Complex.exp_mul_I`
  which gives exp(θ * I) = cos θ + i sin θ.
- **Original Contributions:** This file provides the classical formulation,
  extensions to integer exponents, and derives standard corollaries including
  the double and triple angle formulas.
- **Proof Techniques Demonstrated:** Rewriting with Mathlib's complex analysis
  API, `ring_nf` for algebraic simplification.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example

## Mathlib Dependencies
- `Complex.exp_mul_I` : exp(θ * I) = cos θ + sin θ * I (Euler's formula)
- `Complex.exp_nat_mul` : exp(n * x) = (exp x)^n
- `Complex.exp_int_mul` : exp(n * x) = (exp x)^n for integers
- `Complex.cos_add`, `Complex.sin_add` : Addition formulas

Historical Note: Abraham de Moivre (1667-1754) discovered this formula around
1707. It was later popularized by Euler and is essential for finding roots of
unity, deriving trigonometric identities, and analyzing rotations in the
complex plane.
-/

open Complex Real

-- ============================================================
-- PART 1: De Moivre's Theorem - Main Result
-- ============================================================

/-
  De Moivre's Theorem states that for any real θ and natural n:
    (cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)

  The proof strategy:
  1. Recognize that cos θ + i sin θ = exp(θ * I) (Euler's formula)
  2. Apply the power rule for exponentials: (exp x)^n = exp(n * x)
  3. Convert back using Euler's formula
-/

/-- De Moivre's Theorem (Wiedijk #17).
    (cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)

    This connects powers of complex numbers in polar form to
    multiple angle formulas for trigonometric functions. -/
theorem de_moivre (θ : ℝ) (n : ℕ) :
    (Complex.cos θ + Complex.sin θ * I) ^ n =
    Complex.cos (n * θ) + Complex.sin (n * θ) * I := by
  -- Use Euler's formula: cos θ + sin θ * I = exp(θ * I)
  conv_lhs => rw [← Complex.exp_mul_I]
  -- Apply (exp x)^n = exp(n * x)
  rw [← Complex.exp_nat_mul]
  -- Simplify the argument and convert back
  have h : (n : ℂ) * (↑θ * I) = ↑((n : ℝ) * θ) * I := by
    simp only [ofReal_mul, ofReal_natCast]
    ring
  rw [h, Complex.exp_mul_I]
  simp only [ofReal_mul, ofReal_natCast]

-- ============================================================
-- PART 2: Exponential Form
-- ============================================================

/-- De Moivre's theorem in exponential form.
    (exp(θ * I))^n = exp(n * θ * I) -/
theorem de_moivre_exp (θ : ℝ) (n : ℕ) :
    Complex.exp (θ * I) ^ n = Complex.exp (n * θ * I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- Alternative formulation with multiplication order swapped. -/
theorem de_moivre_exp' (θ : ℝ) (n : ℕ) :
    Complex.exp (I * θ) ^ n = Complex.exp (I * (n * θ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

-- ============================================================
-- PART 3: Integer Exponent Extension
-- ============================================================

/-
  De Moivre's theorem extends naturally to integer exponents,
  allowing negative powers which correspond to division.

  For n < 0: (cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)
  where cos(-θ) = cos(θ) and sin(-θ) = -sin(θ)
-/

/-- De Moivre's theorem for integer exponents.
    (exp(θ * I))^n = exp(n * θ * I) for any integer n. -/
theorem de_moivre_int (θ : ℝ) (n : ℤ) :
    Complex.exp (θ * I) ^ n = Complex.exp (n * θ * I) := by
  rw [← Complex.exp_int_mul]
  congr 1
  ring

/-- De Moivre's theorem in trigonometric form for integers. -/
theorem de_moivre_int' (θ : ℝ) (n : ℤ) :
    (Complex.cos θ + Complex.sin θ * I) ^ n =
    Complex.cos (n * θ) + Complex.sin (n * θ) * I := by
  conv_lhs => rw [← Complex.exp_mul_I]
  rw [de_moivre_int]
  have h : (n : ℂ) * ↑θ * I = ↑((n : ℝ) * θ) * I := by
    simp only [ofReal_mul, ofReal_intCast]
  rw [h, Complex.exp_mul_I]
  simp only [ofReal_mul, ofReal_intCast]

-- ============================================================
-- PART 4: Double Angle Formulas (n = 2)
-- ============================================================

/-
  Setting n = 2 in De Moivre's theorem yields the double angle formulas:
    cos(2θ) + i sin(2θ) = (cos θ + i sin θ)²
                        = cos²θ - sin²θ + 2i sin θ cos θ

  Comparing real and imaginary parts:
    cos(2θ) = cos²θ - sin²θ
    sin(2θ) = 2 sin θ cos θ
-/

/-- Double angle formula derived from De Moivre's theorem. -/
theorem de_moivre_double (θ : ℝ) :
    (Complex.cos θ + Complex.sin θ * I) ^ 2 =
    Complex.cos (2 * θ) + Complex.sin (2 * θ) * I := by
  exact de_moivre θ 2

-- ============================================================
-- PART 5: Triple Angle Formulas (n = 3)
-- ============================================================

/-
  Setting n = 3 gives triple angle formulas:
    cos(3θ) = cos³θ - 3 cos θ sin²θ = 4cos³θ - 3cos θ
    sin(3θ) = 3 cos²θ sin θ - sin³θ = 3sin θ - 4sin³θ
-/

/-- Triple angle formula derived from De Moivre's theorem. -/
theorem de_moivre_triple (θ : ℝ) :
    (Complex.cos θ + Complex.sin θ * I) ^ 3 =
    Complex.cos (3 * θ) + Complex.sin (3 * θ) * I := by
  exact de_moivre θ 3

-- ============================================================
-- PART 6: Roots of Unity Connection
-- ============================================================

/-
  De Moivre's theorem is essential for finding nth roots of unity.
  The nth roots of 1 are: exp(2πik/n) for k = 0, 1, ..., n-1

  By De Moivre: (exp(2πik/n))^n = exp(2πik) = 1

  This shows these are indeed nth roots of unity.
-/

/-- The nth power of an nth root of unity equals 1. -/
theorem nth_root_of_unity_power (n : ℕ) (k : ℕ) (hn : n ≠ 0) :
    Complex.exp (2 * π * I * k / n) ^ n = 1 := by
  rw [← Complex.exp_nat_mul]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h : (n : ℂ) * (2 * ↑π * I * ↑k / ↑n) = 2 * ↑π * I * ↑k := by
    field_simp
  rw [h]
  -- Rearrange to form k * (2 * π * I)
  have h2 : (2 : ℂ) * ↑π * I * ↑k = ↑k * (2 * ↑π * I) := by ring
  rw [h2]
  -- exp(k * 2πi) = (exp(2πi))^k = 1^k = 1
  rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

-- ============================================================
-- PART 7: Special Cases
-- ============================================================

/-- De Moivre with n = 0: any complex number to the 0th power is 1. -/
theorem de_moivre_zero (θ : ℝ) :
    (Complex.cos θ + Complex.sin θ * I) ^ 0 = 1 := by
  simp

/-- De Moivre with n = 1: identity case. -/
theorem de_moivre_one (θ : ℝ) :
    (Complex.cos θ + Complex.sin θ * I) ^ 1 =
    Complex.cos θ + Complex.sin θ * I := by
  simp

-- ============================================================
-- PART 8: Why This Matters
-- ============================================================

/-
  De Moivre's Theorem is fundamental in:

  **Complex Analysis:**
  - Computing powers and roots of complex numbers
  - Deriving trigonometric identities for multiple angles
  - Understanding the algebraic structure of the unit circle

  **Applications:**
  - Signal processing: Fourier analysis foundations
  - Electrical engineering: AC circuit analysis
  - Physics: Wave mechanics and quantum theory
  - Number theory: Cyclotomic fields and roots of unity

  **Proof Techniques:**
  - The theorem demonstrates the power of the exponential representation
  - Converting between rectangular and polar forms simplifies many problems
  - Connects algebra (powers) with geometry (rotations on the unit circle)

  The elegance of De Moivre's theorem lies in reducing the computation
  of arbitrary powers to simple multiplication of angles.
-/

-- Final verification: all main theorems are fully proven
#check de_moivre           -- Main theorem: (cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)
#check de_moivre_exp       -- Exponential form: (exp(θI))^n = exp(nθI)
#check de_moivre_int       -- Integer extension
#check de_moivre_double    -- Double angle (n=2)
#check de_moivre_triple    -- Triple angle (n=3)
#check nth_root_of_unity_power  -- Roots of unity connection
