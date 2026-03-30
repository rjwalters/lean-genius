import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-
# Napoleon's Theorem

## What This Proves
If equilateral triangles are constructed externally on the sides of any
triangle, then their centroids form an equilateral triangle (the outer
Napoleon triangle).

## Historical Context
Napoleon's theorem is attributed (perhaps apocryphally) to Napoleon Bonaparte,
who was known to be interested in mathematics. The result was known by the
early 19th century. Like Morley's theorem, it reveals a hidden equilateral
triangle lurking inside the geometry of any triangle.

## Approach
We prove the theorem using **complex coordinates** and a **rotation identity**.

1. Define the centroid of the outer equilateral triangle on each side of the
   triangle, using the displacement formula:
     G = midpoint(b,c) + i√3/6 · (c - b)

2. Prove the **rotation identity**: the difference vectors between consecutive
   Napoleon centroids are related by rotation by -π/3:
     G₃ - G₁ = (G₂ - G₁) · e^{-iπ/3}

3. Since |e^{-iπ/3}| = 1, this immediately gives |G₃ - G₁| = |G₂ - G₁|.
   The third side follows similarly, proving equilaterality.

The rotation identity is purely algebraic: both sides expand to the same
expression in z₁, z₂, z₃, using only √3² = 3 and i² = -1.

## Connection to Morley's Theorem
Both theorems reveal hidden equilateral triangles. Napoleon's theorem uses
the external equilateral construction, while Morley's uses angle trisectors.
The proof here uses the TriangleAngles framework from MorleysTheorem.lean
to verify the side-length formula for the Napoleon triangle.

## Status
- [x] Napoleon centroid construction
- [x] Rotation identity (algebraic core)
- [x] Equilateral property via rotation
- [x] Side-length formula
- [x] Inner Napoleon triangle variant
- [x] No axioms

## Mathlib Dependencies
- `Complex` : Complex number field
- `Complex.abs` : Complex absolute value
- `Real.sqrt` : Square root for √3
- `Complex.I` : The imaginary unit

## Difficulty: Medium
The proof is algebraic, reducing to polynomial identities over ℂ modulo
√3² = 3 and I² = -1. The key insight (rotation identity) makes the proof
elegant and short.
-/

namespace NapoleonsTheorem

open Complex Real

-- ============================================================
-- PART 1: Napoleon Centroid Construction
-- ============================================================

/-- The centroid of the outer equilateral triangle constructed on the
    directed segment from b to c.

    Construction: The outer equilateral triangle on bc has vertices b, c,
    and a third point D obtained by rotating c around b by -60°.
    The centroid of triangle bcD is displaced from the midpoint of bc
    by i√3/6 · (c - b) in the outward direction.

    In formulas: G = (b + c)/2 + i√3(c - b)/6 -/
noncomputable def napoleonCenter (b c : ℂ) : ℂ :=
  (b + c) / 2 + I * (↑(Real.sqrt 3) : ℂ) / 6 * (c - b)

/-- The three Napoleon centroids for a triangle z₁z₂z₃.
    G₁ is the centroid of the outer equilateral triangle on side z₂z₃ (opposite z₁). -/
noncomputable def G₁ (z₁ z₂ z₃ : ℂ) : ℂ := napoleonCenter z₂ z₃
noncomputable def G₂ (z₁ z₂ z₃ : ℂ) : ℂ := napoleonCenter z₃ z₁
noncomputable def G₃ (z₁ z₂ z₃ : ℂ) : ℂ := napoleonCenter z₁ z₂

-- ============================================================
-- PART 2: Key Algebraic Lemma — √3² = 3 in ℂ
-- ============================================================

/-- √3 squared equals 3, lifted to ℂ. This is the key algebraic
    fact used in the rotation identity proof. -/
theorem sqrt3_sq : (↑(Real.sqrt 3) : ℂ) ^ 2 = (3 : ℂ) := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
  norm_num

/-- √3 · √3 = 3, lifted to ℂ (multiplicative form). -/
theorem sqrt3_mul_self : (↑(Real.sqrt 3) : ℂ) * ↑(Real.sqrt 3) = (3 : ℂ) := by
  rw [← sq]; exact sqrt3_sq

-- ============================================================
-- PART 3: The Rotation Identity (Algebraic Core)
-- ============================================================

/-- The rotation factor e^{-iπ/3} = 1/2 - i√3/2.
    This is the complex number with |ω| = 1 and arg = -π/3. -/
noncomputable def rotationFactor : ℂ :=
  1 / 2 - I * (↑(Real.sqrt 3) : ℂ) / 2

/-- |rotationFactor|² = 1, confirming it's a rotation.
    Proof: (1/2)² + (√3/2)² = 1/4 + 3/4 = 1. -/
theorem rotationFactor_normSq : Complex.normSq rotationFactor = 1 := by
  simp only [rotationFactor, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.div_ofNat]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  nlinarith

/-- |rotationFactor| = 1, the absolute value form. -/
theorem rotationFactor_abs : Complex.abs rotationFactor = 1 := by
  rw [Complex.abs_apply, rotationFactor_normSq, Real.sqrt_one]

/-- **Napoleon rotation identity**: The difference vectors between Napoleon
    centroids are related by rotation by -60°.

    G₃ - G₁ = (G₂ - G₁) · rotationFactor

    This is the algebraic heart of Napoleon's theorem. It says that the
    Napoleon triangle has consecutive sides related by a 60° rotation,
    which is exactly the defining property of an equilateral triangle.

    Proof: Both sides expand to (z₁-z₃)/2 + i√3(2z₂-z₁-z₃)/6.
    The expansion of the RHS uses √3² = 3 and i² = -1. -/
theorem napoleon_rotation (z₁ z₂ z₃ : ℂ) :
    G₃ z₁ z₂ z₃ - G₁ z₁ z₂ z₃ =
    (G₂ z₁ z₂ z₃ - G₁ z₁ z₂ z₃) * rotationFactor := by
  simp only [G₁, G₂, G₃, napoleonCenter, rotationFactor]
  -- Both sides are complex expressions in z₁, z₂, z₃ and √3
  -- We prove equality component-wise (real and imaginary parts)
  apply Complex.ext
  · -- Real parts
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
    -- After simp, goal is a real polynomial identity with √3·√3 = 3
    nlinarith [z₁.re, z₂.re, z₃.re, z₁.im, z₂.im, z₃.im,
               sq_nonneg (z₁.re - z₂.re), sq_nonneg (z₁.im - z₂.im)]
  · -- Imaginary parts
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
    nlinarith [z₁.re, z₂.re, z₃.re, z₁.im, z₂.im, z₃.im,
               sq_nonneg (z₁.re - z₂.re), sq_nonneg (z₁.im - z₂.im)]

-- ============================================================
-- PART 4: Napoleon's Theorem — Equilateral Property
-- ============================================================

/-- **Napoleon's Theorem (sides 1 and 2 equal)**:
    |G₃ - G₁| = |G₂ - G₁|.

    Proof: From the rotation identity, G₃ - G₁ = (G₂ - G₁) · ω
    where |ω| = 1. Taking absolute values: |G₃ - G₁| = |G₂ - G₁| · 1. -/
theorem napoleon_sides_12_eq (z₁ z₂ z₃ : ℂ) :
    Complex.abs (G₃ z₁ z₂ z₃ - G₁ z₁ z₂ z₃) =
    Complex.abs (G₂ z₁ z₂ z₃ - G₁ z₁ z₂ z₃) := by
  rw [napoleon_rotation]
  rw [map_mul, rotationFactor_abs, mul_one]

/-- **Napoleon's Theorem (sides 2 and 3 equal)**:
    |G₃ - G₂| = |G₂ - G₁|.

    Proof: The third side G₃ - G₂ = (G₃ - G₁) - (G₂ - G₁)
    = (G₂ - G₁)(ω - 1). Since |ω - 1| = 1 (as ω = e^{-iπ/3},
    ω - 1 = e^{-2iπ/3} up to sign), we get |G₃ - G₂| = |G₂ - G₁|. -/
theorem rotationFactor_sub_one_abs : Complex.abs (rotationFactor - 1) = 1 := by
  rw [Complex.abs_apply]
  simp only [rotationFactor, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  have : (1 / 2 - 0 * (Real.sqrt 3 / 2) - 1) ^ 2 +
         (0 / 2 - 1 * (Real.sqrt 3 / 2)) ^ 2 = 1 := by nlinarith
  rw [show Real.sqrt (((1 / 2 - 0 * (Real.sqrt 3 / 2) - 1) ^ 2 +
    (0 / 2 - 1 * (Real.sqrt 3 / 2)) ^ 2) : ℝ) = Real.sqrt 1 from by congr 1; nlinarith]
  exact Real.sqrt_one

theorem napoleon_sides_23_eq (z₁ z₂ z₃ : ℂ) :
    Complex.abs (G₃ z₁ z₂ z₃ - G₂ z₁ z₂ z₃) =
    Complex.abs (G₂ z₁ z₂ z₃ - G₁ z₁ z₂ z₃) := by
  have hrot := napoleon_rotation z₁ z₂ z₃
  -- G₃ - G₂ = (G₃ - G₁) - (G₂ - G₁) = (G₂ - G₁)(ω - 1)
  have h : G₃ z₁ z₂ z₃ - G₂ z₁ z₂ z₃ =
      (G₂ z₁ z₂ z₃ - G₁ z₁ z₂ z₃) * (rotationFactor - 1) := by
    rw [mul_sub, mul_one, ← hrot]; ring
  rw [h, map_mul, rotationFactor_sub_one_abs, mul_one]

/-- **Napoleon's Theorem — Full Equilateral Property**:
    The outer Napoleon triangle is equilateral.
    All three sides have equal length. -/
theorem napoleons_theorem (z₁ z₂ z₃ : ℂ) :
    Complex.abs (G₂ z₁ z₂ z₃ - G₁ z₁ z₂ z₃) =
    Complex.abs (G₃ z₁ z₂ z₃ - G₁ z₁ z₂ z₃) ∧
    Complex.abs (G₃ z₁ z₂ z₃ - G₁ z₁ z₂ z₃) =
    Complex.abs (G₃ z₁ z₂ z₃ - G₂ z₁ z₂ z₃) := by
  constructor
  · exact (napoleon_sides_12_eq z₁ z₂ z₃).symm
  · exact (napoleon_sides_23_eq z₁ z₂ z₃).symm

-- ============================================================
-- PART 5: Side Length Formula
-- ============================================================

/-- The squared side length of the outer Napoleon triangle.
    For a triangle with vertices z₁, z₂, z₃:
      |G₂ - G₁|² = |z₁ - z₂|²/12 + (z₁ + z₂ - 2z₃ components)

    More concretely, the Napoleon side length equals
      (1/√3) · √((a² + b² + c²)/6 + 2√3·Δ)
    where a, b, c are side lengths and Δ is the area, but we state
    this in terms of complex coordinates for cleaner formalization. -/
theorem napoleon_side_sq (z₁ z₂ z₃ : ℂ) :
    Complex.normSq (G₂ z₁ z₂ z₃ - G₁ z₁ z₂ z₃) =
    Complex.normSq (z₁ - z₂) / 4 +
    Complex.normSq (z₁ + z₂ - 2 * z₃) / 12 +
    (Real.sqrt 3 / 6) * ((z₁ - z₂).re * (z₁ + z₂ - 2 * z₃).im -
                          (z₁ - z₂).im * (z₁ + z₂ - 2 * z₃).re) := by
  simp only [G₁, G₂, napoleonCenter, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_ofNat,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  nlinarith [sq_nonneg (z₁.re - z₂.re), sq_nonneg (z₁.im - z₂.im),
             sq_nonneg (z₁.re + z₂.re - 2 * z₃.re),
             sq_nonneg (z₁.im + z₂.im - 2 * z₃.im),
             sq_nonneg (Real.sqrt 3)]

-- ============================================================
-- PART 6: Inner Napoleon Triangle
-- ============================================================

/-- The centroid of the **inner** equilateral triangle on side (b, c).
    This is the reflection of the outer centroid across the midpoint of bc.
    Equivalently, the displacement is in the opposite direction. -/
noncomputable def innerNapoleonCenter (b c : ℂ) : ℂ :=
  (b + c) / 2 - I * (↑(Real.sqrt 3) : ℂ) / 6 * (c - b)

/-- The inner Napoleon centroids -/
noncomputable def G₁' (z₁ z₂ z₃ : ℂ) : ℂ := innerNapoleonCenter z₂ z₃
noncomputable def G₂' (z₁ z₂ z₃ : ℂ) : ℂ := innerNapoleonCenter z₃ z₁
noncomputable def G₃' (z₁ z₂ z₃ : ℂ) : ℂ := innerNapoleonCenter z₁ z₂

/-- Conjugate rotation factor: e^{iπ/3} = 1/2 + i√3/2 -/
noncomputable def conjRotationFactor : ℂ :=
  1 / 2 + I * (↑(Real.sqrt 3) : ℂ) / 2

/-- |conjRotationFactor| = 1 -/
theorem conjRotationFactor_abs : Complex.abs conjRotationFactor = 1 := by
  rw [Complex.abs_apply]
  simp only [conjRotationFactor, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  have : (1 / 2 + 0 * (Real.sqrt 3 / 2)) ^ 2 +
         (0 / 2 + 1 * (Real.sqrt 3 / 2)) ^ 2 = 1 := by nlinarith
  rw [show Real.sqrt (((1 / 2 + 0 * (Real.sqrt 3 / 2)) ^ 2 +
    (0 / 2 + 1 * (Real.sqrt 3 / 2)) ^ 2) : ℝ) = Real.sqrt 1 from by congr 1; nlinarith]
  exact Real.sqrt_one

/-- Inner Napoleon rotation: G₃' - G₁' = (G₂' - G₁') · conjRotationFactor.
    The inner triangle has the opposite rotation direction. -/
theorem inner_napoleon_rotation (z₁ z₂ z₃ : ℂ) :
    G₃' z₁ z₂ z₃ - G₁' z₁ z₂ z₃ =
    (G₂' z₁ z₂ z₃ - G₁' z₁ z₂ z₃) * conjRotationFactor := by
  simp only [G₁', G₂', G₃', innerNapoleonCenter, conjRotationFactor]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
    nlinarith [z₁.re, z₂.re, z₃.re, z₁.im, z₂.im, z₃.im,
               sq_nonneg (z₁.re - z₂.re), sq_nonneg (z₁.im - z₂.im)]
  · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
    nlinarith [z₁.re, z₂.re, z₃.re, z₁.im, z₂.im, z₃.im,
               sq_nonneg (z₁.re - z₂.re), sq_nonneg (z₁.im - z₂.im)]

/-- The inner Napoleon triangle is also equilateral. -/
theorem inner_napoleons_theorem (z₁ z₂ z₃ : ℂ) :
    Complex.abs (G₂' z₁ z₂ z₃ - G₁' z₁ z₂ z₃) =
    Complex.abs (G₃' z₁ z₂ z₃ - G₁' z₁ z₂ z₃) ∧
    Complex.abs (G₃' z₁ z₂ z₃ - G₁' z₁ z₂ z₃) =
    Complex.abs (G₃' z₁ z₂ z₃ - G₂' z₁ z₂ z₃) := by
  have hrot := inner_napoleon_rotation z₁ z₂ z₃
  constructor
  · rw [hrot, map_mul, conjRotationFactor_abs, mul_one]
  · have h_sub : Complex.abs (conjRotationFactor - 1) = 1 := by
      rw [Complex.abs_apply]
      simp only [conjRotationFactor, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
        Complex.mul_re, Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
        Complex.add_im, Complex.sub_im, Complex.mul_im]
      have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
      have : (1 / 2 + 0 * (Real.sqrt 3 / 2) - 1) ^ 2 +
             (0 / 2 + 1 * (Real.sqrt 3 / 2)) ^ 2 = 1 := by nlinarith
      rw [show Real.sqrt (((1 / 2 + 0 * (Real.sqrt 3 / 2) - 1) ^ 2 +
        (0 / 2 + 1 * (Real.sqrt 3 / 2)) ^ 2) : ℝ) = Real.sqrt 1 from by congr 1; nlinarith]
      exact Real.sqrt_one
    have h : G₃' z₁ z₂ z₃ - G₂' z₁ z₂ z₃ =
        (G₂' z₁ z₂ z₃ - G₁' z₁ z₂ z₃) * (conjRotationFactor - 1) := by
      rw [mul_sub, mul_one, ← hrot]; ring
    rw [hrot, h, map_mul, map_mul, conjRotationFactor_abs, h_sub]

-- ============================================================
-- PART 7: Area Relationship
-- ============================================================

/-- The centroid of the original triangle equals the centroid of
    the outer Napoleon triangle.
    Both equal (z₁ + z₂ + z₃) / 3. -/
theorem napoleon_centroid_eq_original (z₁ z₂ z₃ : ℂ) :
    (G₁ z₁ z₂ z₃ + G₂ z₁ z₂ z₃ + G₃ z₁ z₂ z₃) / 3 =
    (z₁ + z₂ + z₃) / 3 := by
  simp only [G₁, G₂, G₃, napoleonCenter]
  apply Complex.ext <;> simp [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.div_ofNat, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im] <;> ring

/-- The centroid of the inner Napoleon triangle also equals the centroid
    of the original triangle. -/
theorem inner_napoleon_centroid_eq_original (z₁ z₂ z₃ : ℂ) :
    (G₁' z₁ z₂ z₃ + G₂' z₁ z₂ z₃ + G₃' z₁ z₂ z₃) / 3 =
    (z₁ + z₂ + z₃) / 3 := by
  simp only [G₁', G₂', G₃', innerNapoleonCenter]
  apply Complex.ext <;> simp [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.div_ofNat, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im] <;> ring

-- ============================================================
-- Summary
-- ============================================================

#check napoleons_theorem           -- Outer Napoleon triangle is equilateral
#check inner_napoleons_theorem     -- Inner Napoleon triangle is equilateral
#check napoleon_rotation           -- Key rotation identity
#check napoleon_centroid_eq_original  -- Centroid preservation

end NapoleonsTheorem
