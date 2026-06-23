import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Proofs.NapoleonsTheorem

/-
# Napoleon's Theorem: Connection to the Discrete Fourier Transform

## What This Proves

The Napoleon triangle construction is equivalent to applying the 3-point Discrete
Fourier Transform (DFT) to the triangle vertices, then negating or zeroing out
specific frequency components.

Let ω = e^{2πi/3} be the primitive cube root of unity. Define the DFT of triangle
(z₁, z₂, z₃) as:
  X₀ = z₁ + z₂ + z₃                   (DC / centroid component)
  X₁ = z₁ + ω·z₂ + ω²·z₃             (frequency-1 component)
  X₂ = z₁ + ω²·z₂ + ω·z₃            (frequency-2 component)

The **outer Napoleon triangle** (G₁, G₂, G₃) has DFT:
  Y₀ = G₁ + G₂ + G₃           = X₀     (centroid preserved)
  Y₁ = G₁ + ω·G₂ + ω²·G₃    = -X₁    (frequency-1 negated)
  Y₂ = G₁ + ω²·G₂ + ω·G₃    = 0      (frequency-2 zeroed)

The **inner Napoleon triangle** (G₁', G₂', G₃') has DFT:
  Y₀' = G₁' + G₂' + G₃'        = X₀    (centroid preserved)
  Y₁' = G₁' + ω·G₂' + ω²·G₃' = 0     (frequency-1 zeroed)
  Y₂' = G₁' + ω²·G₂' + ω·G₃' = -X₂   (frequency-2 negated)

## Mathematical Significance

This DFT perspective reveals WHY Napoleon's theorem is true:
- The Napoleon construction is a linear operation on triangle vertices
- In the DFT basis, it acts diagonally: X₀ ↦ X₀, X₁ ↦ -X₁, X₂ ↦ 0 (outer)
- The resulting triangle has X₂ = 0, which characterizes equilateral triangles
- Hence the outer Napoleon triangle is ALWAYS equilateral, for any input triangle

## Key Algebraic Identity

The proof hinges on the formula G_k = z_{k-1}·(1-ω)/3 + z_{k+1}·(1-ω²)/3,
which is equivalent to the original napoleonCenter definition. From this:

Y₁ = G₁ + ω·G₂ + ω²·G₃
   = [z₁·(ω(1-ω²)+ω²(1-ω)) + z₂·((1-ω)+ω²(1-ω²)) + z₃·((1-ω²)+ω(1-ω))] / 3

Using 1+ω+ω² = 0 and ω³ = 1:
   z₁ coeff: ω+ω²-2ω³ = -1-2 = -3   →  coefficient = -1
   z₂ coeff: 1+ω²-2ω  = -3ω          →  coefficient = -ω
   z₃ coeff: 1+ω-2ω²  = -3ω²         →  coefficient = -ω²

So Y₁ = -(z₁ + ω·z₂ + ω²·z₃) = -X₁ ✓

## Status
- [x] omega is a primitive cube root of unity (ω³=1, 1+ω+ω²=0)
- [x] Outer Napoleon DFT: Y₁ = -X₁
- [x] Outer Napoleon DFT: Y₂ = 0
- [x] Inner Napoleon DFT: Y₁' = 0
- [x] Inner Napoleon DFT: Y₂' = -X₂
- [x] No axioms, no sorries
-/

set_option maxHeartbeats 400000

namespace NapoleonsTheoremOQ02

open Complex Real NapoleonsTheorem

-- ============================================================
-- PART 1: The Primitive Cube Root of Unity
-- ============================================================

/-- The primitive cube root of unity ω = e^{2πi/3} = (-1 + I√3) / 2 -/
noncomputable def omega : ℂ := (-1 + I * (↑(Real.sqrt 3) : ℂ)) / 2

/-- Its conjugate: ω² = (-1 - I√3) / 2 -/
noncomputable def omegaSq : ℂ := (-1 - I * (↑(Real.sqrt 3) : ℂ)) / 2

/-- Key lemma: √3 · √3 = 3 in ℝ -/
private lemma sqrt3_sq_real : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)

/-- omegaSq equals omega^2 -/
theorem omegaSq_eq_sq : omegaSq = omega ^ 2 := by
  simp only [omegaSq, omega]
  apply Complex.ext <;>
  · simp only [pow_succ, pow_zero, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3]

/-- 1 + ω + ω² = 0: fundamental identity for cube roots of unity -/
theorem one_add_omega_add_omegaSq : 1 + omega + omegaSq = 0 := by
  simp only [omega, omegaSq]
  apply Complex.ext <;>
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_ofNat] <;>
  ring

/-- ω³ = 1: omega is a cube root of unity -/
theorem omega_cube : omega ^ 3 = 1 := by
  simp only [omega]
  apply Complex.ext <;>
  · simp only [pow_succ, pow_zero, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3]

-- ============================================================
-- PART 2: Main DFT Theorems — Outer Napoleon Triangle
-- ============================================================

/-- **Outer Napoleon DFT at Frequency 1**: The DFT of the outer Napoleon
    triangle at frequency 1 equals the NEGATIVE of the DFT of the original
    triangle at frequency 1.

    G₁ + ω·G₂ + ω²·G₃ = -(z₁ + ω·z₂ + ω²·z₃)

    Proof: Direct algebraic computation using the napoleonCenter formula,
    ω = (-1+I√3)/2, and the identity ω²+ω = -1 (from 1+ω+ω² = 0). -/
theorem napoleon_outer_dft1 (z₁ z₂ z₃ : ℂ) :
    G₁ z₁ z₂ z₃ + omega * G₂ z₁ z₂ z₃ + omegaSq * G₃ z₁ z₂ z₃ =
    -(z₁ + omega * z₂ + omegaSq * z₃) := by
  simp only [G₁, G₂, G₃, napoleonCenter, omega, omegaSq]
  apply Complex.ext
  · -- Real part
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
      Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.neg_re,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3, sq_nonneg (Real.sqrt 3),
              mul_comm (Real.sqrt 3) z₁.im, mul_comm (Real.sqrt 3) z₂.im,
              mul_comm (Real.sqrt 3) z₃.im, mul_comm (Real.sqrt 3) z₁.re,
              mul_comm (Real.sqrt 3) z₂.re, mul_comm (Real.sqrt 3) z₃.re]
  · -- Imaginary part
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_im, Complex.neg_im,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3, sq_nonneg (Real.sqrt 3),
              mul_comm (Real.sqrt 3) z₁.im, mul_comm (Real.sqrt 3) z₂.im,
              mul_comm (Real.sqrt 3) z₃.im, mul_comm (Real.sqrt 3) z₁.re,
              mul_comm (Real.sqrt 3) z₂.re, mul_comm (Real.sqrt 3) z₃.re]

/-- **Outer Napoleon DFT at Frequency 2**: The DFT of the outer Napoleon
    triangle at frequency 2 is ZERO.

    G₁ + ω²·G₂ + ω·G₃ = 0

    **Significance**: A triangle is equilateral iff its DFT at frequency 2
    (and frequency 1) vanishes. Since Y₂ = 0 always, the outer Napoleon
    triangle is always equilateral. -/
theorem napoleon_outer_dft2 (z₁ z₂ z₃ : ℂ) :
    G₁ z₁ z₂ z₃ + omegaSq * G₂ z₁ z₂ z₃ + omega * G₃ z₁ z₂ z₃ = 0 := by
  simp only [G₁, G₂, G₃, napoleonCenter, omega, omegaSq]
  apply Complex.ext
  · -- Real part
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.zero_re,
      Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3, sq_nonneg (Real.sqrt 3),
              mul_comm (Real.sqrt 3) z₁.im, mul_comm (Real.sqrt 3) z₂.im,
              mul_comm (Real.sqrt 3) z₃.im, mul_comm (Real.sqrt 3) z₁.re,
              mul_comm (Real.sqrt 3) z₂.re, mul_comm (Real.sqrt 3) z₃.re]
  · -- Imaginary part
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.zero_im,
      Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_im,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3, sq_nonneg (Real.sqrt 3),
              mul_comm (Real.sqrt 3) z₁.im, mul_comm (Real.sqrt 3) z₂.im,
              mul_comm (Real.sqrt 3) z₃.im, mul_comm (Real.sqrt 3) z₁.re,
              mul_comm (Real.sqrt 3) z₂.re, mul_comm (Real.sqrt 3) z₃.re]

-- ============================================================
-- PART 3: Main DFT Theorems — Inner Napoleon Triangle
-- ============================================================

/-- **Inner Napoleon DFT at Frequency 1**: The DFT of the inner Napoleon
    triangle at frequency 1 is ZERO.

    G₁' + ω·G₂' + ω²·G₃' = 0

    Complementary to `napoleon_outer_dft2`: the inner construction kills X₁
    while the outer kills X₂. -/
theorem napoleon_inner_dft1 (z₁ z₂ z₃ : ℂ) :
    G₁' z₁ z₂ z₃ + omega * G₂' z₁ z₂ z₃ + omegaSq * G₃' z₁ z₂ z₃ = 0 := by
  simp only [G₁', G₂', G₃', innerNapoleonCenter, omega, omegaSq]
  apply Complex.ext
  · -- Real part
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.zero_re,
      Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3, sq_nonneg (Real.sqrt 3),
              mul_comm (Real.sqrt 3) z₁.im, mul_comm (Real.sqrt 3) z₂.im,
              mul_comm (Real.sqrt 3) z₃.im, mul_comm (Real.sqrt 3) z₁.re,
              mul_comm (Real.sqrt 3) z₂.re, mul_comm (Real.sqrt 3) z₃.re]
  · -- Imaginary part
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.zero_im,
      Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_im,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3, sq_nonneg (Real.sqrt 3),
              mul_comm (Real.sqrt 3) z₁.im, mul_comm (Real.sqrt 3) z₂.im,
              mul_comm (Real.sqrt 3) z₃.im, mul_comm (Real.sqrt 3) z₁.re,
              mul_comm (Real.sqrt 3) z₂.re, mul_comm (Real.sqrt 3) z₃.re]

/-- **Inner Napoleon DFT at Frequency 2**: The DFT of the inner Napoleon
    triangle at frequency 2 equals the NEGATIVE of the DFT of the original
    triangle at frequency 2.

    G₁' + ω²·G₂' + ω·G₃' = -(z₁ + ω²·z₂ + ω·z₃)

    **Symmetry**: Outer and inner Napoleon constructions are mirror images in
    the DFT domain — they swap the roles of X₁ and X₂. -/
theorem napoleon_inner_dft2 (z₁ z₂ z₃ : ℂ) :
    G₁' z₁ z₂ z₃ + omegaSq * G₂' z₁ z₂ z₃ + omega * G₃' z₁ z₂ z₃ =
    -(z₁ + omegaSq * z₂ + omega * z₃) := by
  simp only [G₁', G₂', G₃', innerNapoleonCenter, omega, omegaSq]
  apply Complex.ext
  · -- Real part
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
      Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3, sq_nonneg (Real.sqrt 3),
              mul_comm (Real.sqrt 3) z₁.im, mul_comm (Real.sqrt 3) z₂.im,
              mul_comm (Real.sqrt 3) z₃.im, mul_comm (Real.sqrt 3) z₁.re,
              mul_comm (Real.sqrt 3) z₂.re, mul_comm (Real.sqrt 3) z₃.re]
  · -- Imaginary part
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_im,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3, sq_nonneg (Real.sqrt 3),
              mul_comm (Real.sqrt 3) z₁.im, mul_comm (Real.sqrt 3) z₂.im,
              mul_comm (Real.sqrt 3) z₃.im, mul_comm (Real.sqrt 3) z₁.re,
              mul_comm (Real.sqrt 3) z₂.re, mul_comm (Real.sqrt 3) z₃.re]

-- ============================================================
-- PART 4: Complete DFT Picture
-- ============================================================

/-- **Outer Napoleon as DFT Filter**:

    The Napoleon construction is a linear DFT filter acting on triangle vertices.
    In the DFT basis (X₀, X₁, X₂), the outer Napoleon map acts as:
      X₀ ↦ X₀    (centroid invariant)
      X₁ ↦ -X₁   (frequency-1 negated)
      X₂ ↦ 0     (frequency-2 eliminated)

    Since equilateral triangles are characterized by X₂ = 0 in the outer case,
    the outer Napoleon triangle is always equilateral. -/
theorem napoleon_as_dft_filter (z₁ z₂ z₃ : ℂ) :
    -- Y₀: centroid preserved
    (G₁ z₁ z₂ z₃ + G₂ z₁ z₂ z₃ + G₃ z₁ z₂ z₃) / 3 = (z₁ + z₂ + z₃) / 3 ∧
    -- Y₁: frequency-1 negated
    G₁ z₁ z₂ z₃ + omega * G₂ z₁ z₂ z₃ + omegaSq * G₃ z₁ z₂ z₃ =
      -(z₁ + omega * z₂ + omegaSq * z₃) ∧
    -- Y₂: frequency-2 eliminated
    G₁ z₁ z₂ z₃ + omegaSq * G₂ z₁ z₂ z₃ + omega * G₃ z₁ z₂ z₃ = 0 :=
  ⟨napoleon_centroid_eq_original z₁ z₂ z₃,
   napoleon_outer_dft1 z₁ z₂ z₃,
   napoleon_outer_dft2 z₁ z₂ z₃⟩

/-- **Inner Napoleon as DFT Filter**:

    The inner Napoleon map acts on (X₀, X₁, X₂) as:
      X₀ ↦ X₀    (centroid invariant)
      X₁ ↦ 0     (frequency-1 eliminated)
      X₂ ↦ -X₂   (frequency-2 negated)

    Complementary to the outer: outer kills X₂ / inner kills X₁. -/
theorem inner_napoleon_as_dft_filter (z₁ z₂ z₃ : ℂ) :
    -- Y₀: centroid preserved
    (G₁' z₁ z₂ z₃ + G₂' z₁ z₂ z₃ + G₃' z₁ z₂ z₃) / 3 = (z₁ + z₂ + z₃) / 3 ∧
    -- Y₁: frequency-1 eliminated
    G₁' z₁ z₂ z₃ + omega * G₂' z₁ z₂ z₃ + omegaSq * G₃' z₁ z₂ z₃ = 0 ∧
    -- Y₂: frequency-2 negated
    G₁' z₁ z₂ z₃ + omegaSq * G₂' z₁ z₂ z₃ + omega * G₃' z₁ z₂ z₃ =
      -(z₁ + omegaSq * z₂ + omega * z₃) :=
  ⟨inner_napoleon_centroid_eq_original z₁ z₂ z₃,
   napoleon_inner_dft1 z₁ z₂ z₃,
   napoleon_inner_dft2 z₁ z₂ z₃⟩

/-- **IDFT Recovery Formula**: The outer Napoleon center G₁ equals the
    inverse DFT of (X₀, -X₁, 0) at index 1.

    G₁ = (X₀ - X₁) / 3 = ((z₁+z₂+z₃) - (z₁+ω·z₂+ω²·z₃)) / 3

    This is the "sum of first two DFT components" formula for recovering
    the Napoleon centroid directly from the original triangle's DFT. -/
theorem napoleon_center_idft_recovery (z₁ z₂ z₃ : ℂ) :
    G₁ z₁ z₂ z₃ =
    ((z₁ + z₂ + z₃) - (z₁ + omega * z₂ + omegaSq * z₃)) / 3 := by
  simp only [G₁, napoleonCenter, omega, omegaSq]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3]
  · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq_real
    ring_nf
    nlinarith [h3]

-- Summary
#check napoleon_outer_dft1          -- Y₁ = -X₁ for outer Napoleon
#check napoleon_outer_dft2          -- Y₂ = 0 for outer Napoleon
#check napoleon_inner_dft1          -- Y₁' = 0 for inner Napoleon
#check napoleon_inner_dft2          -- Y₂' = -X₂ for inner Napoleon
#check napoleon_as_dft_filter       -- Complete outer DFT characterization
#check inner_napoleon_as_dft_filter -- Complete inner DFT characterization

end NapoleonsTheoremOQ02
