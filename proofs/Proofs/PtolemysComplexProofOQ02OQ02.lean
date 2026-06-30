/-
# Ptolemy → Chord/Radius-r Generalization + Law of Cosines (OQ02-OQ02)

## What This Proves

The parent entry (`PtolemysComplexProofOQ02`, "Ptolemy → sine addition formula")
works entirely on the **unit** circle: its distance lemmas all compute
`‖1 - exp(θ·i)‖`, `‖exp(α·i) - exp(β·i)‖`, etc. on radius 1.  This file lifts
that machinery to a circle of arbitrary radius `r ≥ 0` and exposes the two
classical chord identities that underlie Ptolemy's chord tables:

  * **Chord-length formula.**  For two points `z = r·exp(θ_z·i)`,
    `w = r·exp(θ_w·i)` on a circle of radius `r`,

        ‖z - w‖ = 2r · |sin((θ_z - θ_w)/2)|.

    This is the "length of a chord subtending a central angle `Δθ`" formula
    Ptolemy tabulated (his `crd Δθ = 2r·sin(Δθ/2)`).

  * **Law of cosines.**  For `z = r₁·exp(θ₁·i)`, `w = r₂·exp(θ₂·i)`,

        ‖z - w‖² = r₁² + r₂² - 2·r₁·r₂·cos(θ₁ - θ₂),

    i.e. the triangle `0, z, w` obeys `c² = a² + b² - 2ab·cos C`.

  * **Consistency.**  On one circle (`r₁ = r₂ = r`) the law of cosines and the
    chord formula agree, via the half-angle identity `1 - cos t = 2 sin²(t/2)`.

  * **Unit-circle specialization** recovers the parent's
    `‖exp(θ_z·i) - exp(θ_w·i)‖ = 2|sin((θ_z - θ_w)/2)|`.

## Status
Verified — 0 sorries, 0 axioms.
-/

import Mathlib

open Complex Real

namespace PtolemysComplexProofOQ02OQ02

/-! ## Part I. Unit-circle squared chord -/

/-- Rewrite `exp(θ·i)` for real `θ` in Cartesian form `cos θ + sin θ·i`. -/
lemma exp_ofReal_mul_I (θ : ℝ) :
    Complex.exp (↑θ * Complex.I) = ↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `‖1 - exp(θ·i)‖² = 2 - 2cos θ` (the parent's core chord identity). -/
lemma normSq_one_sub_exp (θ : ℝ) :
    ‖(1 : ℂ) - Complex.exp (↑θ * Complex.I)‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [exp_ofReal_mul_I, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
             Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
             Complex.sub_im, Complex.one_im, Complex.add_im, Complex.mul_im]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Factoring out `exp(b·i)`: `‖exp(a·i) - exp(b·i)‖ = ‖1 - exp((a-b)·i)‖`. -/
lemma norm_exp_sub_exp (a b : ℝ) :
    ‖Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I)‖
      = ‖(1 : ℂ) - Complex.exp (↑(a - b) * Complex.I)‖ := by
  have hfac : Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I)
      = Complex.exp (↑b * Complex.I) * (Complex.exp (↑(a - b) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_sub_rev]

/-! ## Part II. The half-angle identity behind chord lengths -/

/-- `2 - 2cos t = (2·sin(t/2))²` — the half-angle identity in squared-chord form. -/
lemma two_sub_two_cos (t : ℝ) :
    2 - 2 * Real.cos t = (2 * Real.sin (t / 2)) ^ 2 := by
  have k := Real.cos_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at k
  nlinarith [Real.sin_sq_add_cos_sq (t / 2), k]

/-! ## Part III. Chord-length formula on a circle of radius r -/

/-- **Chord-length formula (radius r).**  For `z = r·exp(θ_z·i)` and
    `w = r·exp(θ_w·i)` on a circle of radius `r ≥ 0`,
    `‖z - w‖ = 2r·|sin((θ_z - θ_w)/2)|`.  This is Ptolemy's `crd`. -/
theorem chord_length (r θz θw : ℝ) (hr : 0 ≤ r) :
    ‖(↑r * Complex.exp (↑θz * Complex.I)) - (↑r * Complex.exp (↑θw * Complex.I))‖
      = 2 * r * |Real.sin ((θz - θw) / 2)| := by
  have hfac : (↑r * Complex.exp (↑θz * Complex.I)) - (↑r * Complex.exp (↑θw * Complex.I))
      = (↑r : ℂ) * (Complex.exp (↑θz * Complex.I) - Complex.exp (↑θw * Complex.I)) := by
    ring
  rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
      norm_exp_sub_exp]
  -- ‖1 - exp((θz-θw)·i)‖ = 2|sin((θz-θw)/2)|
  have hchord : ‖(1 : ℂ) - Complex.exp (↑(θz - θw) * Complex.I)‖
      = 2 * |Real.sin ((θz - θw) / 2)| := by
    have hsq : ‖(1 : ℂ) - Complex.exp (↑(θz - θw) * Complex.I)‖ ^ 2
        = (2 * |Real.sin ((θz - θw) / 2)|) ^ 2 := by
      rw [normSq_one_sub_exp, two_sub_two_cos]
      simp only [mul_pow, sq_abs]
    have h1 : 0 ≤ ‖(1 : ℂ) - Complex.exp (↑(θz - θw) * Complex.I)‖ := norm_nonneg _
    have h2 : 0 ≤ 2 * |Real.sin ((θz - θw) / 2)| := by positivity
    nlinarith [hsq, h1, h2]
  rw [hchord]; ring

/-! ## Part IV. Law of cosines -/

/-- **Law of cosines.**  For `z = r₁·exp(θ₁·i)` and `w = r₂·exp(θ₂·i)`,
    `‖z - w‖² = r₁² + r₂² - 2·r₁·r₂·cos(θ₁ - θ₂)`.  The triangle `0, z, w`
    has side lengths `r₁, r₂, ‖z-w‖` and included angle `θ₁ - θ₂`. -/
theorem law_of_cosines (r1 r2 θ1 θ2 : ℝ) :
    ‖(↑r1 * Complex.exp (↑θ1 * Complex.I)) - (↑r2 * Complex.exp (↑θ2 * Complex.I))‖ ^ 2
      = r1 ^ 2 + r2 ^ 2 - 2 * r1 * r2 * Real.cos (θ1 - θ2) := by
  rw [exp_ofReal_mul_I, exp_ofReal_mul_I, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
             Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [Real.cos_sub]
  linear_combination (r1 ^ 2) * Real.sin_sq_add_cos_sq θ1
    + (r2 ^ 2) * Real.sin_sq_add_cos_sq θ2

/-! ## Part V. Consistency and unit-circle specialization -/

/-- On a single circle (`r₁ = r₂ = r`) the law of cosines reproduces the squared
    chord-length formula `‖z - w‖² = (2r·sin(Δθ/2))²`, via `1 - cos = 2sin²(·/2)`. -/
theorem law_of_cosines_eq_chord_sq (r θz θw : ℝ) :
    r ^ 2 + r ^ 2 - 2 * r * r * Real.cos (θz - θw)
      = (2 * r * |Real.sin ((θz - θw) / 2)|) ^ 2 := by
  have h := two_sub_two_cos (θz - θw)
  have hrw : (2 * r * |Real.sin ((θz - θw) / 2)|) ^ 2
      = r ^ 2 * (2 * Real.sin ((θz - θw) / 2)) ^ 2 := by
    simp only [mul_pow, sq_abs]; ring
  rw [hrw, ← h]; ring

/-- The two theorems agree on one circle: the law-of-cosines value equals the
    square of the chord length given by `chord_length`. -/
theorem consistency (r θz θw : ℝ) (hr : 0 ≤ r) :
    ‖(↑r * Complex.exp (↑θz * Complex.I)) - (↑r * Complex.exp (↑θw * Complex.I))‖ ^ 2
      = r ^ 2 + r ^ 2 - 2 * r * r * Real.cos (θz - θw) := by
  rw [chord_length r θz θw hr, law_of_cosines_eq_chord_sq r θz θw]

/-- **Unit-circle specialization** (`r = 1`) recovers the parent's chord identity
    `‖exp(θ_z·i) - exp(θ_w·i)‖ = 2|sin((θ_z - θ_w)/2)|`. -/
theorem chord_length_unit (θz θw : ℝ) :
    ‖Complex.exp (↑θz * Complex.I) - Complex.exp (↑θw * Complex.I)‖
      = 2 * |Real.sin ((θz - θw) / 2)| := by
  have h := chord_length 1 θz θw (by norm_num)
  simpa using h

/-! ## Part VI. Worked example -/

/-- A regular hexagon vertex pair: two points at central-angle `π/3` on a radius-2
    circle subtend a chord of length `2`.  `crd(π/3) = 2·2·sin(π/6) = 4·(1/2) = 2`. -/
example : ‖((2 : ℂ) * Complex.exp (↑(Real.pi / 3) * Complex.I))
            - (2 : ℂ) * Complex.exp (↑(0 : ℝ) * Complex.I)‖ = 2 := by
  have h := chord_length 2 (Real.pi / 3) 0 (by norm_num)
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num] at *
  rw [h]
  rw [show (Real.pi / 3 - 0) / 2 = Real.pi / 6 by ring, Real.sin_pi_div_six]
  norm_num

end PtolemysComplexProofOQ02OQ02
