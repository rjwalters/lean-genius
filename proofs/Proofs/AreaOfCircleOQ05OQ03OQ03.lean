/-
  The Gaussian Fourier transform: translation–modulation duality
  (area-of-circle-oq-05-oq-03-oq-03)

  Follow-up to `area-of-circle-oq-05-oq-03` ("the Gaussian is its own Fourier
  transform"), which established, axiom-free and in explicit Lebesgue form,

      ∫_ℝ e^{i t x} · e^{-x²/2} dx = e^{-t²/2} · √(2π).

  The parent fixes the *centred, unmodulated* standard Gaussian.  Here we work out
  what the Fourier transform does to the two elementary symmetries of that
  density — translation in space and modulation by a phase — and show they are
  exchanged by the transform.  This is the "shift theorem" of Fourier analysis,
  made completely explicit for the Gaussian:

    • TRANSLATION ↦ MODULATION
        ∫_ℝ e^{i t x} · e^{-(x-a)²/2} dx = e^{i t a} · e^{-t²/2} · √(2π).
      Translating the bump by `a` multiplies its transform by the unit-modulus
      phase `e^{i t a}`.

    • MODULATION ↦ TRANSLATION
        ∫_ℝ e^{i t x} · (e^{i a x} · e^{-x²/2}) dx = e^{-(t+a)²/2} · √(2π).
      Modulating the bump by `e^{i a x}` translates its transform by `a`
      (`t ↦ t + a`).

  These are dual statements: each is the other read through the inverse Fourier
  transform.  Two consequences make the duality concrete:

    • the modulus of the transform is *unchanged* by translation — the phase
      `e^{i t a}` has absolute value 1, so a translated Gaussian and the centred
      Gaussian have transforms of equal magnitude (only the phase moves);
    • both identities specialise at `a = 0` back to the parent's
      `gaussian_fourier_real`.

  METHOD.  Both reduce to the parent identity by *elementary* manipulations that
  need no new analysis:
    • translation: factor `e^{i t x} = e^{i t a} · e^{i t (x-a)}`, pull the
      constant out, and remove the shift with Lebesgue translation-invariance
      `MeasureTheory.integral_sub_right_eq_self`;
    • modulation: merge `e^{i t x} · e^{i a x} = e^{i (t+a) x}` and apply the
      parent at `t + a`.
  The base identity `gaussian_fourier_real` is reproved here verbatim (three short
  lemmas) so the file is self-contained.

  Everything is proved with 0 sorries and 0 axioms.

  References:
  - The shift theorem (translation/modulation duality), e.g. Stein–Shakarchi,
    Fourier Analysis (2003), Ch. 5.
  - Mathlib: Analysis.SpecialFunctions.Gaussian.FourierTransform
-/
import Mathlib

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Real Complex MeasureTheory
open scoped Real

namespace GaussianShiftTheorem

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  THE BASE GAUSSIAN FOURIER IDENTITY (reproved, self-contained)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Completing the square at the level of the integrand:
    `e^{i t x} · e^{-x²/2} = e^{-(1/2)(x + (-t)·i)²} · e^{-t²/2}` (using `i² = -1`). -/
theorem gaussian_integrand_complete_square (t x : ℝ) :
    Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
      = Complex.exp (-(((1 : ℝ) / 2 : ℝ) : ℂ) * ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) ^ 2)
        * Complex.exp (-(t : ℂ) ^ 2 / 2) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (t : ℂ) ^ 2 / 2 * Complex.I_sq

/-- The Mathlib contour constant `(π / (1/2))^(1/2)` is the complex coercion of
    the real `√(2π)`. -/
theorem cpow_half_eq_sqrt_two_pi :
    ((π : ℂ) / (((1 : ℝ) / 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have h0 : (0 : ℝ) ≤ 2 * π := by positivity
  rw [show ((π : ℂ) / (((1 : ℝ) / 2 : ℝ) : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h0]
  norm_num

/-- **The Gaussian is its own Fourier transform (un-normalized).**

      ∫_ℝ e^{i t x} · e^{-x²/2} dx = e^{-t²/2} · √(2π). -/
theorem gaussian_fourier_real (t : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
      = Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  simp_rw [gaussian_integrand_complete_square t]
  rw [MeasureTheory.integral_mul_const]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I
        (b := (((1 : ℝ) / 2 : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; norm_num) (-t)]
  rw [cpow_half_eq_sqrt_two_pi]
  ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  TRANSLATION ↦ MODULATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Translating the Gaussian multiplies its Fourier transform by a phase.**

      ∫_ℝ e^{i t x} · e^{-(x-a)²/2} dx = e^{i t a} · (e^{-t²/2} · √(2π)).

    Shifting the standard Gaussian by `a` in space introduces the unit-modulus
    factor `e^{i t a}` in frequency. -/
theorem gaussian_fourier_translation (t a : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-((x : ℂ) - a) ^ 2 / 2)
      = Complex.exp (Complex.I * (t : ℂ) * (a : ℂ))
          * (Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ)) := by
  -- factor the integrand as  e^{i t a} · ( e^{i t (x-a)} · e^{-(x-a)²/2} )
  have key : ∀ x : ℝ,
      Complex.exp (Complex.I * t * x) * Complex.exp (-((x : ℂ) - a) ^ 2 / 2)
        = Complex.exp (Complex.I * (t : ℂ) * (a : ℂ))
          * (Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - a))
              * Complex.exp (-((x : ℂ) - a) ^ 2 / 2)) := by
    intro x
    have e1 : Complex.exp (Complex.I * (t : ℂ) * (a : ℂ))
          * Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - a))
        = Complex.exp (Complex.I * t * x) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← mul_assoc, e1]
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  -- remove the shift via Lebesgue translation-invariance, then apply the parent
  have hF : (∫ x : ℝ, Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - a))
              * Complex.exp (-((x : ℂ) - a) ^ 2 / 2))
      = ∫ x : ℝ, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
              * Complex.exp (-(x : ℂ) ^ 2 / 2) := by
    have hcast : (∫ x : ℝ, Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - a))
                * Complex.exp (-((x : ℂ) - a) ^ 2 / 2))
        = ∫ x : ℝ, (fun y : ℝ => Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))
                * Complex.exp (-(y : ℂ) ^ 2 / 2)) (x - a) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      push_cast
      ring
    rw [hcast, MeasureTheory.integral_sub_right_eq_self
        (fun y : ℝ => Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))
            * Complex.exp (-(y : ℂ) ^ 2 / 2)) a]
  rw [hF, gaussian_fourier_real]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  MODULATION ↦ TRANSLATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Modulating the Gaussian translates its Fourier transform.**

      ∫_ℝ e^{i t x} · (e^{i a x} · e^{-x²/2}) dx = e^{-(t+a)²/2} · √(2π).

    Multiplying the standard Gaussian by the phase `e^{i a x}` shifts its
    transform `t ↦ t + a`. -/
theorem gaussian_fourier_modulation (t a : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x)
        * (Complex.exp (Complex.I * a * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
      = Complex.exp (-((t + a : ℝ) : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have key : ∀ x : ℝ,
      Complex.exp (Complex.I * t * x)
          * (Complex.exp (Complex.I * a * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
        = Complex.exp (Complex.I * ((t + a : ℝ) : ℂ) * (x : ℂ))
            * Complex.exp (-(x : ℂ) ^ 2 / 2) := by
    intro x
    rw [← mul_assoc, ← Complex.exp_add]
    have hexp : Complex.I * (t : ℂ) * (x : ℂ) + Complex.I * (a : ℂ) * (x : ℂ)
        = Complex.I * ((t + a : ℝ) : ℂ) * (x : ℂ) := by
      push_cast; ring
    rw [hexp]
  simp_rw [key]
  rw [gaussian_fourier_real (t + a)]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV:  CONSEQUENCES — DUALITY AND THE PARENT AS A SPECIAL CASE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Translation preserves the modulus of the transform.**  Because the phase
    `e^{i t a}` has absolute value 1, the translated Gaussian and the centred
    Gaussian have Fourier transforms of equal magnitude — translation only moves
    the phase. -/
theorem gaussian_fourier_translation_modulus (t a : ℝ) :
    ‖∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-((x : ℂ) - a) ^ 2 / 2)‖
      = ‖Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ)‖ := by
  rw [gaussian_fourier_translation, norm_mul]
  have hphase : ‖Complex.exp (Complex.I * (t : ℂ) * (a : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  rw [hphase, one_mul]

/-- The translation identity recovers the parent `gaussian_fourier_real` at
    `a = 0` (no shift, no phase). -/
theorem gaussian_fourier_translation_recovers_parent (t : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
      = Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  simpa using gaussian_fourier_translation t 0

/-- The modulation identity recovers the parent `gaussian_fourier_real` at
    `a = 0` (no modulation, no shift in frequency). -/
theorem gaussian_fourier_modulation_recovers_parent (t : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x)
        * (1 * Complex.exp (-(x : ℂ) ^ 2 / 2))
      = Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have h := gaussian_fourier_modulation t 0
  simpa using h

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## Translation–modulation duality for the Gaussian Fourier transform
   (area-of-circle-oq-05-oq-03-oq-03)

### What's proved (0 sorries, 0 axioms):
- `gaussian_fourier_real` (reproved, self-contained): the base identity
  ∫ e^{itx} e^{-x²/2} = e^{-t²/2}·√(2π).
- `gaussian_fourier_translation`: **∫ e^{itx} e^{-(x-a)²/2} = e^{ita}·e^{-t²/2}·√(2π)**
  — translation in space ↦ modulation by the phase e^{ita}.
- `gaussian_fourier_modulation`: **∫ e^{itx}·(e^{iax} e^{-x²/2}) = e^{-(t+a)²/2}·√(2π)**
  — modulation in space ↦ translation t ↦ t+a in frequency.
- `gaussian_fourier_translation_modulus`: the transform's magnitude is invariant
  under translation (the phase has modulus 1).
- `gaussian_fourier_translation_recovers_parent`,
  `gaussian_fourier_modulation_recovers_parent`: both specialise at a = 0 to the
  parent identity.

### Honest scope:
These are the standard "shift theorem" identities of Fourier analysis,
instantiated on the explicit Gaussian density and proved as concrete Lebesgue
integrals. No new analytic machinery is used: both reduce to the parent identity
by translation-invariance of Lebesgue measure and the exponent algebra. The
content is the *explicit duality* — that translation and modulation are exchanged
by the Gaussian Fourier transform — for the concrete density, complementing the
parent (self-duality) and the dilation/convolution siblings of this lineage.
-/

#check @gaussian_fourier_real
#check @gaussian_fourier_translation
#check @gaussian_fourier_modulation
#check @gaussian_fourier_translation_modulus

end GaussianShiftTheorem
