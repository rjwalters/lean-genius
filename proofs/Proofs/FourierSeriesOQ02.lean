/-
# Fourier Coefficient Decay under Hölder Continuity (OQ-02)

## Main Result

If f : AddCircle T → ℂ is α-Hölder continuous with constant C, then its
Fourier coefficients decay as:

  ‖fourierCoeff f n‖ ≤ (C / 2) · dist(0, h)^α     for n ≠ 0

where h = T/(2n) is the adapted half-period element. This gives the optimal
rate |ĉₙ| = O(|n|^{-α}) as |n| → ∞.

## Proof Technique

The **half-period shift trick**: for n ≠ 0, shift the integration variable
by h = T/(2n). The Fourier exponential picks up a factor of -1 at this shift,
while the Hölder condition controls |f(x) - f(x+h)| ≤ C · dist(0,h)^α.
-/

import Mathlib

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle
open scoped ENNReal NNReal Real

namespace FourierHolderDecay

variable {T : ℝ} [hT : Fact (0 < T)]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: CHARACTER PROPERTY OF FOURIER MONOMIALS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Fourier monomial `fourier n` is a multiplicative character of `AddCircle T`. -/
theorem fourier_add_right (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add]
  rfl

/-- Norm of Fourier monomials is 1 (values lie on the unit circle). -/
theorem norm_fourier_eq_one (n : ℤ) (x : AddCircle T) :
    ‖fourier n x‖ = 1 := by
  show ‖(AddCircle.toCircle (n • x) : ℂ)‖ = 1
  have h := (AddCircle.toCircle (n • x)).2
  simpa [Metric.mem_sphere, dist_zero_right] using h

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: HALF-PERIOD EVALUATION — THE KEY COMPUTATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The half-period element adapted to frequency n. -/
def halfPeriod (n : ℤ) : ℝ := T / (2 * (n : ℝ))

/-- At the adapted half-period, fourier(-n) evaluates to -1.
    exp(2πi(-n)(T/(2n))/T) = exp(-πi) = -1. -/
theorem fourier_neg_at_halfPeriod (n : ℤ) (hn : n ≠ 0) :
    fourier (-n) (↑(halfPeriod (T := T) n) : AddCircle T) = -1 := by
  rw [fourier_coe_apply]
  have hT_ne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hT.out)
  have hn_ne : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  -- Step 1: Simplify the exponent to -π·I
  -- The exponent 2πI(-n)(T/(2n))/T simplifies to -(π*I)
  -- exp(-(πI)) = (exp(πI))⁻¹ = (-1)⁻¹ = -1
  -- Step 1: Compute n * halfPeriod = T/2 in ℝ
  have hR : (n : ℝ) * halfPeriod (T := T) n = T / 2 := by
    unfold halfPeriod; field_simp
  -- Step 2: Compute the complex exponent as -(π * I) via separate have
  -- (isolated from main goal to prevent field_simp interference)
  suffices key : 2 * ↑Real.pi * I * (↑(-n : ℤ) : ℂ) * (↑(halfPeriod (T := T) n) : ℂ) / (↑T : ℂ) =
      -(↑Real.pi * I) by
    rw [key, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  -- Proof of key: arithmetic in ℂ
  calc 2 * ↑Real.pi * I * (↑(-n : ℤ) : ℂ) * (↑(halfPeriod n) : ℂ) / (↑T : ℂ)
      = -(2 * ↑Real.pi * I * ((↑n : ℂ) * ↑(halfPeriod n)) / ↑T) := by push_cast; ring
    _ = -(2 * ↑Real.pi * I * ↑((n : ℝ) * halfPeriod n) / ↑T) := by push_cast; ring
    _ = -(2 * ↑Real.pi * I * ↑(T / 2) / ↑T) := by rw [hR]
    _ = -(↑Real.pi * I) := by
        push_cast; field_simp

/-- Shifting by the adapted half-period negates the Fourier exponential. -/
theorem fourier_neg_shift (n : ℤ) (hn : n ≠ 0) (x : AddCircle T) :
    fourier (-n) (x + (↑(halfPeriod (T := T) n) : AddCircle T)) = -(fourier (-n) x) := by
  rw [fourier_add_right, fourier_neg_at_halfPeriod n hn, mul_neg_one]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: DIFFERENCE REPRESENTATION OF FOURIER COEFFICIENTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Translation invariance of Haar integral. -/
theorem integral_translate (g : AddCircle T → ℂ) (h : AddCircle T) :
    ∫ x, g x ∂haarAddCircle = ∫ x, g (x + h) ∂haarAddCircle :=
  (integral_add_right_eq_self g h).symm

/-- Shifting the Fourier integral by the half-period gives a sign flip. -/
theorem fourierCoeff_eq_neg_shifted (f : AddCircle T → ℂ) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff f n =
    -(∫ x, fourier (-n) x * f (x + (↑(halfPeriod (T := T) n) : AddCircle T)) ∂haarAddCircle) := by
  have h1 : fourierCoeff f n = ∫ x, fourier (-n) x * f x ∂haarAddCircle := rfl
  conv_lhs =>
    rw [h1, integral_translate (fun x => fourier (-n) x * f x)
        (↑(halfPeriod (T := T) n) : AddCircle T)]
  simp_rw [fourier_neg_shift n hn]
  simp [neg_mul, integral_neg]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: HÖLDER CONTINUITY AND DISTANCE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Hölder continuity: ‖f(x) - f(y)‖ ≤ C · dist(x,y)^α -/
def IsHolderOn (f : AddCircle T → ℂ) (C α : ℝ) : Prop :=
  0 < α ∧ 0 ≤ C ∧ ∀ x y : AddCircle T, ‖f x - f y‖ ≤ C * dist x y ^ α

/-- Distance is translation-invariant: dist(x, x+h) = dist(0, h) -/
theorem dist_self_add_eq (h x : AddCircle T) :
    dist x (x + h) = dist (0 : AddCircle T) h := by
  rw [add_comm x h, ← dist_add_right 0 h x, zero_add]

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: INTEGRABILITY HELPERS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Product of a Fourier monomial with an integrable function is integrable. -/
theorem fourier_mul_integrable (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle) (m : ℤ) :
    Integrable (fun x => fourier m x * f x) (haarAddCircle (T := T)) :=
  hf.mono ((fourier m).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (by filter_upwards with x; rw [norm_mul, norm_fourier_eq_one, one_mul])

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: THE MAIN DECAY THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Main Theorem**: Fourier coefficient decay under Hölder continuity.

    If f : AddCircle T → ℂ is α-Hölder continuous with constant C, then
    ‖fourierCoeff f n‖ ≤ (C / 2) · dist(0, h)^α for n ≠ 0,
    where h = ↑(T/(2n)) in AddCircle T. -/
theorem fourierCoeff_holder_decay
    (f : AddCircle T → ℂ)
    (C α : ℝ)
    (hHolder : IsHolderOn f C α)
    (hf_int : Integrable f haarAddCircle)
    (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff f n‖ ≤
      C / 2 * dist (0 : AddCircle T) (↑(halfPeriod (T := T) n) : AddCircle T) ^ α := by
  obtain ⟨hα, hC, hHold⟩ := hHolder
  set h : AddCircle T := ↑(halfPeriod n) with h_def
  -- Shifted function is also integrable
  have hf_sh : Integrable (fun x => f (x + h)) haarAddCircle := hf_int.comp_add_right h
  -- Step 1: Two representations
  have h_pos : fourierCoeff f n = ∫ x, fourier (-n) x * f x ∂haarAddCircle := rfl
  have h_neg := fourierCoeff_eq_neg_shifted f n hn
  -- Step 2: Difference representation
  have h_diff : 2 * fourierCoeff f n =
      ∫ x, fourier (-n) x * (f x - f (x + h)) ∂haarAddCircle := by
    have eq1 : 2 * fourierCoeff f n =
        (∫ x, fourier (-n) x * f x ∂haarAddCircle) -
        (∫ x, fourier (-n) x * f (x + h) ∂haarAddCircle) := by
      rw [two_mul]; nth_rewrite 1 [h_pos]; rw [h_neg]; ring
    rw [eq1, ← integral_sub
      (fourier_mul_integrable f hf_int (-n))
      (fourier_mul_integrable (fun x => f (x + h)) hf_sh (-n))]
    congr 1; ext x; ring
  -- Step 3: Pointwise bound from Hölder condition
  have h_holder_bound : ∀ x : AddCircle T,
      ‖f x - f (x + h)‖ ≤ C * dist (0 : AddCircle T) h ^ α := fun x => by
    calc ‖f x - f (x + h)‖ ≤ C * dist x (x + h) ^ α := hHold x (x + h)
      _ = C * dist (0 : AddCircle T) h ^ α := by rw [dist_self_add_eq]
  -- Step 4: Bound the integral
  have h_int_bound :
      ‖∫ x, fourier (-n) x * (f x - f (x + h)) ∂haarAddCircle‖ ≤
        C * dist (0 : AddCircle T) h ^ α := by
    calc ‖∫ x, fourier (-n) x * (f x - f (x + h)) ∂haarAddCircle‖
        ≤ ∫ x, ‖fourier (-n) x * (f x - f (x + h))‖ ∂haarAddCircle :=
          norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x - f (x + h)‖ ∂haarAddCircle := by
          congr 1; ext x; rw [norm_mul, norm_fourier_eq_one, one_mul]
      _ ≤ ∫ _ : AddCircle T, C * dist (0 : AddCircle T) h ^ α ∂haarAddCircle := by
          apply integral_mono_of_nonneg
          · filter_upwards with x using norm_nonneg _
          · exact integrable_const _
          · filter_upwards with x using h_holder_bound x
      _ = C * dist (0 : AddCircle T) h ^ α := by
          simp [integral_const]
  -- Step 5: From |2·c_n| ≤ B, deduce |c_n| ≤ B/2
  calc ‖fourierCoeff f n‖
      = ‖2 * fourierCoeff f n‖ / 2 := by
        have : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [norm_mul, this]; ring
      _ = ‖∫ x, fourier (-n) x * (f x - f (x + h)) ∂haarAddCircle‖ / 2 := by
        rw [h_diff]
      _ ≤ (C * dist (0 : AddCircle T) h ^ α) / 2 :=
        div_le_div_of_nonneg_right h_int_bound (by positivity)
      _ = C / 2 * dist (0 : AddCircle T) h ^ α := by ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: COROLLARIES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Lipschitz case (α = 1): |ĉₙ| ≤ (C/2) · dist(0, h). -/
theorem fourierCoeff_lipschitz_decay
    (f : AddCircle T → ℂ)
    (C : ℝ)
    (hLip : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ C * dist x y)
    (hC : 0 ≤ C)
    (hf_int : Integrable f haarAddCircle)
    (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff f n‖ ≤
      C / 2 * dist (0 : AddCircle T) (↑(halfPeriod (T := T) n) : AddCircle T) := by
  have hHolder : IsHolderOn f C 1 := by
    exact ⟨one_pos, hC, fun x y => by simp only [Real.rpow_one]; exact hLip x y⟩
  have h := fourierCoeff_holder_decay f C 1 hHolder hf_int n hn
  simp only [Real.rpow_one] at h; exact h

/-
═══════════════════════════════════════════════════════════════════════════════
PART VIII: VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @fourier_add_right
#check @norm_fourier_eq_one
#check @fourier_neg_at_halfPeriod
#check @fourier_neg_shift
#check @fourierCoeff_eq_neg_shifted
#check @dist_self_add_eq
#check @fourierCoeff_holder_decay
#check @fourierCoeff_lipschitz_decay

end FourierHolderDecay
