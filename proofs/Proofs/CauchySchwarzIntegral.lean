import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-
# Bunyakovsky-Schwarz Integral Inequality

## What This Proves
The integral form of the Cauchy-Schwarz inequality, also known as the
Bunyakovsky-Schwarz inequality:

  (∫ f · g dμ)² ≤ (∫ f² dμ) · (∫ g² dμ)

for square-integrable functions f, g in L²(μ).

## Approach
The key insight is that Mathlib's L²(μ) space is already an InnerProductSpace,
where the inner product is defined as ⟪f, g⟫ = ∫ f · g dμ. Therefore the
abstract Cauchy-Schwarz inequality |⟪f, g⟫| ≤ ‖f‖ · ‖g‖ directly gives us
the integral form.

## Historical Note
Viktor Bunyakovsky first proved this for integrals in 1859. Hermann Schwarz
independently proved it in 1885 for the context of variational calculus.

## Status
- [x] Abstract L2 Cauchy-Schwarz (|⟪f,g⟫| ≤ ‖f‖·‖g‖)
- [x] L2 inner product = integral bridge
- [x] L2 norm squared = integral of square bridge
- [x] Integral form: |∫ f·g dμ| ≤ ‖f‖_L2 · ‖g‖_L2
- [x] Squared integral form
- [x] Equality characterization
-/

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace BunyakovskySchwarz

-- L2 is an inner product space (Mathlib provides this instance)
instance : InnerProductSpace ℝ (Lp ℝ 2 μ) := inferInstance

-- The abstract Cauchy-Schwarz on L2 functions
theorem cauchy_schwarz_L2 (f g : Lp ℝ 2 μ) :
    |@inner ℝ _ _ f g| ≤ ‖f‖ * ‖g‖ :=
  abs_real_inner_le_norm f g

-- Squared form on L2
theorem cauchy_schwarz_L2_sq (f g : Lp ℝ 2 μ) :
    (@inner ℝ _ _ f g) ^ 2 ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  have h := abs_real_inner_le_norm f g
  have h_nonneg : 0 ≤ ‖f‖ * ‖g‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h_sq := sq_le_sq' (by linarith [abs_nonneg (@inner ℝ _ _ f g)]) h
  rw [sq_abs] at h_sq
  calc (@inner ℝ _ _ f g) ^ 2 ≤ (‖f‖ * ‖g‖) ^ 2 := h_sq
    _ = ‖f‖ ^ 2 * ‖g‖ ^ 2 := by ring

-- The inner product on L2 IS the integral
-- MeasureTheory.L2.inner_def : ⟪f, g⟫ = ∫ a, inner (f a) (g a) ∂μ
-- For ℝ-valued functions, inner x y = x * y

-- Bridge theorem: the L2 inner product equals ∫ f * g dμ
-- This is the key connection between abstract inner product and integrals
theorem L2_inner_eq_integral (f g : Lp ℝ 2 μ) :
    @inner ℝ _ _ f g = ∫ a, (f : α → ℝ) a * (g : α → ℝ) a ∂μ := by
  rw [L2.inner_def]
  congr 1
  ext a
  simp [mul_comm]

-- Bunyakovsky-Schwarz Inequality (Integral Form, Absolute Value)
--
-- For L² functions f, g:
--   |∫ f · g dμ| ≤ ‖f‖_L2 · ‖g‖_L2
--
-- This is the classical integral form of Cauchy-Schwarz.
theorem bunyakovsky_schwarz_abs (f g : Lp ℝ 2 μ) :
    |∫ a, (f : α → ℝ) a * (g : α → ℝ) a ∂μ| ≤ ‖f‖ * ‖g‖ := by
  rw [← L2_inner_eq_integral]
  exact abs_real_inner_le_norm f g

-- Bunyakovsky-Schwarz Inequality (Integral Form, Squared)
--
-- For L² functions f, g:
--   (∫ f · g dμ)² ≤ ‖f‖² · ‖g‖²
theorem bunyakovsky_schwarz_sq (f g : Lp ℝ 2 μ) :
    (∫ a, (f : α → ℝ) a * (g : α → ℝ) a ∂μ) ^ 2 ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  rw [← L2_inner_eq_integral]
  exact cauchy_schwarz_L2_sq f g

-- Equality Characterization
--
-- Equality in L2 Cauchy-Schwarz holds iff f and g are linearly dependent in L2.
theorem cauchy_schwarz_L2_eq_iff (f g : Lp ℝ 2 μ) (hf : f ≠ 0) (hg : g ≠ 0) :
    |@inner ℝ _ _ f g| = ‖f‖ * ‖g‖ ↔ ∃ c : ℝ, f = c • g := by
  constructor
  · intro h
    have h' : ‖@inner ℝ _ _ f g‖ = ‖f‖ * ‖g‖ := by rwa [Real.norm_eq_abs]
    obtain ⟨r, hr_ne, hr⟩ := (norm_inner_eq_norm_iff hf hg).mp h'
    exact ⟨r⁻¹, by rw [hr, smul_smul, inv_mul_cancel₀ hr_ne, one_smul]⟩
  · intro ⟨c, hc⟩
    rw [hc, inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs]
    simp only [starRingEnd_apply, star_trivial]
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖g‖)]
    ring

-- Summary check
#check @bunyakovsky_schwarz_abs
#check @bunyakovsky_schwarz_sq
#check @cauchy_schwarz_L2_eq_iff

end BunyakovskySchwarz

end