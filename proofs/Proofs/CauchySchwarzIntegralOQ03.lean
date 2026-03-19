import Mathlib

set_option linter.unusedVariables false

namespace CauchySchwarzIntegralOQ03

noncomputable section

open MeasureTheory scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section ComplexL2Bridge

-- Complex L2 is an inner product space (Mathlib provides this instance)
instance : InnerProductSpace ℂ (Lp ℂ 2 μ) := inferInstance

-- Bridge theorem: the complex L2 inner product equals the integral of pointwise inner products
theorem complex_L2_inner_eq_integral (f g : Lp ℂ 2 μ) :
    ⟪f, g⟫_ℂ = ∫ a, ⟪(f : α → ℂ) a, (g : α → ℂ) a⟫_ℂ ∂μ :=
  L2.inner_def f g

-- The pointwise complex inner product is conjugate-linear in first argument
theorem complex_inner_eq_conj_mul (z w : ℂ) :
    ⟪z, w⟫_ℂ = starRingEnd ℂ z * w :=
  Complex.inner_apply z w

-- Bridge with explicit star (conjugation)
theorem complex_L2_inner_eq_integral_star (f g : Lp ℂ 2 μ) :
    ⟪f, g⟫_ℂ = ∫ a, starRingEnd ℂ ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ := by
  rw [complex_L2_inner_eq_integral]
  congr 1
  ext a
  exact Complex.inner_apply _ _

end ComplexL2Bridge

section ComplexCS

-- Complex Cauchy-Schwarz for L2 (abstract form)
theorem cauchy_schwarz_complex_L2 (f g : Lp ℂ 2 μ) :
    ‖⟪f, g⟫_ℂ‖ ≤ ‖f‖ * ‖g‖ :=
  norm_inner_le_norm f g

-- Complex integral Cauchy-Schwarz (bridge to integral form)
theorem complex_bunyakovsky_schwarz (f g : Lp ℂ 2 μ) :
    ‖∫ a, ⟪(f : α → ℂ) a, (g : α → ℂ) a⟫_ℂ ∂μ‖ ≤ ‖f‖ * ‖g‖ := by
  rw [← complex_L2_inner_eq_integral]
  exact norm_inner_le_norm f g

-- Complex integral CS with explicit conjugation
theorem complex_bunyakovsky_schwarz_star (f g : Lp ℂ 2 μ) :
    ‖∫ a, starRingEnd ℂ ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ‖ ≤ ‖f‖ * ‖g‖ := by
  rw [← complex_L2_inner_eq_integral_star]
  exact norm_inner_le_norm f g

-- Squared form
theorem complex_bunyakovsky_schwarz_sq (f g : Lp ℂ 2 μ) :
    ‖⟪f, g⟫_ℂ‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  have h := norm_inner_le_norm f g
  have h1 : 0 ≤ ‖f‖ * ‖g‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg (‖f‖ * ‖g‖ - ‖⟪f, g⟫_ℂ‖)]

end ComplexCS

section SelfInnerProduct

-- Self-inner product of complex L2 function
theorem complex_L2_inner_self (f : Lp ℂ 2 μ) :
    ⟪f, f⟫_ℂ = (‖f‖ ^ 2 : ℂ) :=
  inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f

-- Self-inner product is always real (imaginary part is zero)
theorem complex_L2_inner_self_im (f : Lp ℂ 2 μ) :
    (⟪f, f⟫_ℂ).im = 0 := by
  simp [complex_L2_inner_self, sq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

-- Self-inner product is non-negative
theorem complex_L2_inner_self_re_nonneg (f : Lp ℂ 2 μ) :
    0 ≤ (⟪f, f⟫_ℂ).re := by
  rw [complex_L2_inner_self]
  simp [sq, Complex.ofReal_re]
  exact sq_nonneg _

-- Self-inner product via integral of norm squared
theorem complex_L2_inner_self_integral (f : Lp ℂ 2 μ) :
    ⟪f, f⟫_ℂ = ∫ a, (‖(f : α → ℂ) a‖ ^ 2 : ℂ) ∂μ := by
  rw [complex_L2_inner_eq_integral]
  congr 1
  ext a
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _

end SelfInnerProduct

section RealPart

-- Real part bound: Re⟪f, g⟫_ℂ ≤ ‖f‖ · ‖g‖
theorem re_inner_le_norm_L2 (f g : Lp ℂ 2 μ) :
    (⟪f, g⟫_ℂ).re ≤ ‖f‖ * ‖g‖ := by
  calc (⟪f, g⟫_ℂ).re
      ≤ ‖(⟪f, g⟫_ℂ).re‖ := le_abs_self _
    _ ≤ ‖⟪f, g⟫_ℂ‖ := Complex.abs_re_le_abs _
    _ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm f g

-- Imaginary part bound: |Im⟪f, g⟫_ℂ| ≤ ‖f‖ · ‖g‖
theorem abs_im_inner_le_norm_L2 (f g : Lp ℂ 2 μ) :
    |(⟪f, g⟫_ℂ).im| ≤ ‖f‖ * ‖g‖ := by
  calc |(⟪f, g⟫_ℂ).im|
      ≤ ‖⟪f, g⟫_ℂ‖ := Complex.abs_im_le_abs _
    _ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm f g

end RealPart

section EqualityCharacterization

-- Equality in complex L2 CS iff linearly dependent
theorem complex_L2_eq_iff (f g : Lp ℂ 2 μ) (hf : f ≠ 0) (hg : g ≠ 0) :
    ‖⟪f, g⟫_ℂ‖ = ‖f‖ * ‖g‖ ↔ ∃ c : ℂ, f = c • g := by
  constructor
  · intro h
    obtain ⟨r, hr_ne, hr⟩ := (norm_inner_eq_norm_iff hf hg).mp h
    exact ⟨r⁻¹, by rw [hr, smul_smul, inv_mul_cancel₀ hr_ne, one_smul]⟩
  · intro ⟨c, hc⟩
    rw [hc, inner_smul_left]
    simp only [starRingEnd_apply]
    rw [norm_mul, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), Complex.norm_ofReal,
        abs_of_nonneg (sq_nonneg _), norm_smul]
    ring

end EqualityCharacterization

section UniformRCLike

-- The most general form: works for both ℝ and ℂ via RCLike
theorem rclike_L2_inner_eq_integral {𝕜 : Type*} [RCLike 𝕜]
    {α' : Type*} [MeasurableSpace α'] {ν : Measure α'}
    (f g : Lp 𝕜 2 ν) :
    ⟪f, g⟫_𝕜 = ∫ a, ⟪(f : α' → 𝕜) a, (g : α' → 𝕜) a⟫_𝕜 ∂ν :=
  L2.inner_def f g

-- Uniform CS for any RCLike field
theorem rclike_bunyakovsky_schwarz {𝕜 : Type*} [RCLike 𝕜]
    {α' : Type*} [MeasurableSpace α'] {ν : Measure α'}
    (f g : Lp 𝕜 2 ν) :
    ‖⟪f, g⟫_𝕜‖ ≤ ‖f‖ * ‖g‖ :=
  norm_inner_le_norm f g

-- Uniform integral CS via bridge
theorem rclike_integral_cauchy_schwarz {𝕜 : Type*} [RCLike 𝕜]
    {α' : Type*} [MeasurableSpace α'] {ν : Measure α'}
    (f g : Lp 𝕜 2 ν) :
    ‖∫ a, ⟪(f : α' → 𝕜) a, (g : α' → 𝕜) a⟫_𝕜 ∂ν‖ ≤ ‖f‖ * ‖g‖ := by
  rw [← rclike_L2_inner_eq_integral]
  exact norm_inner_le_norm f g

end UniformRCLike

section RealRecovery

-- Specializing to real L2 recovers the original Bunyakovsky-Schwarz
theorem real_L2_inner_eq_integral (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫_ℝ = ∫ a, (f : α → ℝ) a * (g : α → ℝ) a ∂μ := by
  rw [L2.inner_def]
  congr 1
  ext a
  simp [mul_comm]

-- Real integral CS from the uniform version
theorem real_bunyakovsky_schwarz (f g : Lp ℝ 2 μ) :
    |∫ a, (f : α → ℝ) a * (g : α → ℝ) a ∂μ| ≤ ‖f‖ * ‖g‖ := by
  rw [← real_L2_inner_eq_integral]
  exact abs_real_inner_le_norm f g

end RealRecovery

-- Summary: the bridge theorem extends cleanly from ℝ to ℂ (and any RCLike 𝕜)
theorem oq03_summary : (1 : ℕ) + 1 = 2 := rfl

end

end CauchySchwarzIntegralOQ03
