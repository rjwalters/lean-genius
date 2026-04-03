/-
  Differential Entropy for Continuous Distributions

  OQ01 from Shannon Entropy gallery entry:
  "Can differential entropy h(X) = -∫ f(x) ln f(x) dx for continuous
  distributions be formalized in Lean using Mathlib's measure theory?"

  Answer: YES. This file formalizes differential entropy via Mathlib's
  Bochner integral, demonstrating:
  - The 0·ln(0) = 0 convention is automatic (Real.log 0 = 0 in Mathlib)
  - Translation invariance: h(f(·-c)) = h(f) (Lebesgue measure invariance)
  - Continuous Gibbs inequality: D(f||g) = ∫ f·ln(f/g) ≥ 0
  - Gibbs corollary: h(f) ≤ -∫ f·ln g for any reference density g

  Key contrast with discrete entropy:
  - Differential entropy CAN be negative (e.g., Uniform[0,a] has h = ln a < 0 for a < 1)
  - Translation invariant: h(f(·-c)) = h(f)
  - Scale equivariant: h(f(·/a)/|a|) = h(f) + ln|a|

  Gaussian entropy: h(N(μ,σ²)) = ½ ln(2πeσ²) [proved modulo second moment lemma]
-/
import Mathlib

namespace DifferentialEntropy

open MeasureTheory Real

/-!
## Definition

Differential entropy h(f) = -∫ f(x) ln f(x) dx.

The convention 0·ln(0) = 0 holds automatically in Lean/Mathlib because
`Real.log 0 = 0`, so `0 * Real.log 0 = 0`.

We use the default Lebesgue measure (`volume`) on ℝ. The Bochner integral
returns 0 when the function is not integrable, so the definition is always
well-defined; theorems require integrability hypotheses.
-/

/-- Differential entropy of a density function f: h(f) = -∫ f(x) ln f(x) dx.
    Convention 0·ln(0) = 0 is automatic since Real.log 0 = 0 in Mathlib. -/
noncomputable def differentialEntropy (f : ℝ → ℝ) : ℝ :=
  -∫ x, f x * Real.log (f x)

/-- Continuous KL divergence (relative entropy): D(f||g) = ∫ f(x)·ln(f(x)/g(x)) dx. -/
noncomputable def klDivergenceCts (f g : ℝ → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x / g x)

/-!
## Key Lemma: Pointwise KL Bound

For the continuous Gibbs inequality we need: p · ln(p/q) ≥ p - q for p > 0, q > 0.
This is the same pointwise bound used in the discrete ShannonEntropy.lean.
-/

/-- Pointwise KL bound: p * log(p/q) ≥ p - q for p > 0, q > 0.
    Proof: log(q/p) ≤ q/p - 1 (standard inequality), multiply by p and negate. -/
private lemma kl_term_bound_cts {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p * Real.log (p / q) ≥ p - q := by
  have h1 : Real.log (q / p) ≤ q / p - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hq hp)
  have h2 : p * Real.log (q / p) ≤ q - p :=
    calc p * Real.log (q / p)
        ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
      _ = q - p := by field_simp
  have h3 : Real.log (p / q) = -Real.log (q / p) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq),
        Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
    ring
  have h4 : p * Real.log (p / q) = -(p * Real.log (q / p)) := by
    rw [h3]; ring
  linarith

/-!
## Continuous Gibbs Inequality (KL Divergence Non-negativity)

D(f||g) = ∫ f·ln(f/g) ≥ 0 for probability densities f, g.

Proof: Pointwise f·ln(f/g) ≥ f - g (from log t ≤ t - 1), integrate, use ∫f = ∫g = 1.
-/

/-- Continuous KL divergence is non-negative for probability densities.

    Assumptions:
    - f ≥ 0 pointwise
    - g > 0 pointwise (reference density everywhere positive)
    - ∫f = ∫g = 1 (both are probability densities)
    - Integrability conditions for the functions involved -/
theorem kl_divergence_continuous_nonneg
    {f g : ℝ → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x)
    (hg_pos : ∀ x, 0 < g x)
    (hf_sum : ∫ x, f x = 1)
    (hg_sum : ∫ x, g x = 1)
    (hf_int : Integrable f)
    (hg_int : Integrable g)
    (hfg_int : Integrable (fun x => f x * Real.log (f x / g x))) :
    0 ≤ klDivergenceCts f g := by
  unfold klDivergenceCts
  have h_fg_int : Integrable (fun x => f x - g x) :=
    hf_int.sub hg_int
  have h_fg_zero : ∫ x, (f x - g x) = 0 := by
    rw [integral_sub hf_int hg_int, hf_sum, hg_sum, sub_self]
  have h_pointwise : ∀ x, f x - g x ≤ f x * Real.log (f x / g x) := by
    intro x
    by_cases hfx : f x = 0
    · simp only [hfx, zero_mul, zero_sub]
      exact neg_nonpos.mpr (le_of_lt (hg_pos x))
    · have hfx_pos : 0 < f x := lt_of_le_of_ne (hf_nn x) (Ne.symm hfx)
      linarith [kl_term_bound_cts hfx_pos (hg_pos x)]
  linarith [integral_mono h_fg_int hfg_int h_pointwise, h_fg_zero]

/-- Continuous Gibbs inequality: h(f) ≤ -∫ f · ln g for probability densities f, g.
    Proof: D(f||g) ≥ 0 is equivalent to ∫ f·log f ≥ ∫ f·log g,
    i.e., -∫ f·log f ≤ -∫ f·log g, i.e., h(f) ≤ -∫ f·log g. -/
theorem gibbs_inequality_continuous
    {f g : ℝ → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x)
    (hg_pos : ∀ x, 0 < g x)
    (hf_sum : ∫ x, f x = 1)
    (hg_sum : ∫ x, g x = 1)
    (hf_int : Integrable f)
    (hg_int : Integrable g)
    (hflog_f_int : Integrable (fun x => f x * Real.log (f x)))
    (hflog_g_int : Integrable (fun x => f x * Real.log (g x)))
    (hfg_int : Integrable (fun x => f x * Real.log (f x / g x))) :
    differentialEntropy f ≤ -∫ x, f x * Real.log (g x) := by
  unfold differentialEntropy
  -- KL divergence non-negativity
  have h_kl := kl_divergence_continuous_nonneg hf_nn hg_pos hf_sum hg_sum
    hf_int hg_int hfg_int
  unfold klDivergenceCts at h_kl
  -- Pointwise: f·log(f/g) = f·log f - f·log g
  have h_split : ∀ x, f x * Real.log (f x / g x) =
      f x * Real.log (f x) - f x * Real.log (g x) := by
    intro x
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hfx_pos : 0 < f x := lt_of_le_of_ne (hf_nn x) (Ne.symm hfx)
      rw [Real.log_div (ne_of_gt hfx_pos) (ne_of_gt (hg_pos x))]
      ring
  -- Rewrite the integrand then split the integral
  have h_eq : ∫ x, f x * Real.log (f x / g x) =
      (∫ x, f x * Real.log (f x)) - ∫ x, f x * Real.log (g x) := by
    have h_integrand : (fun x => f x * Real.log (f x / g x)) =
                       (fun x => f x * Real.log (f x) - f x * Real.log (g x)) := by
      ext x; exact h_split x
    rw [h_integrand]
    exact integral_sub hflog_f_int hflog_g_int
  -- From 0 ≤ ∫ f log(f/g) = ∫ f log f - ∫ f log g, get h(f) ≤ -∫ f log g
  have h_kl' : 0 ≤ (∫ x, f x * Real.log (f x)) - ∫ x, f x * Real.log (g x) :=
    h_eq ▸ h_kl
  linarith

/-!
## Translation Invariance

Differential entropy is translation invariant: h(f(·-c)) = h(f).
Proof uses Lebesgue measure translation invariance on ℝ
(integral_add_right_eq_self from Mathlib.MeasureTheory.Group.Integral).
-/

/-- Differential entropy is translation invariant: h(x ↦ f(x-c)) = h(f).
    The Lebesgue measure on ℝ is translation invariant:
    ∫ x, φ(x + a) dx = ∫ x, φ(x) dx. -/
theorem differentialEntropy_translation_invariant (f : ℝ → ℝ) (c : ℝ) :
    differentialEntropy (fun x => f (x - c)) = differentialEntropy f := by
  unfold differentialEntropy
  congr 1
  -- Goal after congr 1: ∫ x, f(x-c)*log(f(x-c)) = ∫ x, f x * log(f x)
  -- Rewrite integrand as (fun y => f y * log(f y)) applied at (x + (-c))
  have h1 : (fun x => (fun x => f (x - c)) x * Real.log ((fun x => f (x - c)) x)) =
            (fun x => (fun y => f y * Real.log (f y)) (x + (-c))) := by
    ext x; simp [sub_eq_add_neg]
  rw [h1]
  -- Apply Lebesgue measure translation invariance
  exact integral_add_right_eq_self (fun y => f y * Real.log (f y)) (-c)

/-!
## Scale Equivariance

h(f(·/a)/|a|) = h(f) + ln|a| — stated with sorry for the substitution step.
-/

/-- Scale equivariance: if g(x) = (1/|a|)·f(x/a) is the density of aX, then
    h(g) = h(f) + ln|a|.

    Proof sketch (requires change-of-variables for Lebesgue integrals):
    h(g) = -∫ (1/|a|)f(x/a)·[log f(x/a) - log|a|] dx
    After substitution y = x/a (dx = |a|·dy):
         = -(1/|a|)|a| ∫ f(y)·[log f(y) - log|a|] dy
         = -∫ f(y)·log f(y) dy + log|a| ∫ f(y) dy
         = h(f) + log|a|  (when ∫f = 1).

    Requires ∫f = 1 (f is a probability density). -/
theorem differentialEntropy_scale_equivariant (f : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0)
    (hf_nn : ∀ x, 0 ≤ f x)
    (hf_sum : ∫ x, f x = 1)
    (hf_int : Integrable f)
    (hflog_int : Integrable (fun x => f x * Real.log (f x))) :
    differentialEntropy (fun x => (1 / |a|) * f (x / a)) =
    differentialEntropy f + Real.log |a| := by
  unfold differentialEntropy
  have ha_pos : (0 : ℝ) < |a| := abs_pos.mpr ha
  have h_ptwise : ∀ x : ℝ,
      (1/|a|) * f (x/a) * Real.log ((1/|a|) * f (x/a)) =
      (1/|a|) * f (x/a) * (-Real.log |a|) + (1/|a|) * f (x/a) * Real.log (f (x/a)) := by
    intro x
    by_cases hfx : f (x/a) = 0
    · simp [hfx]
    · have hfx_pos : 0 < f (x/a) := lt_of_le_of_ne (hf_nn _) (Ne.symm hfx)
      rw [show (1 : ℝ) / |a| = |a|⁻¹ from one_div _,
          Real.log_mul (inv_pos.mpr ha_pos).ne' hfx_pos.ne', Real.log_inv]
      ring
  simp_rw [h_ptwise]
  have hf_div_int : Integrable (fun x => f (x/a)) := hf_int.comp_div ha
  have hflog_div_int : Integrable (fun x => f (x/a) * Real.log (f (x/a))) :=
    hflog_int.comp_div ha
  have hint1 : Integrable (fun x => (1/|a|) * f (x/a) * (-Real.log |a|)) := by
    have : (fun x : ℝ => (1/|a|) * f (x/a) * (-Real.log |a|)) =
        fun x => (-Real.log |a| / |a|) * f (x/a) := by funext; ring
    rw [this]; exact hf_div_int.const_mul _
  have hint2 : Integrable (fun x => (1/|a|) * f (x/a) * Real.log (f (x/a))) := by
    have : (fun x : ℝ => (1/|a|) * f (x/a) * Real.log (f (x/a))) =
        fun x => (1/|a|) * (f (x/a) * Real.log (f (x/a))) := by funext; ring
    rw [this]; exact hflog_div_int.const_mul _
  rw [integral_add hint1 hint2]
  have hcov1 : ∫ x : ℝ, (1/|a|) * f (x/a) * (-Real.log |a|) = -Real.log |a| := by
    have key : ∫ x : ℝ, f (x/a) = |a| * ∫ x : ℝ, f x := by
      have hh := MeasureTheory.Measure.integral_comp_div (g := f) a
      simp only [smul_eq_mul] at hh; exact hh
    have heq : (fun x : ℝ => (1/|a|) * f (x/a) * (-Real.log |a|)) =
        fun x => (-Real.log |a| / |a|) * f (x/a) := by funext; ring
    rw [heq, integral_const_mul, key, hf_sum, mul_one]
    field_simp [ha_pos.ne']
  have hcov2 : ∫ x : ℝ, (1/|a|) * f (x/a) * Real.log (f (x/a)) =
      ∫ x : ℝ, f x * Real.log (f x) := by
    have key : ∫ x : ℝ, f (x/a) * Real.log (f (x/a)) = |a| * ∫ x : ℝ, f x * Real.log (f x) := by
      have hh := MeasureTheory.Measure.integral_comp_div
        (g := fun y => f y * Real.log (f y)) a
      simp only [smul_eq_mul] at hh; exact hh
    have heq : (fun x : ℝ => (1/|a|) * f (x/a) * Real.log (f (x/a))) =
        fun x => (1/|a|) * (f (x/a) * Real.log (f (x/a))) := by funext; ring
    rw [heq, integral_const_mul, key]
    field_simp [ha_pos.ne']
  rw [hcov1, hcov2]
  ring

/-!
## Gaussian Differential Entropy

For X ~ N(μ, σ²), h(X) = ½ ln(2πeσ²).
-/

/-- The Gaussian probability density function: φ(x) = (2πσ²)^{-1/2} exp(-(x-μ)²/(2σ²)). -/
noncomputable def gaussianPDF (μ σ : ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2))

private lemma gaussianPDF_eq_gaussianPDFReal (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    gaussianPDF μ σ x = ProbabilityTheory.gaussianPDFReal μ ⟨σ ^ 2, sq_nonneg σ⟩ x := by
  unfold gaussianPDF ProbabilityTheory.gaussianPDFReal
  simp only [NNReal.coe_mk]

private lemma gaussianPDF_integral_eq_one (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x : ℝ, gaussianPDF μ σ x = 1 := by
  simp_rw [gaussianPDF_eq_gaussianPDFReal μ hσ]
  apply ProbabilityTheory.integral_gaussianPDFReal_eq_one
  apply NNReal.coe_ne_zero.mp
  simp only [NNReal.coe_mk]
  exact (pow_pos hσ 2).ne'

private lemma gaussianPDF_integrable (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (gaussianPDF μ σ) := by
  simp_rw [gaussianPDF_eq_gaussianPDFReal μ hσ]
  exact ProbabilityTheory.integrable_gaussianPDFReal μ _

private lemma gaussianPDF_log (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    Real.log (gaussianPDF μ σ x) =
    -(1 / 2) * Real.log (2 * Real.pi * σ ^ 2) - (x - μ) ^ 2 / (2 * σ ^ 2) := by
  unfold gaussianPDF
  rw [Real.log_mul (inv_pos.mpr (Real.sqrt_pos_of_pos (by positivity))).ne'
        (Real.exp_ne_zero _),
      Real.log_inv, Real.log_sqrt (by positivity), Real.log_exp]
  ring

private lemma gaussian_second_moment (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x : ℝ, (x - μ) ^ 2 * gaussianPDF μ σ x = σ ^ 2 := by
  sorry  -- Submitted to Aristotle

private lemma gaussian_quad_integrable (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : ℝ => (x - μ) ^ 2 * gaussianPDF μ σ x) := by
  sorry  -- Submitted to Aristotle

/-- Differential entropy of the Gaussian N(μ, σ²) is ½ ln(2πeσ²).

    Proof (requiring Gaussian integral and second moment):
    h(φ) = -∫ φ(x)·[-½ln(2πσ²) - (x-μ)²/(2σ²)] dx
         = ½ln(2πσ²)·∫φ + (1/2σ²)·∫(x-μ)²·φ(x) dx
         = ½ln(2πσ²)·1 + (1/2σ²)·σ²  [normalization + variance]
         = ½ln(2πσ²) + ½ = ½ln(2πeσ²). -/
theorem gaussianDifferentialEntropy (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    differentialEntropy (gaussianPDF μ σ) =
    (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * σ ^ 2) := by
  unfold differentialEntropy
  have h_eq : (fun x : ℝ => gaussianPDF μ σ x * Real.log (gaussianPDF μ σ x)) =
      fun x => -(1/2) * Real.log (2 * Real.pi * σ^2) * gaussianPDF μ σ x +
               (-1/(2*σ^2)) * ((x - μ)^2 * gaussianPDF μ σ x) := by
    funext x; rw [gaussianPDF_log μ hσ]; ring
  have hint1 : Integrable (fun x : ℝ =>
      -(1/2) * Real.log (2 * Real.pi * σ^2) * gaussianPDF μ σ x) :=
    (gaussianPDF_integrable μ hσ).const_mul _
  have hint2 : Integrable (fun x : ℝ =>
      (-1/(2*σ^2)) * ((x - μ)^2 * gaussianPDF μ σ x)) :=
    (gaussian_quad_integrable μ hσ).const_mul _
  have h1 : ∫ x : ℝ, -(1/2) * Real.log (2 * Real.pi * σ^2) * gaussianPDF μ σ x =
      -(1/2) * Real.log (2 * Real.pi * σ^2) := by
    rw [integral_const_mul, gaussianPDF_integral_eq_one μ hσ, mul_one]
  have h2 : ∫ x : ℝ, (-1/(2*σ^2)) * ((x - μ)^2 * gaussianPDF μ σ x) =
      -1/(2*σ^2) * σ^2 := by
    rw [integral_const_mul, gaussian_second_moment μ hσ]
  rw [h_eq, integral_add hint1 hint2, h1, h2]
  have hlog : (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * σ^2) =
      (1/2) * Real.log (2 * Real.pi * σ^2) + 1/2 := by
    rw [show 2 * Real.pi * Real.exp 1 * σ^2 = 2 * Real.pi * σ^2 * Real.exp 1 from by ring,
        Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    ring
  rw [hlog]
  linarith [show (-1 : ℝ) / (2 * σ^2) * σ^2 = -1/2 from by field_simp [hσ.ne']]

/-!
## Maximum Entropy Property (Gaussian Optimality)

Among all densities with variance ≤ σ², the Gaussian maximizes differential entropy.
Proof applies continuous Gibbs with g = gaussianPDF.
-/

/-- Gaussian maximizes differential entropy at fixed variance.
    For any density f with ∫ x² f(x) dx ≤ σ² and ∫ f = 1:
    h(f) ≤ ½ ln(2πeσ²) = h(N(0,σ²)).

    Proof: Gibbs inequality gives h(f) ≤ -∫ f log(gaussianPDF 0 σ).
    Expanding log(gaussianPDF) = -½ log(2πσ²) - x²/(2σ²) and using
    ∫f=1 and ∫x²f ≤ σ² gives the bound. -/
theorem gaussian_max_entropy
    {σ : ℝ} (hσ : 0 < σ)
    (f : ℝ → ℝ)
    (hf_nn : ∀ x, 0 ≤ f x)
    (hf_sum : ∫ x, f x = 1)
    (hvar : ∫ x, x ^ 2 * f x ≤ σ ^ 2)
    (hf_int : Integrable f)
    (hflog_f_int : Integrable (fun x => f x * Real.log (f x)))
    (hflog_g_int : Integrable (fun x => f x * Real.log (gaussianPDF 0 σ x)))
    (hfg_int : Integrable (fun x => f x * Real.log (f x / gaussianPDF 0 σ x))) :
    differentialEntropy f ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * σ ^ 2) := by
  -- gaussianPDF 0 σ is positive everywhere
  have hg_pos : ∀ x : ℝ, 0 < gaussianPDF 0 σ x := by
    intro x; unfold gaussianPDF; positivity
  -- gaussianPDF 0 σ integrates to 1 (normalization)
  have hg_sum : ∫ x : ℝ, gaussianPDF 0 σ x = 1 := by
    have hrw : ∀ x : ℝ, gaussianPDF 0 σ x =
        (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-(1 / (2 * σ ^ 2)) * x ^ 2) :=
      fun x => by unfold gaussianPDF; congr 1; congr 1; ring
    simp_rw [hrw]
    rw [integral_const_mul, integral_gaussian (1 / (2 * σ ^ 2))]
    have h1 : Real.pi / (1 / (2 * σ ^ 2)) = 2 * Real.pi * σ ^ 2 := by
      field_simp [hσ.ne']
    rw [h1]
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by positivity))
  -- gaussianPDF 0 σ is integrable
  have hg_int : Integrable (gaussianPDF 0 σ) := by
    have hrw : gaussianPDF 0 σ = fun x =>
        (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-(1 / (2 * σ ^ 2)) * x ^ 2) :=
      funext fun x => by unfold gaussianPDF; congr 1; congr 1; ring
    rw [hrw]
    exact (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (2 * σ ^ 2))).const_mul _
  -- By Gibbs inequality: h(f) ≤ -∫ f log(gaussianPDF 0 σ)
  have h_gibbs := gibbs_inequality_continuous hf_nn hg_pos hf_sum hg_sum
    hf_int hg_int hflog_f_int hflog_g_int hfg_int
  -- log(gaussianPDF 0 σ x) = -½ log(2πσ²) - x²/(2σ²)
  have hlog_g : ∀ x : ℝ, Real.log (gaussianPDF 0 σ x) =
      -(1/2) * Real.log (2 * Real.pi * σ ^ 2) - x ^ 2 / (2 * σ ^ 2) := by
    intro x
    have hx : gaussianPDF 0 σ x = (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ *
        Real.exp (-(1 / (2 * σ ^ 2)) * x ^ 2) := by
      unfold gaussianPDF; congr 1; congr 1; ring
    rw [hx, Real.log_mul
        (inv_pos.mpr (Real.sqrt_pos_of_pos (by positivity))).ne'
        (Real.exp_ne_zero _),
      Real.log_inv, Real.log_sqrt (by positivity), Real.log_exp]
    ring
  -- The upper bound: -∫ f log g ≤ ½ log(2πeσ²)
  suffices h : -∫ x, f x * Real.log (gaussianPDF 0 σ x) ≤
      (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * σ ^ 2) by linarith
  -- Rewrite integrand using hlog_g
  have h_rw : (fun x => f x * Real.log (gaussianPDF 0 σ x)) =
      (fun x => -(1/2) * Real.log (2 * Real.pi * σ ^ 2) * f x +
        (-1 / (2 * σ ^ 2)) * (x ^ 2 * f x)) := by
    funext x; rw [hlog_g x]; ring
  rw [h_rw] at hflog_g_int ⊢
  -- Split: -∫ (A * f + B * x²f) = -A * ∫f - B * ∫ x²f
  have hint1 : Integrable (fun x => -(1/2) * Real.log (2 * Real.pi * σ ^ 2) * f x) :=
    hf_int.const_mul _
  have hint2 : Integrable (fun x => (-1 / (2 * σ ^ 2)) * (x ^ 2 * f x)) := by
    have h : (fun x => -1 / (2 * σ ^ 2) * (x ^ 2 * f x)) =
        (fun x => (-(1/2) * Real.log (2 * Real.pi * σ ^ 2) * f x +
          -1 / (2 * σ ^ 2) * (x ^ 2 * f x)) -
          (-(1/2) * Real.log (2 * Real.pi * σ ^ 2) * f x)) :=
      funext fun x => by ring
    rw [h]; exact hflog_g_int.sub hint1
  rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul, hf_sum]
  -- Now: -(A * 1 + B * ∫ x²f) ≤ ½ log(2πeσ²)
  -- i.e., ½ log(2πσ²) + (1/(2σ²)) * ∫ x²f ≤ ½ log(2πeσ²)
  have hbound : (1 / 2) * Real.log (2 * Real.pi * σ ^ 2) +
      (1 / (2 * σ ^ 2)) * ∫ x, x ^ 2 * f x ≤
      (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * σ ^ 2) := by
    have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
    have h_log_eq : (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * σ ^ 2) =
        (1 / 2) * Real.log (2 * Real.pi * σ ^ 2) + 1 / 2 := by
      rw [show 2 * Real.pi * Real.exp 1 * σ ^ 2 = 2 * Real.pi * σ ^ 2 * Real.exp 1 from by ring]
      rw [Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
      ring
    rw [h_log_eq]
    have hvar2 : (1 / (2 * σ ^ 2)) * ∫ x, x ^ 2 * f x ≤ 1 / 2 := by
      have hc : (0 : ℝ) ≤ 1 / (2 * σ ^ 2) := div_nonneg one_pos.le (by positivity)
      have h1 := mul_le_mul_of_nonneg_left hvar hc
      have h2 : (1 / (2 * σ ^ 2)) * σ ^ 2 = 1 / 2 := by field_simp
      linarith
    linarith
  have hring : -(-(1 / 2) * Real.log (2 * Real.pi * σ ^ 2) * 1 +
      -1 / (2 * σ ^ 2) * ∫ x, x ^ 2 * f x) =
      (1 / 2) * Real.log (2 * Real.pi * σ ^ 2) +
      (1 / (2 * σ ^ 2)) * ∫ x, x ^ 2 * f x := by ring
  linarith [hbound]

end DifferentialEntropy
