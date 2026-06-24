/-
  Quantitative Paley–Zygmund Inequality in the MeasureTheory.Lp Setting

  This file recasts the quantitative Paley–Zygmund inequality (proved over a
  finite Finset model in `ProbMethodSecondMomentOQ01.lean`) into Mathlib's
  native measure-theoretic framework, over a genuine probability space and
  Bochner integrals.

  For a nonnegative random variable `X ∈ L²(μ)` on a probability space and a
  threshold `0 ≤ θ ≤ 1`, the probability that `X` exceeds the fraction `θ` of
  its mean is bounded below:

      μ({X > θ · 𝔼X}) · 𝔼[X²]  ≥  (1 - θ)² · (𝔼X)².

  Equivalently, when `𝔼[X²] > 0`,

      μ({X > θ · 𝔼X})  ≥  (1 - θ)² · (𝔼X)² / 𝔼[X²].

  The proof follows the classical second-moment argument:
    * split  𝔼X = ∫_A X + ∫_{Aᶜ} X  with  A = {X > θ 𝔼X};
    * on `Aᶜ` we have `X ≤ θ 𝔼X`, so `∫_{Aᶜ} X ≤ θ 𝔼X`, giving `∫_A X ≥ (1-θ)𝔼X`;
    * Cauchy–Schwarz: `(∫_A X)² ≤ 𝔼[X²] · μ(A)`.

  Combining yields the bound.  The core integral Cauchy–Schwarz step is packaged
  as `sq_integral_mul_le`, derived from Mathlib's Hölder inequality for the
  conjugate pair `(2, 2)`.

  Paley–Zygmund is not currently in Mathlib; this provides a measure-theoretic
  formalization reusing only standard `MeasureTheory` / `ProbabilityTheory` API.
-/
import Mathlib

set_option linter.unusedVariables false

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMethod.SecondMoment.MeasureTheoretic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Integral Cauchy–Schwarz (squared form).**  For nonnegative `L²` functions
`f, g`, the square of the integral of their product is bounded by the product of
their second moments:

    (∫ f · g)²  ≤  (∫ f²) · (∫ g²).

This is the special case `p = q = 2` of Hölder's inequality, squared. -/
theorem sq_integral_mul_le {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : 0 ≤ᵐ[μ] f) (hgn : 0 ≤ᵐ[μ] g) :
    (∫ a, f a * g a ∂μ) ^ 2 ≤ (∫ a, f a ^ 2 ∂μ) * (∫ a, g a ^ 2 ∂μ) := by
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by rw [ENNReal.ofReal_ofNat]; exact hf
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by rw [ENNReal.ofReal_ofNat]; exact hg
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hfn hgn hf' hg'
  simp only [Real.rpow_two] at hcs
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  have hA : 0 ≤ ∫ a, f a ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  have hB : 0 ≤ ∫ a, g a ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  have hfg : 0 ≤ ∫ a, f a * g a ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hfn, hgn] with a ha hb using mul_nonneg ha hb)
  calc (∫ a, f a * g a ∂μ) ^ 2
      ≤ (Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ hfg hcs 2
    _ = (∫ a, f a ^ 2 ∂μ) * (∫ a, g a ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- **Quantitative Paley–Zygmund inequality (measure-theoretic form).**

For a nonnegative `X ∈ L²(μ)` on a probability space and `0 ≤ θ ≤ 1`:

    (1 - θ)² · (𝔼X)²  ≤  μ({X > θ 𝔼X}) · 𝔼[X²].

(Here `μ.real s = (μ s).toReal` is the real-valued measure and `∫ ω, X ω ∂μ` is
the expectation.) -/
theorem paley_zygmund [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 μ) (hXnn : 0 ≤ᵐ[μ] X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, X ω ∂μ) ^ 2
      ≤ μ.real {ω | θ * (∫ ω, X ω ∂μ) < X ω} * ∫ ω, X ω ^ 2 ∂μ := by
  set m := ∫ ω, X ω ∂μ with hm
  set A := {ω | θ * m < X ω} with hA_def
  -- `A` is the preimage of an open ray, hence measurable.
  have hA_meas : MeasurableSet A := hXm measurableSet_Ioi
  -- Integrability facts from `X ∈ L²` on a finite measure.
  have hXint : Integrable X μ := hX.integrable (by norm_num)
  have hm_nonneg : 0 ≤ m := integral_nonneg_of_ae hXnn
  -- The constant-`1` indicator of `A` lives in `L²`.
  have hg_mem : MemLp (A.indicator (fun _ => (1 : ℝ))) 2 μ :=
    memLp_indicator_const 2 hA_meas 1 (Or.inr (measure_ne_top μ A))
  have hg_nn : 0 ≤ᵐ[μ] A.indicator (fun _ => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  -- Step 1: 𝔼X = ∫_A X + ∫_{Aᶜ} X.
  have hsplit : (∫ ω in A, X ω ∂μ) + (∫ ω in Aᶜ, X ω ∂μ) = m :=
    integral_add_compl hA_meas hXint
  -- Step 2: on `Aᶜ`, `X ≤ θ 𝔼X`, so `∫_{Aᶜ} X ≤ θ 𝔼X`.
  have hcompl_le : (∫ ω in Aᶜ, X ω ∂μ) ≤ θ * m := by
    have hpt : ∀ ω ∈ Aᶜ, X ω ≤ θ * m := by
      intro ω hω
      simp only [hA_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
      exact hω
    calc (∫ ω in Aᶜ, X ω ∂μ)
        ≤ ∫ _ in Aᶜ, θ * m ∂μ :=
          setIntegral_mono_on hXint.integrableOn integrableOn_const hA_meas.compl hpt
      _ = μ.real Aᶜ * (θ * m) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * (θ * m) :=
          mul_le_mul_of_nonneg_right measureReal_le_one (mul_nonneg hθ0 hm_nonneg)
      _ = θ * m := one_mul _
  -- Step 3: hence `∫_A X ≥ (1-θ) 𝔼X`.
  have habove_ge : (1 - θ) * m ≤ ∫ ω in A, X ω ∂μ := by
    have hrw : (∫ ω in A, X ω ∂μ) = m - ∫ ω in Aᶜ, X ω ∂μ := by linarith [hsplit]
    have hexp : (1 - θ) * m = m - θ * m := by ring
    rw [hrw, hexp]; linarith [hcompl_le]
  -- Step 4: Cauchy–Schwarz `(∫_A X)² ≤ 𝔼[X²] · μ(A)`.
  have hind : (∫ ω in A, X ω ∂μ) = ∫ ω, X ω * A.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
    rw [← integral_indicator hA_meas]
    apply integral_congr_ae
    filter_upwards with ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator_of_mem, hω]
  have hsq_ind : (∫ ω, (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂μ) = μ.real A := by
    have hfun : (fun ω => (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2)
        = A.indicator (fun _ => (1 : ℝ)) := by
      funext ω; by_cases hω : ω ∈ A <;>
        simp [Set.indicator_of_mem, hω]
    rw [hfun, integral_indicator hA_meas, setIntegral_const, smul_eq_mul, mul_one]
  have hcs0 := sq_integral_mul_le hX hg_mem hXnn hg_nn
  rw [← hind, hsq_ind] at hcs0
  -- Step 5: combine.
  have h1mθ_nn : 0 ≤ (1 - θ) * m := mul_nonneg (by linarith) hm_nonneg
  have hstep : ((1 - θ) * m) ^ 2 ≤ (∫ ω in A, X ω ∂μ) ^ 2 :=
    pow_le_pow_left₀ h1mθ_nn habove_ge 2
  calc (1 - θ) ^ 2 * m ^ 2
      = ((1 - θ) * m) ^ 2 := by ring
    _ ≤ (∫ ω in A, X ω ∂μ) ^ 2 := hstep
    _ ≤ (∫ ω, X ω ^ 2 ∂μ) * μ.real A := hcs0
    _ = μ.real A * ∫ ω, X ω ^ 2 ∂μ := by ring

/-- **Probability form.**  When the second moment is positive,

    μ({X > θ 𝔼X})  ≥  (1 - θ)² · (𝔼X)² / 𝔼[X²]. -/
theorem paley_zygmund_prob [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 μ) (hXnn : 0 ≤ᵐ[μ] X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hX2pos : 0 < ∫ ω, X ω ^ 2 ∂μ) :
    (1 - θ) ^ 2 * (∫ ω, X ω ∂μ) ^ 2 / (∫ ω, X ω ^ 2 ∂μ)
      ≤ μ.real {ω | θ * (∫ ω, X ω ∂μ) < X ω} := by
  rw [div_le_iff₀ hX2pos]
  exact paley_zygmund hXm hX hXnn hθ0 hθ1

/-- **Qualitative corollary (`θ = 0`).**  The second-moment lower bound on the
probability that `X` is strictly positive:

    (𝔼X)²  ≤  μ({X > 0}) · 𝔼[X²].

In particular, if `𝔼X > 0` then `μ({X > 0}) > 0`. -/
theorem paley_zygmund_pos [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 μ) (hXnn : 0 ≤ᵐ[μ] X) :
    (∫ ω, X ω ∂μ) ^ 2 ≤ μ.real {ω | 0 < X ω} * ∫ ω, X ω ^ 2 ∂μ := by
  have h := paley_zygmund hXm hX hXnn (le_refl (0 : ℝ)) zero_le_one
  simpa using h

end ProbMethod.SecondMoment.MeasureTheoretic
