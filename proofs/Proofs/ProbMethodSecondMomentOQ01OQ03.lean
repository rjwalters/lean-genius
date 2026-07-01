/-
Paley–Zygmund inequality in Mathlib's measure-theoretic framework
(prob-method-second-moment-oq-01-oq-03).

The parent entry `prob-method-second-moment` proves the Paley–Zygmund inequality
in a *finite* (`Finset`) setting.  This file lifts it to Mathlib's general
`MeasureTheory` / `ProbabilityTheory` framework: for a non-negative random
variable `Z ∈ L²` on a probability space and `0 ≤ θ ≤ 1`,

      (1 - θ)² · E[Z]²  ≤  P(Z > θ·E[Z]) · E[Z²].

Dividing through by `E[Z²]` (when positive) recovers the classical ratio form
`P(Z > θ E[Z]) ≥ (1-θ)² E[Z]²/E[Z²]`.

Mathlib has Hölder's inequality for integrals (`integral_mul_le_Lp_mul_Lq_of_nonneg`)
and the Chebyshev/Markov machinery, but **no** packaged measure-theoretic
Paley–Zygmund inequality.  This file supplies it.

## Proof

Write `m = E[Z]` and `A = {Z > θ m}`.  The pointwise truncation bound

      Z ω ≤ θ m + Z ω · 𝟙_A(ω)          (for every ω)

integrates (using `μ` a probability measure) to `m ≤ θ m + E[Z · 𝟙_A]`, i.e.
`(1-θ) m ≤ E[Z · 𝟙_A]`.  Cauchy–Schwarz (Hölder with `p = q = 2`) gives
`E[Z · 𝟙_A] ≤ √(E[Z²]) · √(μ A)`.  Squaring the resulting non-negative
inequality yields `(1-θ)² m² ≤ μ(A) · E[Z²]`.

## Main result

* `paley_zygmund_measure` — the measure-theoretic Paley–Zygmund inequality.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory
open scoped ENNReal

namespace ProbMethodSecondMomentOQ01OQ03

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Helper: for `0 ≤ x`, squaring the real square root cancels: `(x ^ (1/2))² = x`. -/
private lemma rpow_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1/2 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast (x ^ (1/2 : ℝ)) 2, ← Real.rpow_mul hx]
  norm_num

/-- **Paley–Zygmund inequality (measure-theoretic form).**

For a probability measure `μ`, a measurable non-negative random variable
`Z ∈ L²(μ)`, and `0 ≤ θ ≤ 1`,
`(1 - θ)² · E[Z]² ≤ P(Z > θ·E[Z]) · E[Z²]`. -/
theorem paley_zygmund_measure
    [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZmeas : Measurable Z) (hZ : 0 ≤ᵐ[μ] Z) (hL2 : MemLp Z 2 μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2
      ≤ (μ {ω | θ * (∫ ω, Z ω ∂μ) < Z ω}).toReal * (∫ ω, (Z ω) ^ 2 ∂μ) := by
  set m : ℝ := ∫ ω, Z ω ∂μ with hm_def
  -- Basic facts.
  have hm0 : 0 ≤ m := integral_nonneg_of_ae hZ
  have hθm0 : 0 ≤ θ * m := mul_nonneg hθ0 hm0
  have hZint : Integrable Z μ := hL2.integrable one_le_two
  -- The threshold set and its indicator.
  set A : Set Ω := {ω | θ * m < Z ω} with hA_def
  have hA : MeasurableSet A := hZmeas measurableSet_Ioi
  set g : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hg_def
  have hg_nonneg : 0 ≤ᵐ[μ] g :=
    Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  -- `Z · g = 𝟙_A · Z`, hence integrable.
  have hZg_eq : (fun ω => Z ω * g ω) = A.indicator Z := by
    funext ω
    by_cases h : ω ∈ A
    · simp [hg_def, Set.indicator_of_mem h]
    · simp [hg_def, Set.indicator_of_notMem h]
  have hZg_int : Integrable (fun ω => Z ω * g ω) μ := by
    rw [hZg_eq]; exact hZint.indicator hA
  -- Pointwise truncation bound: `Z ω ≤ θ m + Z ω · g ω`.
  have hbound : ∀ ω, Z ω ≤ θ * m + Z ω * g ω := by
    intro ω
    by_cases h : θ * m < Z ω
    · have hmem : ω ∈ A := h
      simp only [hg_def, Set.indicator_of_mem hmem, mul_one]
      linarith
    · have hmem : ω ∉ A := h
      simp only [hg_def, Set.indicator_of_notMem hmem, mul_zero, add_zero]
      linarith
  -- Integrate the bound.
  have hconst_int : Integrable (fun _ : Ω => θ * m) μ := integrable_const _
  have hrhs_int : Integrable (fun ω => θ * m + Z ω * g ω) μ := hconst_int.add hZg_int
  have hint_le : m ≤ θ * m + ∫ ω, Z ω * g ω ∂μ := by
    have h1 : m ≤ ∫ ω, (θ * m + Z ω * g ω) ∂μ :=
      integral_mono_ae hZint hrhs_int (Filter.Eventually.of_forall hbound)
    rwa [integral_add hconst_int hZg_int, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul] at h1
  have hstep1 : (1 - θ) * m ≤ ∫ ω, Z ω * g ω ∂μ := by linarith
  -- Cauchy–Schwarz (Hölder, p = q = 2).
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨one_lt_two, by norm_num⟩
  have hL2' : MemLp Z (ENNReal.ofReal 2) μ := by rw [ENNReal.ofReal_ofNat]; exact hL2
  have hgL2' : MemLp g (ENNReal.ofReal 2) μ := (memLp_const (1 : ℝ)).indicator hA
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hZ hg_nonneg hL2' hgL2'
  -- Rewrite the rpow exponents `^ (2:ℝ)` back to `^ (2:ℕ)`.
  have hexp : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ 2 := by
    intro y; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hexp] at hCS
  -- `∫ g² = ∫ g = μ(A).toReal`.
  have hg_sq : (fun ω => g ω ^ 2) = g := by
    funext ω
    by_cases h : ω ∈ A
    · simp [hg_def, Set.indicator_of_mem h]
    · simp [hg_def, Set.indicator_of_notMem h]
  have hg_int_eq : ∫ ω, g ω ^ 2 ∂μ = (μ A).toReal := by
    rw [hg_sq, hg_def, integral_indicator_const _ hA, smul_eq_mul, mul_one, measureReal_def]
  rw [hg_int_eq] at hCS
  -- Abbreviations for the two non-negative quantities.
  set S : ℝ := ∫ ω, Z ω ^ 2 ∂μ with hS_def
  set T : ℝ := (μ A).toReal with hT_def
  have hS0 : 0 ≤ S := integral_nonneg fun ω => sq_nonneg _
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  -- Now `hCS : ∫ Z·g ≤ S ^ (1/2) * T ^ (1/2)`.
  have hstep2 : (1 - θ) * m ≤ S ^ (1/2 : ℝ) * T ^ (1/2 : ℝ) := le_trans hstep1 hCS
  have hlhs0 : 0 ≤ (1 - θ) * m := mul_nonneg (by linarith) hm0
  -- Square both sides.
  have hrhs : (S ^ (1/2 : ℝ) * T ^ (1/2 : ℝ)) ^ 2 = S * T := by
    rw [mul_pow, rpow_half_sq hS0, rpow_half_sq hT0]
  have hsq := pow_le_pow_left₀ hlhs0 hstep2 2
  rw [hrhs] at hsq
  -- `((1-θ) m)² = (1-θ)² m²` and conclude.
  calc (1 - θ) ^ 2 * m ^ 2 = ((1 - θ) * m) ^ 2 := by rw [mul_pow]
    _ ≤ S * T := hsq
    _ = T * S := mul_comm S T
