/-
# Hölder Inequality — eLpNorm-based Formalization for NormedField (OQ-03-OQ-01)

## Problem: cauchy-schwarz-integral-oq-01-oq-03-oq-01

## Open Question
"Can the Hölder inequality be stated using Mathlib's `eLpNorm` API for functions
valued in any NormedField 𝕜?"

## Answer: YES

OQ-03 (`CauchySchwarzIntegralOQ01OQ03.lean`) proved Hölder at the lintegral level:
  `∫⁻ ‖fg‖₊ dμ ≤ (∫⁻ ‖f‖₊^p dμ)^(1/p) · (∫⁻ ‖g‖₊^q dμ)^(1/q)`

This file lifts to the `eLpNorm` API — the standard interface for Lp spaces — via:
  `eLpNorm_eq_lintegral_rpow_enorm` (Mathlib: eLpNorm f p μ = (∫⁻ ‖f‖ₑ^p.toReal)^(1/p.toReal))

## Results

1. `holder_normedField_eLpNorm` — Hölder in eLpNorm form for any NormedField 𝕜
2. `memLp_mul_of_memLp_ofReal` — Product membership: f ∈ Lp, g ∈ Lq ⟹ fg ∈ L1
3. `holder_complex_eLpNorm` — Complex specialization
4. `cauchy_schwarz_complex_eLpNorm` — CS at p=q=2 in eLpNorm form

## Why This Matters

The eLpNorm API is the standard Lp space interface in Mathlib.
`Memℒp f p μ` = `AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞`.
The product membership theorem (`memLp_mul_of_memLp_ofReal`) is the most
practically useful consequence of Hölder's inequality.

## Status: 0 sorries, 0 axioms
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal NNReal Real

namespace HolderELpNorm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

-- ============================================================================
-- Part 1: Bridge Lemma — eLpNorm ↔ lintegral
-- ============================================================================

/-- For `p > 0` (as a real number), the eLpNorm API equals the Lp lintegral.
    Uses `eLpNorm_eq_lintegral_rpow_enorm` (‖·‖ₑ is `enorm = nnnorm` as ENNReal). -/
private lemma eLpNorm_ofReal_eq {p : ℝ} (hp : 0 < p)
    {E : Type*} [NormedAddCommGroup E] {f : α → E} :
    eLpNorm f (ENNReal.ofReal p) μ =
    (∫⁻ a, ‖f a‖ₑ ^ p ∂μ) ^ (1 / p) := by
  have h0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm h0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le]

-- ============================================================================
-- Part 2: Hölder in eLpNorm Form
-- ============================================================================

/-- **Hölder's Inequality in eLpNorm Form for NormedField 𝕜**

    For Hölder conjugate exponents p, q (1/p + 1/q = 1, p > 1) and
    AE-measurable f, g : α → 𝕜:

      eLpNorm (f·g) 1 μ ≤ eLpNorm f (ENNReal.ofReal p) μ · eLpNorm g (ENNReal.ofReal q) μ

    Proof: Bridge via `eLpNorm_ofReal_eq` to the lintegral form, then apply
    `ENNReal.lintegral_mul_le_Lp_mul_Lq` after factoring `nnnorm_mul`. -/
theorem holder_normedField_eLpNorm
    {𝕜 : Type*} [NormedField 𝕜]
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {f g : α → 𝕜} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (fun a => f a * g a) 1 μ ≤
    eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ := by
  -- Bridge eLpNorm to lintegral form
  rw [eLpNorm_one_eq_lintegral_nnnorm,
      eLpNorm_ofReal_eq hpq.pos,
      eLpNorm_ofReal_eq hpq.symm.pos]
  -- Factor nnnorm via NormedField multiplicativity: ‖fg‖₊ = ‖f‖₊ · ‖g‖₊
  simp_rw [nnnorm_mul, ENNReal.coe_mul]
  -- Apply ENNReal Hölder (‖·‖ₑ = (‖·‖₊ : ℝ≥0∞) definitionally, exact closes)
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    hf.nnnorm.coe_nnreal_ennreal hg.nnnorm.coe_nnreal_ennreal

-- ============================================================================
-- Part 3: Product Membership in L1 — the Practical Consequence
-- ============================================================================

/-- **Product Membership via Hölder**: If f ∈ Lp and g ∈ Lq (conjugate exponents),
    then f·g ∈ L1.

    This is the most directly useful consequence of Hölder's inequality:
    the product of an Lp and Lq function is integrable. -/
theorem memLp_mul_of_memLp_ofReal
    {𝕜 : Type*} [NormedField 𝕜]
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {f g : α → 𝕜}
    (hf : Memℒp f (ENNReal.ofReal p) μ) (hg : Memℒp g (ENNReal.ofReal q) μ) :
    Memℒp (fun a => f a * g a) 1 μ := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  calc eLpNorm (fun a => f a * g a) 1 μ
      ≤ eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ :=
          holder_normedField_eLpNorm hpq hf.1.aemeasurable hg.1.aemeasurable
      _ < ∞ := ENNReal.mul_lt_top hf.2.ne hg.2.ne

-- ============================================================================
-- Part 4: Real and Complex Specializations
-- ============================================================================

/-- Hölder for real-valued functions in eLpNorm form. -/
theorem holder_real_eLpNorm
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {f g : α → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (fun a => f a * g a) 1 μ ≤
    eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ :=
  holder_normedField_eLpNorm hpq hf hg

/-- Hölder for complex-valued functions in eLpNorm form. -/
theorem holder_complex_eLpNorm
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {f g : α → ℂ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (fun a => f a * g a) 1 μ ≤
    eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ :=
  holder_normedField_eLpNorm hpq hf hg

/-- Cauchy-Schwarz (p=q=2) for complex functions in eLpNorm form. -/
theorem cauchy_schwarz_complex_eLpNorm
    {f g : α → ℂ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (fun a => f a * g a) 1 μ ≤
    eLpNorm f (ENNReal.ofReal 2) μ * eLpNorm g (ENNReal.ofReal 2) μ := by
  apply holder_complex_eLpNorm _ hf hg
  have h := Real.HolderConjugate.conjExponent (p := 2) (by norm_num : (1 : ℝ) < 2)
  have heq : Real.conjExponent 2 = 2 := by simp [Real.conjExponent]; norm_num
  rwa [heq] at h

-- ============================================================================
-- Part 5: Numerical Verification
-- ============================================================================

-- Verify the 2-2 conjugate pair satisfies HolderConjugate
example : Real.HolderConjugate 2 2 := by
  have h := Real.HolderConjugate.conjExponent (p := 2) (by norm_num : (1 : ℝ) < 2)
  have heq : Real.conjExponent 2 = 2 := by simp [Real.conjExponent]; norm_num
  rwa [heq] at h

-- Verify bridge: ENNReal.ofReal 2 → the usual 2
example : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num

/-
## Summary

**Answer to OQ-03-OQ-01**: YES. Hölder holds in eLpNorm form for any NormedField 𝕜.

**Relationship to OQ-03:**
- OQ-03 (`holder_normedField_lintegral`): lintegral level, using `∫⁻` notation
- OQ-03-OQ-01 (`holder_normedField_eLpNorm`): eLpNorm level, using standard Lp API
- Bridge: `eLpNorm_ofReal_eq` connects the two formulations

**New contribution (beyond OQ-03):**
The product membership theorem `memLp_mul_of_memLp_ofReal` is the most practically
useful form of Hölder's inequality: it shows fg ∈ L1 whenever f ∈ Lp and g ∈ Lq.

**Proof structure:**
1. `nnnorm_mul` (NormedField): ‖fg‖₊ = ‖f‖₊ · ‖g‖₊
2. `ENNReal.lintegral_mul_le_Lp_mul_Lq` (Mathlib): lintegral Hölder
3. `eLpNorm_ofReal_eq` (bridge via `eLpNorm_eq_lintegral_rpow_enorm`): eLpNorm ↔ lintegral
4. `‖·‖ₑ = (‖·‖₊ : ℝ≥0∞)` definitionally — `exact` closes the Hölder goal
5. Combine to get eLpNorm Hölder → product Memℒp
-/

end HolderELpNorm

end
