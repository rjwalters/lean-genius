/-
  CauchySchwarzIntegralOQ01OQ03: Complex-Valued Hölder via NNNorm

  Answers OQ-03: Can the complex-valued Hölder inequality be stated and
  proved using the nnnorm approach?

  **YES** — the nnnorm approach works for ℂ (and any NormedField) via
  the same proof structure as for ℝ:
    ‖f(a) * g(a)‖₊ = ‖f(a)‖₊ * ‖g(a)‖₊   [nnnorm_mul in NormedField]

  Key insight: The parent proof (OQ-01) uses `nnnorm_mul` which holds in
  any NormedField. Since ℂ is a NormedField, the identical tactic proof
  applies. Moreover, we can state a single unified theorem for ANY
  NormedField that recovers both the ℝ and ℂ cases as special instances.

  This unification is the mathematical content of OQ-03: the nnnorm
  approach is not just a trick for ℝ, but the correct framework that
  works uniformly across all normed fields.

  ## Proof Structure

  1. holder_normedfield_lintegral: unified Hölder for any NormedField
     (uses: nnnorm_mul, holder_nnreal_lintegral, AEMeasurable.nnnorm)
  2. holder_complex_lintegral: complex specialization (from 1)
  3. cauchy_schwarz_complex_from_holder: p=q=2 complex C-S (from 2)
  4. holder_real_from_normedfield: shows ℝ-version is subsumed (from 1)
  5. cauchy_schwarz_inner_complex_nnnorm: algebraic C-S in nnnorm form

  ## Why This Answers OQ-03

  The OQ asks whether the nnnorm approach extends to ℂ. The answer is:
  it extends to ALL NormedFields simultaneously, with identical proofs.
  The crucial lemma is `nnnorm_mul : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊`, which
  holds in any NormedField (in fact any NormedRing).
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic
import Proofs.CauchySchwarzIntegralOQ01

noncomputable section

open MeasureTheory ENNReal NNReal Real

namespace ComplexHolderNNNorm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

open HolderGeneralizesCS

/-
## Part 1: Unified Hölder for Any NormedField

The key observation: `nnnorm_mul` holds in any NormedField (since multiplication
is multiplicative for the norm in a NormedField), so the nnnorm approach
applies uniformly to ℝ, ℂ, ℚ_p, and any other normed field.
-/

/-- Hölder's inequality for functions valued in any NormedField, via the nnnorm approach.

    For conjugate exponents p, q (1/p + 1/q = 1), any NormedField E, and
    AEMeasurable functions f, g : α → E:
      ∫⁻ ‖f·g‖₊ dμ ≤ (∫⁻ ‖f‖₊^p dμ)^{1/p} · (∫⁻ ‖g‖₊^q dμ)^{1/q}

    **This is the main result of OQ-03**: the nnnorm approach works for any
    NormedField, not just ℝ. The key is nnnorm_mul : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊,
    which holds in any NormedField (via NormedRing → NonUnitalNormedRing). -/
theorem holder_normedfield_lintegral {p q : ℝ} (hpq : p.HolderConjugate q)
    {E : Type*} [NormedField E] [MeasurableSpace E] [BorelSpace E]
    {f g : α → E} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, (‖f a * g a‖₊ : ℝ≥0∞) ∂μ ≤
      (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) *
      (∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) := by
  -- nnnorm is multiplicative in any NormedField:  ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
  have hmul : ∀ a, (‖f a * g a‖₊ : ℝ≥0∞) = (‖f a‖₊ : ℝ≥0∞) * ‖g a‖₊ := fun a => by
    simp only [← ENNReal.coe_mul, nnnorm_mul]
  simp_rw [hmul]
  -- Reduce to the NNReal-valued Hölder (established in OQ-01)
  exact holder_nnreal_lintegral hpq hf.nnnorm hg.nnnorm

/-
## Part 2: Complex-Valued Hölder as a Special Case

ℂ is a NormedField, so `holder_normedfield_lintegral` applies directly.
The complex version is not a new proof — it is an instance of the general theorem.
-/

/-- Hölder's inequality for complex-valued functions via the nnnorm approach.
    This is the direct specialization of `holder_normedfield_lintegral` to E = ℂ.

    For conjugate exponents p, q (1/p + 1/q = 1) and AEMeasurable f, g : α → ℂ:
      ∫⁻ ‖f·g‖₊ dμ ≤ (∫⁻ ‖f‖₊^p dμ)^{1/p} · (∫⁻ ‖g‖₊^q dμ)^{1/q} -/
theorem holder_complex_lintegral {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℂ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, (‖f a * g a‖₊ : ℝ≥0∞) ∂μ ≤
      (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) *
      (∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) :=
  holder_normedfield_lintegral hpq hf hg

/-- Cauchy-Schwarz for complex-valued functions: the p=q=2 case of complex Hölder.
    ∫⁻ ‖f·g‖₊ dμ ≤ (∫⁻ ‖f‖₊² dμ)^{1/2} · (∫⁻ ‖g‖₊² dμ)^{1/2} -/
theorem cauchy_schwarz_complex_from_holder
    {f g : α → ℂ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, (‖f a * g a‖₊ : ℝ≥0∞) ∂μ ≤
      (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
      (∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) :=
  holder_complex_lintegral holder_conj_2_2 hf hg

/-
## Part 3: Subsumption of the Real Case

ℝ is also a NormedField, so holder_normedfield_lintegral recovers
holder_real_lintegral from OQ-01 as a special case.
This demonstrates the unifying power of the nnnorm approach.
-/

/-- The real-valued Hölder inequality follows from the general NormedField version.
    This shows that OQ-01's `holder_real_lintegral` is subsumed by
    `holder_normedfield_lintegral` (the answer to OQ-03). -/
theorem holder_real_from_normedfield {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, (‖f a * g a‖₊ : ℝ≥0∞) ∂μ ≤
      (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) *
      (∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) :=
  holder_normedfield_lintegral hpq hf hg

/-
## Part 4: Algebraic Cauchy-Schwarz for Complex Inner Product Spaces

In a complex Hilbert space, the Cauchy-Schwarz inequality takes the form:
  |⟪x, y⟫_ℂ| ≤ ‖x‖ · ‖y‖

The nnnorm formulation gives:
  ‖⟪x, y⟫_ℂ‖₊ ≤ ‖x‖₊ · ‖y‖₊

This connects the integral form (above) to the algebraic form in Hilbert spaces.
-/

/-- Cauchy-Schwarz for complex inner product spaces: |⟪x, y⟫_ℂ| ≤ ‖x‖ · ‖y‖ -/
theorem cauchy_schwarz_inner_complex {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x y : E) :
    ‖(inner (𝕜 := ℂ) x y : ℂ)‖ ≤ ‖x‖ * ‖y‖ :=
  norm_inner_le_norm x y

/-- NNNorm formulation of the complex inner product Cauchy-Schwarz inequality. -/
theorem cauchy_schwarz_inner_complex_nnnorm {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x y : E) :
    ‖(inner (𝕜 := ℂ) x y : ℂ)‖₊ ≤ ‖x‖₊ * ‖y‖₊ := by
  exact_mod_cast cauchy_schwarz_inner_complex x y

/-- Unified form: for RCLike fields (both ℝ and ℂ), Cauchy-Schwarz in nnnorm form. -/
theorem cauchy_schwarz_inner_rclike_nnnorm {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) :
    ‖(inner (𝕜 := 𝕜) x y : 𝕜)‖₊ ≤ ‖x‖₊ * ‖y‖₊ := by
  exact_mod_cast norm_inner_le_norm x y

/-
## Summary: Answer to OQ-03

**Q**: Can the complex-valued Hölder inequality be proved using the nnnorm approach?
**A**: YES — and more:

1. `holder_normedfield_lintegral` proves Hölder for ANY NormedField E in one theorem,
   with the same proof as the ℝ case (just using nnnorm_mul in NormedField).

2. The real case (OQ-01's `holder_real_lintegral`) is subsumed by specializing to E = ℝ.
   The complex case is the E = ℂ specialization.

3. The key lemma is `nnnorm_mul : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊`, which holds in any
   NormedField (via the NormedRing/NormedField instance hierarchy in Mathlib).

4. The algebraic Cauchy-Schwarz for complex inner products also has a clean nnnorm form,
   connecting the integral and algebraic theories.

**Philosophical point**: The nnnorm approach is "right" because it factors through ℝ≥0,
working for any NormedField where the norm is multiplicative. It avoids the need for
order structures (comparison of signs) that would restrict to ℝ.
-/

#check @holder_normedfield_lintegral
#check @holder_complex_lintegral
#check @cauchy_schwarz_complex_from_holder
#check @cauchy_schwarz_inner_complex_nnnorm

end ComplexHolderNNNorm

end
