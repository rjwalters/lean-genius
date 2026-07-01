import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-
# Hölder's Inequality: the Bunyakovsky–Schwarz Bridge beyond L²

## What This Proves
This file answers the open question raised by the L² Bunyakovsky–Schwarz
gallery entry (`CauchySchwarzIntegral.lean`):

> *Can the "inner-product = integral" bridge extend to Lᵖ spaces for p ≠ 2?*

The answer is **yes**, and the correct generalization is **Hölder's inequality**.
The L² result

  |∫ f·g dμ| ≤ ‖f‖_{L²} · ‖g‖_{L²}

is exactly the diagonal case `p = q = 2` of the family

  |∫ f·g dμ| ≤ (∫ |f|ᵖ dμ)^{1/p} · (∫ |g|ᵍ dμ)^{1/q},   1/p + 1/q = 1.

The bridge that made the L² case work was that L²(μ) is its own dual (an
inner-product space). For p ≠ 2 the Riesz duality is between Lᵖ and its
conjugate Lᵍ, and Hölder's inequality is precisely the pairing bound. The
symmetric self-pairing of Cauchy–Schwarz is the single fixed point `p = q = 2`
of the conjugation `p ↦ p/(p-1)`.

## Main Results
* `holder_integral_abs` — signed Hölder inequality for real-valued functions:
  the absolute value of the pairing `∫ f·g` is bounded by the product of the
  Lᵖ and Lᵍ integrals. This is the genuine extension of the L² bridge to all
  conjugate exponents (Mathlib only ships the nonnegative and norm forms).
* `holder_integral_abs_L2` — the L² special case in `Real.sqrt` form,
  recovering the shape of the parent gallery's `bunyakovsky_schwarz_abs`.
* `holder_recovers_cauchy_schwarz` — the squared Cauchy–Schwarz integral
  inequality `(∫ f·g)² ≤ (∫ f²)·(∫ g²)` obtained as the `p = q = 2` case,
  proving the parent theorem is literally a specialization of Hölder.
* `holder_integral_abs_symm` — the pairing bound is symmetric under swapping
  `(f, p) ↔ (g, q)`, reflecting `p.HolderConjugate q ↔ q.HolderConjugate p`.

## References
Bunyakovsky (1859), Schwarz (1885) for the L² case; Hölder (1889) for the
general conjugate-exponent inequality.
-/

noncomputable section

open MeasureTheory Real

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace HolderIntegralBridge

/-- **Signed Hölder integral inequality.** For real-valued `f ∈ Lᵖ` and
`g ∈ Lᵍ` with conjugate exponents `p, q`, the pairing integral `∫ f·g` is
controlled by the product of the `Lᵖ` and `Lᵍ` integrals:

  `|∫ f·g dμ| ≤ (∫ |f|ᵖ dμ)^{1/p} · (∫ |g|ᵍ dμ)^{1/q}`.

Unlike Mathlib's `integral_mul_le_Lp_mul_Lq_of_nonneg` (which assumes `f, g ≥ 0`)
and `integral_mul_norm_le_Lp_mul_Lq` (bounding `∫ ‖f‖·‖g‖`), this handles
arbitrary *signed* functions by bounding the signed pairing directly — the exact
generalization of the L² bridge `|∫ f·g| ≤ ‖f‖·‖g‖`. -/
theorem holder_integral_abs {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    |∫ a, f a * g a ∂μ| ≤
      (∫ a, |f a| ^ p ∂μ) ^ (1 / p) * (∫ a, |g a| ^ q ∂μ) ^ (1 / q) := by
  calc |∫ a, f a * g a ∂μ|
      ≤ ∫ a, |f a * g a| ∂μ := abs_integral_le_integral_abs
    _ = ∫ a, |f a| * |g a| ∂μ := by simp_rw [abs_mul]
    _ ≤ (∫ a, |f a| ^ p ∂μ) ^ (1 / p) * (∫ a, |g a| ^ q ∂μ) ^ (1 / q) := by
        have h := integral_mul_norm_le_Lp_mul_Lq hpq hf hg
        simpa only [Real.norm_eq_abs] using h

/-- **L² special case in `sqrt` form.** Recovers the shape of the parent
gallery's `bunyakovsky_schwarz_abs`: for `f, g ∈ L²`,

  `|∫ f·g dμ| ≤ √(∫ f² dμ) · √(∫ g² dμ)`.

This is `holder_integral_abs` at the fixed point `p = q = 2` of conjugation,
with the `1/2`-powers rewritten as square roots. -/
theorem holder_integral_abs_L2 {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ a, f a * g a ∂μ| ≤ Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ) := by
  have h2 : (ENNReal.ofReal 2 : ENNReal) = 2 := by norm_num
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by rwa [h2]
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by rwa [h2]
  have h := holder_integral_abs (Real.HolderConjugate.two_two) hf' hg'
  -- In `h` the exponents are real powers; convert `|f|^(2:ℝ) = f^2` and match √.
  simp_rw [Real.rpow_two, sq_abs] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h

/-- **Cauchy–Schwarz as the `p = q = 2` case of Hölder.** The classical squared
integral Cauchy–Schwarz inequality

  `(∫ f·g dμ)² ≤ (∫ f² dμ) · (∫ g² dμ)`

is a specialization of the general Hölder inequality. This proves the parent
gallery theorem `bunyakovsky_schwarz_sq` is *not* a separate result but the
diagonal restriction of the conjugate-exponent family. -/
theorem holder_recovers_cauchy_schwarz {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ a, f a * g a ∂μ) ^ 2 ≤ (∫ a, f a ^ 2 ∂μ) * (∫ a, g a ^ 2 ∂μ) := by
  have hA : 0 ≤ ∫ a, f a ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  have hB : 0 ≤ ∫ a, g a ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  have h := holder_integral_abs_L2 hf hg
  have hR : 0 ≤ Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- Square the absolute-value bound; both sides are nonnegative.
  have hsq : (∫ a, f a * g a ∂μ) ^ 2 ≤
      (Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ)) ^ 2 := by
    rw [← sq_abs (∫ a, f a * g a ∂μ)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc (∫ a, f a * g a ∂μ) ^ 2
      ≤ (Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ)) ^ 2 := hsq
    _ = (∫ a, f a ^ 2 ∂μ) * (∫ a, g a ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- **Symmetry of the Hölder pairing bound.** Swapping the two functions and
their conjugate exponents leaves the inequality invariant, reflecting the
symmetry `p.HolderConjugate q ↔ q.HolderConjugate p` of the conjugation. -/
theorem holder_integral_abs_symm {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    |∫ a, g a * f a ∂μ| ≤
      (∫ a, |g a| ^ q ∂μ) ^ (1 / q) * (∫ a, |f a| ^ p ∂μ) ^ (1 / p) :=
  holder_integral_abs hpq.symm hg hf

-- Summary checks
#check @holder_integral_abs
#check @holder_integral_abs_L2
#check @holder_recovers_cauchy_schwarz
#check @holder_integral_abs_symm

end HolderIntegralBridge

end
