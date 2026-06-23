/-
# Synthesis: Eliminating the `riesz_lp_surjective` Axiom — Full Lᵖ Duality
(cauchy-schwarz-integral-lp-duality-synthesis)

## Goal

The parent file `CauchySchwarzIntegralOQ01OQ01OQ02.lean` states the Lᵖ Riesz
representation for an **arbitrary** measure `μ` (1 < p < ∞) as a single axiom:

    axiom riesz_lp_surjective (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
      (hpq : p.toReal.HolderConjugate q.toReal) :
      ∀ φ : Lp ℝ p μ →L[ℝ] ℝ, ∃ g : α → ℝ, Memℒp g q μ ∧
        ∀ f, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ

This file works toward eliminating that axiom by **reducing the arbitrary-measure
case to the already-proven σ-finite case**, which is the classical strategy of
Folland, *Real Analysis* (2nd ed.), Theorem 6.16 (valid precisely because
`1 < p < ∞`).

## What is already verified (0 axioms, 0 sorries) in the dependency chain

* `RieszLpSurjectivity.riesz_lp_surjective_from_rn`  — finite-measure case
  (CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean). Radon–Nikodým + Lᵖ machinery.
* `RieszSigmaFinite.riesz_lp_surjective_sigma_finite` — **σ-finite case**
  (CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01.lean), built from the finite case by
  spanning-set localization (`localization_existence`) + an Lᵖ density extension.
* `extByZeroCLM : Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ` — the extension-by-zero
  **isometry** (CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01.lean, currently
  `private`; trivially re-exposable), together with the restriction isometry
  `eLpNorm (S.indicator f) p μ = eLpNorm f p (μ.restrict S)`.

## The remaining mathematical content: a maximality argument

For an arbitrary measure `μ` and `1 < p < ∞`, every `f ∈ Lᵖ(μ)` is supported on a
σ-finite set (Mathlib: `MemLp.aefinStronglyMeasurable` → `AEFinStronglyMeasurable`;
see `memLp_exists_sigmaFinite_support` below). The reduction goes:

1. For each measurable `S` with `μ.restrict S` σ-finite, pull `φ` back along
   `extByZeroCLM` to a functional on `Lp ℝ p (μ.restrict S)`, and apply the σ-finite
   Riesz theorem to obtain `g_S ∈ Lq(μ.restrict S)` with `‖g_S‖_q ≤ ‖φ‖`.
2. Let `c = ⨆_S ‖g_S‖_q` (bounded above by `‖φ‖`, so finite). Pick σ-finite sets
   `S_n` with `‖g_{S_n}‖_q → c`; set `T = ⋃ₙ S_n`. Then `μ.restrict T` is σ-finite
   (countable union of σ-finite pieces) and, by uniqueness of the representing
   function, `g_T` realizes the supremum: `‖g_T‖_q = c`.
3. For arbitrary `f ∈ Lᵖ(μ)`, its support `Sf` is σ-finite; put `U = T ∪ Sf`. On `U`,
   `g_U` represents `φ`. Lᵠ-norm additivity over the disjoint pieces `T` and `U \ T`
   plus maximality `‖g_U‖_q ≤ c = ‖g_T‖_q` forces `g_U = g_T` a.e. on `T` and
   `g_U = 0` a.e. on `U \ T`. Hence `φ f = ∫ f · g_U = ∫ f · g_T`, with `g_T`
   extended by `0` off `T`.

The only non-mechanical step is this maximality construction
(`riesz_representing_function_maximal` below). All other ingredients are already in
the verified chain or in Mathlib.

## Status

WORK IN PROGRESS. The bridge lemma `memLp_exists_sigmaFinite_support` is complete and
self-contained. The headline reduction `riesz_lp_surjective_general` is stated with a
single `sorry` for the maximality construction — it does **not** yet eliminate the
axiom. Do not present this as verified until the `sorry` is discharged and the file
builds under the Docker wrapper.

## References

* Folland, *Real Analysis* (2nd ed.), Theorem 6.16.
* Rudin, *Real and Complex Analysis* (3rd ed.), Theorem 6.16.
* Mathlib: `MeasureTheory.MemLp.aefinStronglyMeasurable`,
  `MeasureTheory.AEFinStronglyMeasurable.{sigmaFiniteSet, ae_eq_zero_compl, sigmaFinite_restrict}`.
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszLpDualitySynthesis

/-- **Bridge lemma.** For `0 < p < ∞`, every `f ∈ Lᵖ(μ)` is a.e. supported on a
    measurable set `S` whose restricted measure `μ.restrict S` is σ-finite: `f = 0`
    a.e. on the complement of `S`.

    This is the ingredient that reduces the *arbitrary-measure* Riesz representation
    to the *σ-finite* case, and it resolves what the earlier sigma-finite file flagged
    as a "Lean infrastructure gap": Mathlib already supplies it via
    `MemLp.aefinStronglyMeasurable`. -/
theorem memLp_exists_sigmaFinite_support
    {f : α → ℝ} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    ∃ S : Set α, MeasurableSet S ∧ SigmaFinite (μ.restrict S) ∧ f =ᵐ[μ.restrict Sᶜ] 0 := by
  have h := hf.aefinStronglyMeasurable hp0 hptop
  exact ⟨h.sigmaFiniteSet, h.measurableSet, h.sigmaFinite_restrict, h.ae_eq_zero_compl⟩

/-- **Riesz representation for Lᵖ — arbitrary measure** (`1 < p < ∞`).

    Every bounded linear functional on `Lp ℝ p μ`, for *any* measure `μ`, is
    represented by integration against some `g ∈ Lq(μ)`.

    This is the statement of the parent file's `riesz_lp_surjective` axiom, here
    presented as a theorem to be discharged from `riesz_lp_surjective_sigma_finite`
    via the maximality argument documented at the top of this file.

    REMAINING WORK: the `sorry` below is the maximality construction
    (`riesz_representing_function_maximal`). It is HARD (classical, Folland 6.16),
    not OPEN. All supporting infrastructure already exists in the verified chain. -/
theorem riesz_lp_surjective_general
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  sorry

end RieszLpDualitySynthesis

end
