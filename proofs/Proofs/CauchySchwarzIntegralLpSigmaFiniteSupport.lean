/-
  σ-finite support of Lᵖ functions — foundational brick of the σ-finite-support
  reduction toward eliminating the `riesz_lp_surjective` axiom.

  Context (synthesis `cauchy-schwarz-integral-lp-duality-synthesis`):
  The base file `CauchySchwarzIntegralOQ01OQ01OQ02.lean` axiomatizes the hard
  (surjectivity) direction of the Riesz representation theorem for `(Lᵖ)*`,
  `1 < p < ∞`, over an ARBITRARY measure `μ`:

      axiom riesz_lp_surjective … : ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
        ∃ g, MemLp g q μ ∧ ∀ f, φ f = ∫ a, f a * g a ∂μ

  The proven surjectivity results — `riesz_lp_surjective_from_rn` (finite measure)
  and `riesz_lp_surjective_sigma_finite` (σ-finite measure) — both require a
  finiteness instance on `μ`.  Closing the general axiom uses the classical
  **σ-finite-support reduction**: for `1 < p < ∞` every bounded functional on
  `Lᵖ(μ)` is carried by a single σ-finite set, so the σ-finite case applies there
  and the functional vanishes on the complement.

  This file discharges the *foundational* step of that reduction — the per-function
  statement that **every `Lᵖ` function (`0 < p < ∞`) is a.e. supported on a σ-finite
  measurable set** — as a fully verified (0-axiom, 0-sorry) consequence of Mathlib's
  `MemLp.aefinStronglyMeasurable` and `AEFinStronglyMeasurable.exists_set_sigmaFinite`.

  Remaining steps toward eliminating the axiom (documented for the next session):
    (2) COMMON CARRIER: extract a *single* σ-finite set carrying an entire functional
        `φ` from a norming sequence `φ(fₙ) → ‖φ‖`.  Needs σ-finiteness of a countable
        union of σ-finite-restricted sets (disjointification: Mathlib has only the
        binary `SigmaFinite (μ.restrict (s ∪ t))` instance, so the countable version
        must be built from `FiniteSpanningSetsIn` / `sigmaFinite_of_le`).
    (3) VANISHING OFF THE CARRIER: `φ` is zero on functions supported off the carrier
        (disjoint-support convexity: `‖fₙ + t·h‖ᵖ = ‖fₙ‖ᵖ + tᵖ‖h‖ᵖ` beats `‖φ‖` for
        small `t` when `p > 1` unless `φ h = 0`).
    (4) Restrict `μ` to the carrier, apply `riesz_lp_surjective_sigma_finite`, and
        extend the representing `g` by `0`.
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal

namespace RieszLpReduction

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- **σ-finite support of an `Lᵖ` function (`0 < p < ∞`).**  For `f : Lp ℝ p μ` with
`p ≠ 0` and `p ≠ ∞` there is a measurable set `t` such that `f` vanishes a.e. on the
complement `tᶜ` and `μ` is σ-finite on `t`.  This is the per-function core of the
σ-finite-support reduction used to eliminate the general-measure `riesz_lp_surjective`
axiom.  Verified 0-axiom via `MemLp.aefinStronglyMeasurable` +
`AEFinStronglyMeasurable.exists_set_sigmaFinite`. -/
theorem exists_sigmaFinite_support (hp0 : p ≠ 0) (hptop : p ≠ ∞) (f : Lp ℝ p μ) :
    ∃ t : Set α, MeasurableSet t ∧ (f : α → ℝ) =ᵐ[μ.restrict tᶜ] 0 ∧
      SigmaFinite (μ.restrict t) :=
  ((Lp.memLp f).aefinStronglyMeasurable hp0 hptop).exists_set_sigmaFinite

/-- The canonical σ-finite carrier `sigmaFiniteSet` of an `Lᵖ` function is measurable
(0-axiom); a convenience projection for the common-carrier construction (step 2). -/
theorem measurableSet_sigmaFiniteSet (hp0 : p ≠ 0) (hptop : p ≠ ∞) (f : Lp ℝ p μ) :
    MeasurableSet ((Lp.memLp f).aefinStronglyMeasurable hp0 hptop).sigmaFiniteSet :=
  ((Lp.memLp f).aefinStronglyMeasurable hp0 hptop).measurableSet

/-- On the complement of its canonical σ-finite carrier, an `Lᵖ` function vanishes a.e.
(0-axiom). -/
theorem ae_eq_zero_compl_sigmaFiniteSet (hp0 : p ≠ 0) (hptop : p ≠ ∞) (f : Lp ℝ p μ) :
    (f : α → ℝ) =ᵐ[μ.restrict
      ((Lp.memLp f).aefinStronglyMeasurable hp0 hptop).sigmaFiniteSetᶜ] 0 :=
  ((Lp.memLp f).aefinStronglyMeasurable hp0 hptop).ae_eq_zero_compl

end RieszLpReduction
