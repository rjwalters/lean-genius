import Mathlib

/-
# Lebesgue Measure — OQ-05: Radon–Nikodym Theorem for σ-finite Measures

## Research Problem: lebesgue-measure-oq-05

The **Radon–Nikodym theorem** is the cornerstone linking absolute continuity of
measures to densities (the abstract "dμ/dν"). The classical statement for σ-finite
measures: if `μ ≪ ν` and both are σ-finite, then there is a measurable density
`f : α → ℝ≥0∞` such that `μ = ν.withDensity f`, the density is unique `ν`-a.e., and
it satisfies the integral characterization `∫⁻ x in s, f x ∂ν = μ s` for every
measurable set `s`.

This file packages Mathlib's Lebesgue-decomposition machinery (`Measure.rnDeriv`,
`Measure.withDensity`, `HaveLebesgueDecomposition`) into the classical Radon–Nikodym
statement for σ-finite measures, together with:
1. measurability of the Radon–Nikodym derivative,
2. the canonical density (`μ.rnDeriv ν` is a density for `μ` w.r.t. `ν`),
3. existence of a measurable density,
4. the integral characterization over measurable sets,
5. the total-mass specialization,
6. uniqueness of the density `ν`-a.e.,
7. the general Lebesgue decomposition (no absolute continuity assumed):
   `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`.

## Honest scope

This is a **formalization** entry: every result is obtained by assembling existing
Mathlib lemmas. The mathematical content (the theorem itself) is due to Radon (1913)
and Nikodym (1930) and is already available in Mathlib; the contribution here is a
clean, self-contained statement of the σ-finite classical package for the gallery.

Tags: measure-theory, radon-nikodym, sigma-finite, density, lebesgue-decomposition
-/

open MeasureTheory
open scoped ENNReal

namespace LebesgueRadonNikodym

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- **Measurability of the Radon–Nikodym derivative.** -/
theorem rnDeriv_measurable (μ ν : Measure α) : Measurable (μ.rnDeriv ν) :=
  Measure.measurable_rnDeriv μ ν

/-- **Radon–Nikodym (canonical witness).** For σ-finite `μ ≪ ν`, the Radon–Nikodym
derivative `μ.rnDeriv ν` is a density for `μ` with respect to `ν`. -/
theorem rnDeriv_isDensity [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    ν.withDensity (μ.rnDeriv ν) = μ :=
  Measure.withDensity_rnDeriv_eq μ ν h

/-- **Radon–Nikodym (existence).** For σ-finite `μ ≪ ν` there exists a measurable
density `f` with `μ = ν.withDensity f`. -/
theorem exists_density [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    ∃ f : α → ℝ≥0∞, Measurable f ∧ ν.withDensity f = μ :=
  ⟨μ.rnDeriv ν, Measure.measurable_rnDeriv μ ν, Measure.withDensity_rnDeriv_eq μ ν h⟩

/-- **Integral characterization.** For σ-finite `μ ≪ ν`, integrating the density over
a measurable set recovers the measure of that set. -/
theorem rnDeriv_setLIntegral [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν)
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s := by
  rw [← withDensity_apply _ hs, Measure.withDensity_rnDeriv_eq μ ν h]

/-- **Total mass.** Specialising the integral characterization to the whole space. -/
theorem rnDeriv_lintegral [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    ∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ := by
  have h2 := rnDeriv_setLIntegral h (s := Set.univ) MeasurableSet.univ
  rwa [Measure.restrict_univ] at h2

/-- **Uniqueness `ν`-a.e.** Any two measurable densities for `μ` with respect to a
σ-finite `ν` agree `ν`-almost everywhere. -/
theorem density_unique [SigmaFinite ν] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfμ : ν.withDensity f = μ) (hgμ : ν.withDensity g = μ) :
    f =ᵐ[ν] g := by
  have hf' : f =ᵐ[ν] (ν.withDensity f).rnDeriv ν := (Measure.rnDeriv_withDensity ν hf).symm
  have hg' : g =ᵐ[ν] (ν.withDensity g).rnDeriv ν := (Measure.rnDeriv_withDensity ν hg).symm
  rw [hfμ] at hf'
  rw [hgμ] at hg'
  exact hf'.trans hg'.symm

/-- **Lebesgue decomposition (general σ-finite).** No absolute continuity needed:
`μ` splits as a singular part plus an absolutely-continuous part with density the
Radon–Nikodym derivative. -/
theorem lebesgue_decomposition [SigmaFinite μ] [SigmaFinite ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  Measure.haveLebesgueDecomposition_add μ ν

end LebesgueRadonNikodym
