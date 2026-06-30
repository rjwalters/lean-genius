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
   `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`,
8. the **Radon–Nikodym chain rule** `(dμ/dν)·(dν/dλ) = dμ/dλ` (`λ`-a.e.),
9. the **self-derivative** `dμ/dμ = 1` (`μ`-a.e.),
10. the **reciprocal relation** `(dμ/dν)·(dν/dμ) = 1` (`μ`-a.e.) for `μ ≪ ν` —
   the chain rule specialised at `λ = μ`, the density analogue of `(dx/dy)(dy/dx)=1`.

Results 8–10 form an elementary *calculus of densities*: the chain rule is the
multiplicative composition law for Radon–Nikodym derivatives, the self-derivative
is its identity, and the reciprocal relation is the resulting inverse law.

The package is rounded out by the basic pointwise regularity of the density and
the probabilistic identification of the derivative:
11. **finiteness** `dμ/dν < ∞` and `dμ/dν ≠ ∞` (`ν`-a.e.) for σ-finite `μ` — the
    density is finite almost everywhere;
12. **positivity** `0 < dμ/dν` (`μ`-a.e.) for `μ ≪ ν` — the density does not
    vanish on the support of `μ`;
13. **inverse law** `(dμ/dν)⁻¹ = dν/dμ` (`μ`-a.e.) for σ-finite `μ ≪ ν` — the
    pointwise-inverse form of the reciprocal relation (10);
14. **conditional expectation as a Radon–Nikodym derivative**: for a sub-σ-algebra
    `m ≤ m₀` with `μ.trim` σ-finite and `f` integrable, the conditional expectation
    `μ[f|m]` agrees `μ`-a.e. with the signed Radon–Nikodym derivative of the
    `f`-weighted measure trimmed to `m`. This identifies `E[f|m]` as a density and
    is the measure-theoretic foundation of conditioning.
15. **change of variables** `∫⁻ g dμ = ∫⁻ (dμ/dν)·g dν` for σ-finite `μ ≪ ν`, with
    its set-restricted form `∫_s g dμ = ∫_s (dμ/dν)·g dν` — the defining property of a
    density and the principal *use* of the theorem (item 4 is the case `g = 1`).

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

/-! ### Calculus of densities

The Radon–Nikodym derivative behaves like a derivative: it composes multiplicatively
(chain rule), has the constant function `1` as its identity (self-derivative), and
consequently obeys a reciprocal law for mutually related measures. -/

variable {lam : Measure α}

/-- **Radon–Nikodym chain rule (σ-finite).** For σ-finite `μ, ν, λ` with `μ ≪ ν`,
the Radon–Nikodym derivatives compose multiplicatively, `λ`-almost everywhere:
`(dμ/dν)·(dν/dλ) = dμ/dλ`. This is the measure-theoretic analogue of the calculus
chain rule and underlies change-of-variables between densities. -/
theorem rnDeriv_chain [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite lam]
    (h : μ ≪ ν) :
    μ.rnDeriv ν * ν.rnDeriv lam =ᵐ[lam] μ.rnDeriv lam :=
  Measure.rnDeriv_mul_rnDeriv h

/-- **Self-derivative.** A σ-finite measure has constant Radon–Nikodym derivative `1`
with respect to itself, `μ`-almost everywhere: `dμ/dμ = 1`. This is the identity of
the chain rule's multiplicative composition law. -/
theorem rnDeriv_self_ae_one [SigmaFinite μ] :
    μ.rnDeriv μ =ᵐ[μ] (fun _ ↦ 1 : α → ℝ≥0∞) :=
  Measure.rnDeriv_self μ

/-- **Reciprocal relation.** For σ-finite `μ ≪ ν`, the forward and backward densities
multiply to `1`, `μ`-almost everywhere: `(dμ/dν)·(dν/dμ) = 1`. This is the chain rule
specialised to `λ = μ` followed by the self-derivative — the density analogue of the
inverse-function relation `(dx/dy)(dy/dx) = 1`. -/
theorem rnDeriv_mul_symm_ae_one [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    μ.rnDeriv ν * ν.rnDeriv μ =ᵐ[μ] (fun _ ↦ 1 : α → ℝ≥0∞) :=
  (Measure.rnDeriv_mul_rnDeriv (κ := μ) h).trans (Measure.rnDeriv_self μ)

/-! ### Pointwise regularity of the density

Basic almost-everywhere properties of the Radon–Nikodym derivative as a function:
it is finite, and (on the support of `μ`) strictly positive, with a pointwise
inverse law refining the reciprocal relation above. -/

/-- **Finiteness (`< ∞`).** The Radon–Nikodym derivative of a σ-finite measure is
finite `ν`-almost everywhere. -/
theorem rnDeriv_lt_top_ae [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x < ∞ :=
  Measure.rnDeriv_lt_top μ ν

/-- **Finiteness (`≠ ∞`).** Equivalent `≠ ∞` form of the finiteness statement. -/
theorem rnDeriv_ne_top_ae [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ ∞ :=
  Measure.rnDeriv_ne_top μ ν

/-- **Positivity.** For σ-finite `μ ≪ ν`, the Radon–Nikodym derivative is strictly
positive `μ`-almost everywhere — it does not vanish on the support of `μ`. -/
theorem rnDeriv_pos_ae [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x :=
  Measure.rnDeriv_pos h

/-- **Inverse law (pointwise).** For σ-finite `μ ≪ ν`, the pointwise inverse of the
forward density is the backward density, `μ`-almost everywhere: `(dμ/dν)⁻¹ = dν/dμ`.
This is the inverse form of the reciprocal relation `rnDeriv_mul_symm_ae_one`. -/
theorem inv_rnDeriv_ae [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ :=
  Measure.inv_rnDeriv h

/-! ### Change of variables: integration against the density

The defining purpose of a density: integrating a function against `μ` is the same as
integrating it weighted by `dμ/dν` against `ν`. This is the principal *use* of the
Radon–Nikodym theorem and the integral that the chain rule above is built to transport.
The measure-of-a-set characterization `rnDeriv_setLIntegral` is the special case `g = 1`. -/

/-- **Change of variables (integration against the density).** For σ-finite `μ ≪ ν`,
integrating `g` against `μ` equals integrating it weighted by the Radon–Nikodym
derivative against `ν`: `∫⁻ g dμ = ∫⁻ (dμ/dν)·g dν`. -/
theorem lintegral_density [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) :
    ∫⁻ x, μ.rnDeriv ν x * g x ∂ν = ∫⁻ x, g x ∂μ :=
  lintegral_rnDeriv_mul h hg

/-- **Change of variables on a set.** The set-restricted form of `lintegral_density`:
for σ-finite `μ ≪ ν` and measurable `s`, `∫_s g dμ = ∫_s (dμ/dν)·g dν`. Taking `g = 1`
recovers `rnDeriv_setLIntegral`. -/
theorem setLIntegral_density [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x * g x ∂ν = ∫⁻ x in s, g x ∂μ :=
  setLIntegral_rnDeriv_mul h hg hs

end LebesgueRadonNikodym

/-! ### Conditional expectation as a Radon–Nikodym derivative

The conditional expectation `μ[f|m]` onto a sub-σ-algebra `m ≤ m₀` is itself a
density: it is the (signed) Radon–Nikodym derivative of the `f`-weighted measure
`μ.withDensityᵥ f`, trimmed to `m`, with respect to `μ` trimmed to `m`. This places
conditioning inside the Radon–Nikodym calculus of this file. -/

namespace LebesgueRadonNikodym

section ConditionalExpectation

variable {β : Type*} {m m₀ : MeasurableSpace β} {ρ : Measure β}

/-- **Conditional expectation as a Radon–Nikodym derivative.** For a sub-σ-algebra
`m ≤ m₀` with `ρ.trim hm` σ-finite and `f` integrable, the conditional expectation
`ρ[f|m]` equals, `ρ`-almost everywhere, the signed Radon–Nikodym derivative of the
`f`-weighted measure trimmed to `m`. Thin wrapper over Mathlib's
`MeasureTheory.rnDeriv_ae_eq_condExp`; recorded here as the probabilistic face of
the σ-finite Radon–Nikodym package. -/
theorem condExp_ae_eq_signed_rnDeriv {hm : m ≤ m₀} [SigmaFinite (ρ.trim hm)]
    {f : β → ℝ} (hf : Integrable f ρ) :
    SignedMeasure.rnDeriv ((ρ.withDensityᵥ f).trim hm) (ρ.trim hm) =ᵐ[ρ] ρ[f|m] :=
  rnDeriv_ae_eq_condExp hf

end ConditionalExpectation

end LebesgueRadonNikodym
