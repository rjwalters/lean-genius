import Mathlib.Dynamics.Ergodic.Extreme
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Tactic

/-!
# Furstenberg correspondence OQ-02 → OQ-02: the extreme-point structure for ergodic decomposition

The parent entry (`furstenberg-correspondence-oq-02`) is a **feasibility survey** of
formalizing the ergodic decomposition theorem. It lists as an open question:

> *Is the disintegration in Mathlib sufficient for the ergodic decomposition, or does it
> need extension?*

and is uncertain whether the key structural fact — that **ergodic measures are exactly the
extreme points** of the invariant probability measures (the Choquet-simplex picture
underlying the decomposition) — is already in Mathlib.

This file resolves that uncertainty: the characterization **is** in Mathlib
(`Ergodic.iff_mem_extremePoints`), together with the **rigidity** of ergodic measures
(`Ergodic.eq_of_absolutelyContinuous`) and the **a.e.-constancy of invariant functions**
(`PreErgodic.ae_eq_const_of_ae_eq_comp`). We package these as the concrete building blocks of
ergodic decomposition, with `0` axioms, so the honest answer to the OQ is recorded:
Mathlib's disintegration plus this extreme-point theory supplies the structure; what remains
for the full decomposition is the Choquet **integral representation** of a general invariant
measure over its ergodic (extreme) components.

## Main results

* `ergodic_iff_extremePoint` : ergodic ⟺ extreme point of the invariant probability measures.
* `ergodic_eq_of_absolutelyContinuous` : ergodic rigidity (distinct components are singular).
* `ergodic_invariant_ae_const` : invariant measurable functions are a.e. constant.
-/

namespace FurstenbergCorrespondenceOQ02OQ02

open MeasureTheory Function Set
open scoped ENNReal

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X} {f : X → X}

/-- **The Choquet-simplex characterization.** A probability measure is **ergodic** for `f`
    iff it is an **extreme point** of the convex set of `f`-invariant probability measures.
    This is the structural fact underlying the ergodic decomposition (a general invariant
    measure as an integral over the extreme = ergodic points), and it is already available in
    Mathlib (`Ergodic.iff_mem_extremePoints`) — answering the parent survey's uncertainty. -/
theorem ergodic_iff_extremePoint [IsProbabilityMeasure μ] :
    Ergodic f μ ↔
      μ ∈ extremePoints ℝ≥0∞ {ν : Measure X | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} :=
  Ergodic.iff_mem_extremePoints

/-- **Ergodic rigidity.** An `f`-invariant probability measure `ν` that is absolutely
    continuous with respect to an ergodic measure `μ` must equal `μ`. Equivalently, distinct
    ergodic measures are mutually singular — the ergodic components of the decomposition do
    not overlap. -/
theorem ergodic_eq_of_absolutelyContinuous {ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ν = μ :=
  hμ.eq_of_absolutelyContinuous hfν hνμ

/-- **Invariant functions are a.e. constant.** Under an ergodic measure, every measurable
    function `g` with `g ∘ f = g` is almost everywhere constant. This is the input that makes
    the decomposition kernel (sending a point to its ergodic component) well defined: the
    invariant σ-algebra is a.e. trivial on each ergodic component. -/
theorem ergodic_invariant_ae_const (hμ : Ergodic f μ) {g : X → ℝ}
    (hgm : Measurable g) (hg : g ∘ f = g) : ∃ c : ℝ, g =ᵐ[μ] Function.const X c :=
  hμ.toPreErgodic.ae_eq_const_of_ae_eq_comp hgm hg

/-- **Packaged prerequisites.** For an ergodic probability measure, the extreme-point
    characterization, rigidity, and invariant-function constancy hold simultaneously — the
    three Mathlib-provided ingredients of the ergodic decomposition. -/
theorem ergodic_decomposition_prerequisites [IsProbabilityMeasure μ] (hμ : Ergodic f μ) :
    (μ ∈ extremePoints ℝ≥0∞ {ν : Measure X | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}) ∧
    (∀ ν : Measure X, IsProbabilityMeasure ν → MeasurePreserving f ν ν → ν ≪ μ → ν = μ) ∧
    (∀ g : X → ℝ, Measurable g → g ∘ f = g → ∃ c : ℝ, g =ᵐ[μ] Function.const X c) := by
  refine ⟨ergodic_iff_extremePoint.mp hμ, ?_, ?_⟩
  · intro ν _ hfν hνμ
    exact ergodic_eq_of_absolutelyContinuous hμ hfν hνμ
  · intro g hgm hg
    exact ergodic_invariant_ae_const hμ hgm hg

end FurstenbergCorrespondenceOQ02OQ02
