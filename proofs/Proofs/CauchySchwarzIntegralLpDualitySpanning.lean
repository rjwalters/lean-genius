/-
# AE-strong-measurability across the σ-finite exhaustion
(cauchy-schwarz-integral-lp-duality-synthesis)

## What this file provides

The σ-finite Riesz-representation chain for `Lᵖ` (file `…OQ01OQ01Incomplete01.lean`)
builds, inside its 600-line `localization_existence` theorem, a single global representer
`g : α → ℝ` out of the per-piece representers `g_n` living on the σ-finite exhaustion
`spanningSets μ n`.  A recurring obstruction there was the step

    (∀ n, AEStronglyMeasurable g (μ.restrict (spanningSets μ n)))  ⟹  AEStronglyMeasurable g μ,

for which the knowledge base recorded a helper
`aestronglyMeasurable_of_restrict_spanningSets` that "exists NOWHERE (Mathlib or local)"
and would have to be constructed.  In fact it is a two-line consequence of two standard
Mathlib facts once they are lined up:

* `aestronglyMeasurable_iUnion_iff` — a.e.-strong-measurability on `μ.restrict (⋃ i, sᵢ)`
  is equivalent to a.e.-strong-measurability on each `μ.restrict sᵢ` (for a **countable**
  index; here `ι = ℕ`), and
* `MeasureTheory.iUnion_spanningSets` — the σ-finite exhaustion covers the space,
  `⋃ n, spanningSets μ n = univ`, together with `Measure.restrict_univ : μ.restrict univ = μ`.

This file packages the helper as a standalone, **Mathlib-only, kernel-verified** lemma so
the eventual repair/assembly of the σ-finite chain can `import` it directly rather than
re-deriving it inline.  It does *not* touch the build-broken chain
(`…Incomplete01.lean`), and eliminates no axiom by itself — it is a reusable building
block for the critical path (Session 16 roadmap, step 1: build the global representer `g`).

## Honesty note

This is elementary once the right Mathlib lemmas are located; the only "work" was
recognizing that the supposedly missing helper reduces to `aestronglyMeasurable_iUnion_iff`
applied along `iUnion_spanningSets`.  Fully verified, 0 axioms, 0 sorries.
-/

import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Metrizable.Basic

noncomputable section

open MeasureTheory TopologicalSpace

namespace RieszLpDualitySpanning

variable {α β : Type*} [MeasurableSpace α] {μ : Measure α}
  [TopologicalSpace β] [PseudoMetrizableSpace β] {f : α → β}

/-- **AE-strong-measurability glues across the σ-finite exhaustion.**
If `f` is a.e.-strongly-measurable on each restriction `μ.restrict (spanningSets μ n)`
of the σ-finite exhaustion, then it is a.e.-strongly-measurable for `μ` itself.

Reduces to `aestronglyMeasurable_iUnion_iff` (the index `ℕ` is countable) applied along
`iUnion_spanningSets μ : ⋃ n, spanningSets μ n = univ` and `Measure.restrict_univ`. -/
theorem aestronglyMeasurable_of_restrict_spanningSets [SigmaFinite μ]
    (h : ∀ n, AEStronglyMeasurable f (μ.restrict (spanningSets μ n))) :
    AEStronglyMeasurable f μ := by
  have hcov : AEStronglyMeasurable f (μ.restrict (⋃ n, spanningSets μ n)) :=
    aestronglyMeasurable_iUnion_iff.mpr h
  rwa [iUnion_spanningSets μ, Measure.restrict_univ] at hcov

end RieszLpDualitySpanning

end
