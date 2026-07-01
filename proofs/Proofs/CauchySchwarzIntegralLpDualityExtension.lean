/-
# Extension-by-zero infrastructure for the Lᵖ-duality synthesis
(cauchy-schwarz-integral-lp-duality-synthesis)

## What this file provides

The arbitrary-measure Riesz representation for `Lᵖ` (`1 < p < ∞`) is reduced to the
σ-finite case by a maximality / exhaustion argument (Folland, *Real Analysis* 2nd ed.,
Thm 6.16). Step 1 of that reduction pulls a functional `φ` on `Lp ℝ p μ` back to a
functional on `Lp ℝ p (μ.restrict S)`, for each measurable `S` whose restriction is
σ-finite, along the **extension-by-zero** isometric embedding

    extByZeroCLM : Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ,   `f ↦ S.indicator f`.

This CLM was previously buried (as a `private`/exposed `def`) inside the deep σ-finite
Riesz chain file `…OQ01OQ01Incomplete01.lean`, which is currently **build-broken** by
Mathlib API drift (~70 errors). Because the whole file is all-or-nothing for
verification, `extByZeroCLM` — although its construction depends on **Mathlib only** —
was effectively quarantined: unusable by any decoupled assembly until the multi-session
chain repair lands.

This file **re-homes** the construction into a standalone, Mathlib-only, kernel-verified
form, so the eventual arbitrary-measure assembly (`riesz_general_of_sigmaFinite`, planned
to take the σ-finite Riesz result *with norm bound* as an explicit hypothesis) can be
stated and proved **without** importing — and hence without waiting on the repair of —
the broken chain. See the knowledge base for the decoupling roadmap (Session 16).

## Simplification discovered while re-homing

The chain built `extByZeroCLM` on two hand-written `private` helper lemmas
(`eLpNorm_indicator_eq_restrict_loc`, `memLp_indicator_of_restrict_loc`). Both are now
**redundant with Mathlib**:

* `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`
    (`eLpNorm (S.indicator f) p μ = eLpNorm f p (μ.restrict S)`), and
* `MeasureTheory.memLp_indicator_iff_restrict`
    (`MemLp (S.indicator f) p μ ↔ MemLp f p (μ.restrict S)`).

So the construction here rests directly on the library, no bespoke seminorm bookkeeping.

## Contents

* `extByZeroCLM`            — the extension-by-zero CLM (norm `≤ 1`, in fact isometric).
* `extByZeroCLM_coeFn`      — `extByZeroCLM f =ᵐ[μ] S.indicator f`.
* `norm_extByZeroCLM_apply` — isometry: `‖extByZeroCLM f‖ = ‖f‖`.
* `norm_extByZeroCLM_le`    — operator-norm bound `‖extByZeroCLM‖ ≤ 1`.

All are verified `lake env lean` / Docker, 0 sorries, 0 `axiom`, axiom profile
`{propext, Classical.choice, Quot.sound}`.

## References

* Folland, *Real Analysis* (2nd ed.), Theorem 6.16.
* Mathlib: `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`,
  `MeasureTheory.memLp_indicator_iff_restrict`.
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszLpDualityExtension

/-- **Extension-by-zero: isometric embedding `Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ`.**

    Sends the class of `f` on the restricted measure to the class of `S.indicator f`
    on `μ`. It is linear (the indicator is `ℝ`-linear pointwise on `S`, and `0` off `S`),
    and isometric because `eLpNorm (S.indicator f) p μ = eLpNorm f p (μ.restrict S)`
    (`eLpNorm_indicator_eq_eLpNorm_restrict`); the `mkContinuous` bound `1` records the
    (tight) operator-norm bound `≤ 1`.

    Mathlib-only: this re-homes the construction that lived inside the build-broken
    σ-finite Riesz chain, so a decoupled arbitrary-measure assembly can use it without
    importing that chain. -/
def extByZeroCLM {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤) [Fact (1 ≤ p)] :
    Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp _
      map_add' := fun f₁ f₂ => by
        rw [Lp.ext_iff]
        filter_upwards [
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp (f₁ + f₂))).coeFn_toLp,
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f₁)).coeFn_toLp,
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f₂)).coeFn_toLp,
          Lp.coeFn_add
            (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f₁)).toLp _)
            (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f₂)).toLp _),
          (ae_restrict_iff' hS).mp (Lp.coeFn_add f₁ f₂)]
          with a h12 h1 h2 hadd hinner
        rw [h12, hadd]
        by_cases ha : a ∈ S
        · simp only [Pi.add_apply, h1, h2, Set.indicator_of_mem ha]
          exact hinner ha
        · simp only [Pi.add_apply, h1, h2, Set.indicator_of_notMem ha, add_zero]
      map_smul' := fun c f => by
        rw [Lp.ext_iff]
        filter_upwards [
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp (c • f))).coeFn_toLp,
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp _),
          (ae_restrict_iff' hS).mp (Lp.coeFn_smul c f)]
          with a hcf hf hsmul hinner
        rw [hcf, RingHom.id_apply, hsmul]
        by_cases ha : a ∈ S
        · simp only [Pi.smul_apply, hf, Set.indicator_of_mem ha]
          exact hinner ha
        · simp only [Pi.smul_apply, hf, Set.indicator_of_notMem ha, smul_zero] }
    1
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      have heq : ‖((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp _‖ = ‖f‖ := by
        simp only [Lp.norm_def]
        congr 1
        rw [eLpNorm_congr_ae ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).coeFn_toLp,
            eLpNorm_indicator_eq_eLpNorm_restrict hS]
      exact heq.le)

/-- The extension-by-zero of `f` is a.e. equal (under `μ`) to `S.indicator f`. -/
theorem extByZeroCLM_coeFn {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤) [Fact (1 ≤ p)]
    (f : Lp ℝ p (μ.restrict S)) :
    extByZeroCLM hS hp hptop f =ᵐ[μ] S.indicator (f : α → ℝ) :=
  ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).coeFn_toLp

/-- **Isometry.** Extension-by-zero preserves the `Lᵖ` norm. -/
theorem norm_extByZeroCLM_apply {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤) [Fact (1 ≤ p)]
    (f : Lp ℝ p (μ.restrict S)) :
    ‖extByZeroCLM hS hp hptop f‖ = ‖f‖ := by
  simp only [Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (extByZeroCLM_coeFn hS hp hptop f),
      eLpNorm_indicator_eq_eLpNorm_restrict hS]

/-- **Operator-norm bound** `‖extByZeroCLM‖ ≤ 1`, as recorded by the `mkContinuous`
    bound. (The map is in fact isometric — see `norm_extByZeroCLM_apply`.) -/
theorem norm_extByZeroCLM_le {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤) [Fact (1 ≤ p)] :
    ‖extByZeroCLM (μ := μ) hS hp hptop‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end RieszLpDualityExtension

end
