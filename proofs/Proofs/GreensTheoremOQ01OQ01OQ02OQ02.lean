/-
  LocallyIntegrable Wrapper for `intervalIntegral_swap`
  (greens-theorem-oq-01-oq-01-oq-02-oq-02)

  Parent slug: greens-theorem-oq-01-oq-01-oq-02 (verified, 0 sorries, 0 axioms)
  Question:    Can the integrability hypothesis of the parent's
               `intervalIntegral_swap` (product-of-restricted volumes on
               `uIcc a b × uIcc c d`) be replaced with the canonical
               Mathlib idiom `LocallyIntegrable f volume`?

  ## Answer (S1 OBSERVE audit, PR #18262): YES — as a user-interface
  wrapper, not as a strict weakening.

  `LocallyIntegrable f volume` is *strictly stronger* than the parent's
  hypothesis (it gives `IntegrableOn` on every compact set, not just the
  one rectangle), but it is the canonical Mathlib idiom users already
  have in hand for continuous functions, L¹_loc densities, and Sobolev
  representatives. The wrapper does **not** weaken the hypothesis; it
  provides an alternative interface that discharges the awkward
  `(restrict A).prod (restrict B)` form internally.

  ## What this file ships (S2 SCAFFOLD)

  A single wrapper theorem
  `intervalIntegral_swap_of_locallyIntegrable` that takes the canonical
  `LocallyIntegrable` hypothesis and delegates to the parent's
  `GreensTheoremOQ01OQ01OQ02.intervalIntegral_swap`.

  ## Proof outline (~5-line modification of parent's continuous case)

  Apply the parent's `intervalIntegral_swap`. The only obligation is the
  awkward integrability hypothesis. Use `LocallyIntegrable.integrableOn_isCompact`
  to get `IntegrableOn f (uIcc a b ×ˢ uIcc c d) volume` from
  `LocallyIntegrable f volume` plus compactness of the rectangle. Then
  rewrite via `restrict_prod_eq_prod_restrict measurableSet_uIcc
  measurableSet_uIcc` to match the parent's `(restrict).prod (restrict)`
  form.

  Sorries: 0.
  Axioms: 0.

  ## What this file does NOT do

  - Does not eliminate the `Measurable` hypothesis. The parent's
    `intervalIntegral_swap` uses `Integrable.mono_measure` which requires
    `Measurable f`, not just `AEStronglyMeasurable f`. Most users have
    `Continuous f` which gives both for free, so the wrapper signature
    remains friendly.
  - Does not generalize the codomain to Bochner-valued `f`. That is
    sibling `oq-03`'s deliverable (see `GreensTheoremOQ01OQ01OQ02OQ03.lean`).
    A composed `LocallyIntegrable` + Bochner wrapper is a natural sub-OQ
    that the seeker may extract separately.
-/

import Proofs.GreensTheoremOQ01OQ01OQ02
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory intervalIntegral Set MeasureTheory.Measure

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

namespace GreensTheoremOQ01OQ01OQ02OQ02

/-- **`intervalIntegral_swap` with the canonical `LocallyIntegrable`
    hypothesis.**

For `f : ℝ → ℝ → ℝ` jointly measurable and `LocallyIntegrable` on `ℝ × ℝ`
against Lebesgue volume, the iterated interval integrals on any rectangle
`[a, b] × [c, d]` (no ordering required) coincide.

This is a strict-usability wrapper: `LocallyIntegrable` is the canonical
Mathlib idiom users already hold for continuous functions, L¹_loc densities,
and Sobolev representatives. The wrapper discharges the parent's awkward
`(volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d))` integrability
form internally via `LocallyIntegrable.integrableOn_isCompact` plus
`restrict_prod_eq_prod_restrict`. -/
theorem intervalIntegral_swap_of_locallyIntegrable {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_loc : LocallyIntegrable (fun p : ℝ × ℝ => f p.1 p.2) volume) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  apply GreensTheoremOQ01OQ01OQ02.intervalIntegral_swap a b c d hf_meas
  have hcpt : IsCompact (uIcc a b ×ˢ uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2)
      (uIcc a b ×ˢ uIcc c d) volume :=
    hf_loc.integrableOn_isCompact hcpt
  -- Bridge: `IntegrableOn f s μ` ⇌ `Integrable f (μ.restrict s)`
  -- (`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`,
  -- def `IntegrableOn`); `volume_eq_prod ℝ ℝ : volume = volume.prod volume`
  -- (`Mathlib/MeasureTheory/Measure/Prod.lean:181`, `rfl`);
  -- `Measure.prod_restrict` requires `[SFinite μ] [SFinite ν]`
  -- (`Mathlib/MeasureTheory/Measure/Prod.lean:720`), satisfied
  -- automatically by `volume` (SigmaFinite ⇒ SFinite). See S3 PREP-2
  -- (#18711-followup) §§1–4 for the verification chain at pin
  -- `2df2f015...` and the `AreaOfCircleOQ05OQ04.lean:158` in-repo
  -- precedent. Replaces phantom-name
  -- `restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc`
  -- in S2 SCAFFOLD #18364.
  rw [IntegrableOn, volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hint
  exact hint

end GreensTheoremOQ01OQ01OQ02OQ02
