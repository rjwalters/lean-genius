/-
# Lᵖ-duality synthesis — the maximality *gluing* lemma

This file supplies the one step of the Folland-6.16 maximality construction that the
existing standalone ingredients (`CauchySchwarzIntegralLpDualityIngredients.lean`,
`CauchySchwarzIntegralLpDualityAnnihilator.lean`) did not yet package: the step that
*forces the representer to vanish off the maximizing hull*.

Setup recap (see `CauchySchwarzIntegralLpDualitySynthesis.lean`). To represent an
arbitrary functional `φ ∈ (Lᵖ(μ))*` one exhausts `μ` by σ-finite sets, obtains a
representer `g_S ∈ Lᵠ(μ.restrict S)` on each with `‖g_S‖_q ≤ ‖φ‖`, and realizes the
supremum `c = ⨆_S ‖g_S‖_q` on a countable-union hull `T`. For any larger σ-finite
`U ⊇ T` the representer `g_U` agrees a.e. with `g_T` on `T` (uniqueness — the
annihilator lemma), so `‖g_U‖_{q, T} = ‖g_T‖_{q, T} = c`, while maximality gives
`‖g_U‖_{q, U} ≤ c`. Combined with the automatic monotonicity `‖g_U‖_{q, T} ≤ ‖g_U‖_{q, U}`
the two seminorms are equal, and the `q`-power additivity over `U = T ⊔ (U \ T)` then
pins the leftover mass on `U \ T` to zero — i.e. `g_U = 0` a.e. off `T`. That is the
content below.

Concretely, `eLpNorm_ae_zero_on_diff_of_le` says: for a single `g ∈ Lᵠ(μ.restrict U)`
and a measurable `T ⊆ U`, if `‖g‖_{q, U} ≤ ‖g‖_{q, T}` then `g = 0` a.e. on `U \ T`.
In the maximality application `g = g_U` and the hypothesis is exactly
`‖g_U‖_{q, U} ≤ ‖g_U‖_{q, T}` (the last equal to `‖g_T‖_{q, T}` via consistency), so
the lemma applies directly. It is the qualitative heart of step 3.

The proof combines the already-verified `q`-power additivity/monotonicity over a set
difference (`RieszLpDualityIngredients.eLpNorm_rpow_restrict_{diff,mono}`) with the
finiteness `‖g‖_{q, U} < ∞` (`MemLp`) to cancel the `U`-mass and read off
`‖g‖_{q, U \ T}^q = 0`, then `eLpNorm_eq_zero_iff`.

**Standalone / verified.** Imports only Mathlib and the Mathlib-only ingredients file;
does *not* touch the build-broken σ-finite Riesz chain (`…Incomplete01.lean`). It is a
kernel-checked building block for the eventual maximality construction, not itself the
axiom elimination.
-/

import Mathlib
import Proofs.CauchySchwarzIntegralLpDualityIngredients

noncomputable section

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszLpDualityGluing

/-- **Maximality gluing lemma.** For `1 ≤ ... `, more precisely for a finite nonzero
    exponent `q` (`q ≠ 0`, `q ≠ ∞`), a function `g ∈ Lᵠ(μ.restrict U)` and a measurable
    `T ⊆ U`, if the Lᵠ-seminorm of `g` over `U` does not exceed its seminorm over the
    subset `T`, then `g` vanishes a.e. on the difference `U \ T`.

    This is the "maximality forces vanishing off the hull" step of the Riesz
    representation reduction: monotonicity always gives `‖g‖_{q, T} ≤ ‖g‖_{q, U}`, so the
    hypothesis `‖g‖_{q, U} ≤ ‖g‖_{q, T}` upgrades to equality, and the `q`-power
    additivity `‖g‖_{q, U}^q = ‖g‖_{q, T}^q + ‖g‖_{q, U \ T}^q` (finite, since `g ∈ Lᵠ`)
    forces the `U \ T` contribution to `0`. -/
theorem eLpNorm_ae_zero_on_diff_of_le
    {g : α → ℝ} {T U : Set α} (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hTU : T ⊆ U) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (hg : MemLp g q (μ.restrict U))
    (hle : eLpNorm g q (μ.restrict U) ≤ eLpNorm g q (μ.restrict T)) :
    g =ᵐ[μ.restrict (U \ T)] 0 := by
  set r := q.toReal with hr_def
  have hr : 0 < r := ENNReal.toReal_pos hq0 hqtop
  -- `q`-power additivity over the disjoint decomposition `U = T ⊔ (U \ T)`.
  have hadd :
      eLpNorm g q (μ.restrict U) ^ r
        = eLpNorm g q (μ.restrict T) ^ r
          + eLpNorm g q (μ.restrict (U \ T)) ^ r :=
    RieszLpDualityIngredients.eLpNorm_rpow_restrict_diff hT hU hTU hq0 hqtop
  -- Monotonicity: `‖g‖_{q, T}^r ≤ ‖g‖_{q, U}^r`.
  have hmono :
      eLpNorm g q (μ.restrict T) ^ r ≤ eLpNorm g q (μ.restrict U) ^ r :=
    RieszLpDualityIngredients.eLpNorm_rpow_restrict_mono hT hU hTU hq0 hqtop
  -- Hypothesis raised to the `r`-th power: `‖g‖_{q, U}^r ≤ ‖g‖_{q, T}^r`.
  have hle_r :
      eLpNorm g q (μ.restrict U) ^ r ≤ eLpNorm g q (μ.restrict T) ^ r :=
    ENNReal.rpow_le_rpow hle hr.le
  -- Hence the two `r`-th powers are equal.
  have heq : eLpNorm g q (μ.restrict U) ^ r = eLpNorm g q (μ.restrict T) ^ r :=
    le_antisymm hle_r hmono
  -- Finiteness of the `T`-mass, from `g ∈ Lᵠ(μ.restrict U)` and the norm equality.
  have hfinU : eLpNorm g q (μ.restrict U) ^ r ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hr.le hg.2.ne
  have hTfin : eLpNorm g q (μ.restrict T) ^ r ≠ ⊤ := heq ▸ hfinU
  -- From additivity + equality: `T^r + diff = T^r`, so `diff = 0` (cancel `T^r ≠ ⊤`).
  have hcollapse :
      eLpNorm g q (μ.restrict T) ^ r + eLpNorm g q (μ.restrict (U \ T)) ^ r
        = eLpNorm g q (μ.restrict T) ^ r := by
    rw [← hadd]; exact heq
  have hdiff0 : eLpNorm g q (μ.restrict (U \ T)) ^ r = 0 :=
    (ENNReal.add_right_inj hTfin).mp (hcollapse.trans (add_zero _).symm)
  -- `x ^ r = 0` with `r > 0` gives `x = 0`.
  have hzero : eLpNorm g q (μ.restrict (U \ T)) = 0 := by
    rcases (ENNReal.rpow_eq_zero_iff.mp hdiff0) with ⟨h, _⟩ | ⟨_, hlt⟩
    · exact h
    · exact absurd hlt (not_lt.mpr hr.le)
  -- Zero seminorm ⇒ a.e. zero.
  have haesm : AEStronglyMeasurable g (μ.restrict (U \ T)) :=
    hg.1.mono_measure (Measure.restrict_mono Set.diff_subset le_rfl)
  exact (eLpNorm_eq_zero_iff haesm hq0).mp hzero

end RieszLpDualityGluing

end
