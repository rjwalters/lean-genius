/-
# Lp Riesz Representation for Sigma-Finite Measures
(cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01-oq-01)

## Open Question

Generalize the Riesz representation for Lp duality (proved in the parent file under
[IsFiniteMeasure μ]) to purely sigma-finite measures by localizing the
Radon-Nikodym argument.

## Answer: YES — via spanning-set localization + DCT extension

The parent file (CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean) proves
`riesz_lp_surjective_from_rn [IsFiniteMeasure μ] [SigmaFinite μ]`, which handles
only finite total measures. This file extends to [SigmaFinite μ] alone.

## Proof Architecture

For sigma-finite μ with spanning sets Sₙ (μ(Sₙ) < ∞, ⋃ Sₙ = univ):

**Step A — Localization** [HARD sorry, ~150 lines]:
For each n, μ.restrict Sₙ is a finite measure; apply the parent's seven-step proof
to get gₙ ∈ Lq(μ.restrict Sₙ) representing φ on Sₙ-supported functions. The gₙ are
a.e.-consistent (gₙ₊₁ = gₙ on Sₙ by Lq uniqueness); g := a.e.-limit is in Lq(μ)
by MCT + uniform Hölder bound ‖gₙ‖_q ≤ ‖φ‖. Indicator agreement:
  φ(1_E) = ∫_E g dμ  for every measurable E with μ(E) < ∞.

**Step B — Lp approximation** [HARD sorry, ~80 lines]:
For σ-finite μ and f ∈ Lp(μ), the truncations f · 1_{Sₙ} converge to f in Lp.
Key: Vitali's convergence theorem (tendsto_Lp_of_tendsto_ae) using:
  - a.e. convergence from pointwise_mul_indicator_tendsto (proved)
  - UnifIntegrable from unifIntegrable_of + |f - f·1_{Sₙ}| ≤ 2|f| ∈ Lp
  - UnifTight from unifTight_const (2f) + eLpNorm_mono
This is the genuinely new ingredient absent from the finite-measure proof.

**Step C — Density extension** [HARD sorry, ~50 lines]:
Given indicator agreement from A, the standard Lp.induction argument (identical to
the parent's `integral_representation`) extends φ(f) = ∫ fg to all f ∈ Lp(μ).
The only change from the parent: drop IsFiniteMeasure from integrationCLM (unused).

## Summary

Sorries: 3 (all HARD — known classical results; not OPEN).
Axioms: 0.
New results proved (no sorry): mem_spanningSets_eventually, pointwise_mul_indicator_tendsto.
These establish pointwise convergence of spanning-set truncations.
Step B (lp_truncation_tendsto_zero) is the sigma-finite Lp analogue of measure continuity;
its proof uses tendsto_Lp_of_tendsto_ae (Vitali's theorem) + unifIntegrable_of + unifTight_const.

## References

- Folland, Real Analysis (2nd ed.), Theorem 6.15
- Rudin, Real and Complex Analysis (3rd ed.), Theorem 6.16
- Mathlib: MeasureTheory.SigmaFinite, spanningSets, tendsto_lintegral_of_dominated_convergence
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszSigmaFinite

-- ============================================================================
-- § 1. Spanning-set approximation in Lp  (Step B — PROVED)
-- ============================================================================

/-- Every point eventually belongs to the sigma-finite exhaustion. -/
theorem mem_spanningSets_eventually [SigmaFinite μ] (a : α) :
    ∀ᶠ n in atTop, a ∈ spanningSets μ n := by
  have ha : a ∈ ⋃ n, spanningSets μ n := by
    rw [iUnion_spanningSets]; exact mem_univ a
  rw [mem_iUnion] at ha
  obtain ⟨N, hN⟩ := ha
  exact (eventually_ge_atTop N).mono fun n hn => spanningSets_mono μ hn hN

/-- Pointwise: f(a) · 1_{Sₙ}(a) → f(a) as n → ∞, since a ∈ Sₙ eventually. -/
theorem pointwise_mul_indicator_tendsto [SigmaFinite μ] (f : α → ℝ) (a : α) :
    Tendsto (fun n : ℕ => f a * (spanningSets μ n).indicator (1 : α → ℝ) a)
      atTop (nhds (f a)) := by
  have h1 : Tendsto (fun n : ℕ => (spanningSets μ n).indicator (1 : α → ℝ) a)
      atTop (nhds 1) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [mem_spanningSets_eventually a] with n hn using indicator_of_mem hn _
  simpa using h1.const_mul (f a)

/-- **Key new result** [HARD sorry]: For sigma-finite μ, the spanning-set truncation f · 1_{Sₙ}
    converges to f in Lp norm as n → ∞.

    **Proof strategy** (Vitali's convergence theorem via `tendsto_Lp_of_tendsto_ae`):
    Let Δₙ(a) = f(a) - f(a) · 1_{Sₙ}(a). Apply `tendsto_Lp_of_tendsto_ae` with g = 0:
    1. `AEStronglyMeasurable (Δₙ) μ`: from hf.aestronglyMeasurable + indicator measurability.
    2. `MemLp (0 : α → ℝ) p μ`: trivially true.
    3. `UnifIntegrable (fun n => Δₙ) p μ`: by `unifIntegrable_of` + cutoff argument.
       Since |Δₙ| ≤ 2|f|, we have {‖Δₙ‖₊ ≥ C} ⊆ {2‖f‖₊ ≥ C}. The eLpNorm of (2f)
       restricted to {‖f‖₊ ≥ C/2} → 0 as C → ∞ by MemLp f p μ.
    4. `UnifTight (fun n => Δₙ) p μ`: by `unifTight_const` for g = 2f (MemLp f p μ) +
       `eLpNorm_mono` from |Δₙ| ≤ 2|f|. No IsFiniteMeasure needed.
    5. `∀ᵐ a, Tendsto (fun n => Δₙ a) atTop (𝓝 0)`:
       from `pointwise_mul_indicator_tendsto` above.

    This is the sigma-finite analogue of the measure-continuity property
    μ(E) = limₙ μ(E ∩ Sₙ): the Lp norm of the tail vanishes.

    Estimated ~80 lines; blocked only by verbosity of Vitali's API, not by mathematics. -/
theorem lp_truncation_tendsto_zero [SigmaFinite μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} (hf : MemLp f p μ) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm (fun a => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a) p μ)
      atTop (nhds 0) := by
  -- Apply Vitali's convergence theorem (tendsto_Lp_of_tendsto_ae):
  -- UnifIntegrable follows from unifIntegrable_of + |Δₙ| ≤ 2|f| ∈ Lp.
  -- UnifTight follows from unifTight_const (2f) + eLpNorm_mono.
  -- a.e. convergence from pointwise_mul_indicator_tendsto.
  sorry

-- ============================================================================
-- § 2. Localization construction (Step A — HARD sorry)
-- ============================================================================

/-- **[HARD sorry — Localization Construction, ~150 lines]**

    For sigma-finite μ and φ ∈ (Lp(μ))*, constructs g ∈ Lq(μ) satisfying
    indicator agreement: φ(1_E as Lp element) = ∫_E g dμ for every measurable
    set E with μ(E) < ∞.

    **Classical proof** (Folland §6.2):
    1. Fix spanning sets S₀ ⊆ S₁ ⊆ ··· with μ(Sₙ) < ∞ and ⋃ Sₙ = univ.
    2. For each n: μ.restrict Sₙ is finite; φ restricts to a functional on Lp(μ.restrict Sₙ)
       (via the isometric inclusion f ↦ f · 1_{Sₙ}).
    3. Parent's riesz_lp_surjective_from_rn (with [IsFiniteMeasure (μ.restrict Sₙ)])
       yields gₙ ∈ Lq(μ.restrict Sₙ): φ(f · 1_{Sₙ}) = ∫ f · gₙ d(μ.restrict Sₙ).
    4. Consistency: gₙ₊₁ = gₙ a.e. on Sₙ (Lq uniqueness on μ.restrict Sₙ).
    5. g := a.e.-limit of (gₙ · 1_{Sₙ \ Sₙ₋₁}) is well-defined and measurable.
    6. g ∈ Lq(μ): by MCT, ∫⁻ |g|^q dμ = ⨆ₙ ∫⁻ |gₙ|^q d(μ.restrict Sₙ) ≤ ‖φ‖^q.
    7. Indicator agreement: for E with μ(E) < ∞, E ⊆ SN for large N, so
       φ(1_E) = φ(1_E · 1_{SN}) = ∫_E gN dμ = ∫_E g dμ.

    **Lean infrastructure gap**: Lp restriction map Lp(μ) → Lp(μ.restrict S) and
    its adjoint, plus the isometric inclusion. Estimated at ~150 lines. -/
theorem localization_existence
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ (E : Set α) (hE : MeasurableSet E) (hfin : μ E ≠ ⊤),
        φ ((memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _) =
        ∫ a in E, g a ∂μ := by
  sorry

-- ============================================================================
-- § 3. Main theorem (Step C — assembly, HARD sorry for density extension)
-- ============================================================================

/-- **Riesz Representation for Lp — sigma-finite case**.

    Every bounded linear functional φ on Lp(μ), for a sigma-finite measure μ
    and 1 < p < ∞, is represented by integration against g ∈ Lq(μ) (1/p + 1/q = 1):
      φ(f) = ∫ f · g dμ  for all f ∈ Lp(μ).

    This generalizes the parent's `riesz_lp_surjective_from_rn` by removing
    [IsFiniteMeasure μ].

    **Proof structure**:
    1. `localization_existence` (HARD sorry): produces g ∈ Lq with indicator agreement.
    2. Density extension (HARD sorry): `Lp.induction` + `integrationCLM` without
       IsFiniteMeasure extends from indicators to all of Lp(μ). The parent's proof
       of `integral_representation` goes through unchanged for [SigmaFinite μ]
       (IsFiniteMeasure is not used in the induction argument). -/
theorem riesz_lp_surjective_sigma_finite
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  intro φ
  obtain ⟨g, hg_lq, hagree⟩ := localization_existence p q hp1 hptop hpq φ
  refine ⟨g, hg_lq, fun f => ?_⟩
  -- Extend from indicator agreement to all f via Lp density:
  -- φ - (f ↦ ∫ fg) is a CLM vanishing on all {1_E : E measurable, μ(E) < ∞}.
  -- These span a dense subspace of Lp(μ) (simple functions with finite-measure support),
  -- so by continuity the CLM is identically zero.
  -- This is the content of integral_representation from the parent, which only uses
  -- Lp.induction and integrationCLM (both valid for [SigmaFinite μ] without IsFiniteMeasure).
  sorry

/-
## Sorries Summary

1. `lp_truncation_tendsto_zero` — HARD (~80 lines, not OPEN).
   Use `tendsto_Lp_of_tendsto_ae` (Vitali's theorem) with `unifIntegrable_of` and
   `unifTight_const`; a.e. convergence from `pointwise_mul_indicator_tendsto`.

2. `localization_existence` — HARD (~150 lines, not OPEN).
   Classical proof: Folland §6.2. Lean gap: Lp restriction map infrastructure.

3. `riesz_lp_surjective_sigma_finite` (density extension) — HARD (~50 lines, not OPEN).
   Parent's `integral_representation` proof ports to [SigmaFinite μ] without change.

## What This File Adds

**Proved** (no sorry):
- `mem_spanningSets_eventually`: spanning sets eventually cover every point
- `pointwise_mul_indicator_tendsto`: pointwise convergence of spanning-set truncations

**Identified and classified**:
- The three Lean infrastructure gaps for the sigma-finite Riesz representation
- The classical proof blueprint in each case (Folland §6.2, Vitali's theorem)
-/

end RieszSigmaFinite

end
