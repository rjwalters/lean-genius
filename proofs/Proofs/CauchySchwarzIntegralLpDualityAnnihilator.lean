/-
# Lᵖ–Lᵠ pairing annihilator (uniqueness ingredient for Riesz maximality)

This file supplies the one analytic ingredient that the arbitrary-measure Riesz
representation (`CauchySchwarzIntegralLpDualitySynthesis.riesz_lp_surjective_general`)
still needs for its maximality construction (Folland *Real Analysis* Thm 6.16) and that
the synthesis file's four existing ingredient lemmas do **not** cover: **uniqueness of the
representing function**, i.e. the pairing `Lᵠ ↪ (Lᵖ)*` is injective.

    If `g ∈ Lᵠ(μ)` and `∫ f·g = 0` for every `f ∈ Lᵖ(μ)`, then `g = 0` a.e.

This is exactly the fact used in the maximality argument to show the representers are
*consistent* across nested σ-finite sets (`E ⊆ F ⟹ g_F = g_E` a.e. on `E`, since
`∫_E f·(g_E − g_F) = 0` for all `f ∈ Lᵖ(E)`) and, at the end, to identify `g_U = g_T`
a.e. off `T`.

## Why this is *not* the converse-Hölder dual-norm gap

Sessions 1–10 of this problem repeatedly flagged the "converse-Hölder dual-norm"
`‖g‖_q ≤ ⨆_{‖f‖_p≤1} |∫ f·g|` as a genuine Mathlib gap blocking maximality. That worry
is misplaced for the *uniqueness* direction: injectivity of the pairing needs only that
`∫ f·g = 0 ∀ f` forces `g = 0` a.e. — a **qualitative** statement with no norm estimate
and **no extremizer** `f = |g|^{q-1} sgn g`. It follows directly from Mathlib's
set-integral a.e.-vanishing machinery: testing against indicators of finite-measure sets
gives `∫_s g = 0` for all such `s`, and
`AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero` concludes `g = 0` a.e.
(no `SigmaFinite μ` hypothesis is even required, because `g ∈ Lᵠ` with `q < ∞` is
automatically `AEFinStronglyMeasurable`). The only place Hölder enters is the harmless
integrability of `g` on finite-measure sets.

Self-contained: imports only Mathlib. Verified by `lake env lean` (0 sorry, 0 axiom
beyond `propext`/`Classical.choice`/`Quot.sound`). Ready to be threaded into the
synthesis file's maximality proof once the σ-finite Riesz chain
(`…OQ01OQ01Incomplete01.lean`) — currently build-broken with ~70 Mathlib-API-drift
errors — is repaired.
-/

import Mathlib

open MeasureTheory ENNReal

namespace RieszLpDualityAnnihilator

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Annihilator / uniqueness lemma for the Lᵖ–Lᵠ pairing.**
    If `g ∈ Lᵠ(μ)` pairs to `0` against every `f ∈ Lᵖ(μ)` (`1 < p < ∞`, `q` the Hölder
    conjugate), then `g = 0` a.e. Equivalently, `Lᵠ(μ) → (Lᵖ(μ))*, g ↦ (f ↦ ∫ f·g)` is
    injective. No `SigmaFinite μ` hypothesis is needed. -/
theorem lp_pairing_eq_zero_ae_zero
    {p q : ℝ≥0∞}
    (hpq : p.toReal.HolderConjugate q.toReal)
    {g : α → ℝ} (hg : MemLp g q μ)
    (hzero : ∀ f : Lp ℝ p μ, ∫ a, (f : α → ℝ) a * g a ∂μ = 0) :
    g =ᵐ[μ] 0 := by
  -- `q` is a genuine finite exponent `1 < q < ∞`.
  have hqtr : (1 : ℝ) < q.toReal := (Real.holderConjugate_iff.mp hpq.symm).1
  have hqtr0 : q.toReal ≠ 0 := ne_of_gt (lt_trans one_pos hqtr)
  obtain ⟨hq0, hqtop⟩ := ENNReal.toReal_ne_zero.mp hqtr0
  have hq1 : (1 : ℝ≥0∞) ≤ q := by
    have h := ENNReal.toReal_le_toReal (a := (1 : ℝ≥0∞)) (by simp) hqtop
    rw [ENNReal.toReal_one] at h
    exact h.mp hqtr.le
  -- `g` is a.e. finitely-strongly-measurable (a `MemLp` function at a finite exponent).
  have hg_afm : AEFinStronglyMeasurable g μ := hg.aefinStronglyMeasurable hq0 hqtop
  refine hg_afm.ae_eq_zero_of_forall_setIntegral_eq_zero ?_ ?_
  · -- `g` is integrable on every finite-measure set (finite measure + `q ≥ 1`).
    intro s _ hμs
    haveI : IsFiniteMeasure (μ.restrict s) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hμs⟩
    exact (hg.restrict s).integrable hq1
  · -- `∫_s g = 0` for finite-measure `s`: pair `g` against the Lᵖ indicator of `s`.
    intro s hs hμs
    set c : α → ℝ := s.indicator (fun _ => (1 : ℝ)) with hc
    have hindic : MemLp c p μ := memLp_indicator_const p hs 1 (Or.inr hμs.ne)
    have hkey := hzero (hindic.toLp c)
    have hcoe : (hindic.toLp c : α → ℝ) =ᵐ[μ] c := hindic.coeFn_toLp
    have h1 : ∫ a, (hindic.toLp c : α → ℝ) a * g a ∂μ = ∫ a, c a * g a ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with a ha
      rw [ha]
    rw [h1] at hkey
    have h2 : (fun a => c a * g a) = s.indicator g := by
      funext a
      rw [hc]
      by_cases ha : a ∈ s
      · simp [Set.indicator_of_mem ha]
      · simp [Set.indicator_of_notMem ha]
    rw [h2, integral_indicator hs] at hkey
    exact hkey

end RieszLpDualityAnnihilator
