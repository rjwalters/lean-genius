/-
# Lᵖ-duality synthesis — the representer *consistency* lemma

This file supplies the remaining structural brick of the Folland-6.16 maximality
construction that the existing standalone ingredients did not yet package: the
step that says the σ-finite Riesz representers are *consistent under set
inclusion*.

Setup recap (see `CauchySchwarzIntegralLpDualitySynthesis.lean`). To represent an
arbitrary functional `φ ∈ (Lᵖ(μ))*` one exhausts `μ` by σ-finite sets, obtains a
representer `g_S ∈ Lᵠ(μ.restrict S)` on each with `‖g_S‖_q ≤ ‖φ‖`, and realizes the
supremum `c = ⨆_S ‖g_S‖_q` on a countable-union hull `T`. Two separate steps of that
argument — "the union hull realizes the supremum" and "for `U ⊇ T` the larger
representer agrees a.e. with `g_T` on `T`" — both rest on the same underlying fact:

  **if `S ⊆ S'` are measurable and `g_S`, `g_{S'}` represent (the `extByZero`-pullbacks
  of) the *same* functional `φ` on their respective restricted spaces, then
  `g_S = g_{S'}` a.e. on `S`.**

That is the content below (`representer_ae_eq_of_subset`). It is exactly the
uniqueness input the synthesis file's top-of-file sketch refers to as "by uniqueness
of the representing function"; it was assumed there but never packaged as a lemma.

## Proof

`g_S` and `g_{S'}` are two `Lᵠ(μ.restrict S)` functions (the second, `g_{S'}`,
restricts to `μ.restrict S` since `S ⊆ S'`). By Mathlib's
`AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq` it suffices to check that
their set-integrals agree over every finite-measure set. Testing against the `Lᵖ`
indicator `𝟙_t` of a finite set `t ⊆ S`, both `∫_t g_S ∂μ` and `∫_t g_{S'} ∂μ` equal
`φ` evaluated at the *same* extension-by-zero of `𝟙_t` (the two extensions
`extS 𝟙_t` and `extS' 𝟙_t` are `μ`-a.e. equal to `𝟙_t`, hence equal in `Lᵖ(μ)`), so
the two integrals coincide.

## Decoupling

The extension maps enter only through their **coeFn characterization**
`extS f =ᵐ[μ] S.indicator f`, so they are taken here as *abstract* continuous linear
hypotheses (`extS`, `hextS`, …) rather than the concrete `extByZeroCLM`. Consequently
this file imports **only Mathlib** and does not touch the build-heavy σ-finite Riesz
chain (`…Incomplete01.lean`); any concrete extension (the decoupled
`RieszLpDualityExtension.extByZeroCLM` or the in-chain `RieszSigmaFiniteComplete`
one) satisfies the coeFn hypothesis and can consume this lemma.

**Standalone / verified.** `0 sorry`, `0 axiom` (foundational axioms only). It is a
kernel-checked building block for the eventual maximality construction, not itself the
axiom elimination.
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszLpDualityConsistency

/-- **Representer consistency under set inclusion.** Let `1 < p < ∞` with Hölder
    conjugate `q`, and `S ⊆ S'` measurable. Suppose `g_S ∈ Lᵠ(μ.restrict S)` and
    `g_{S'} ∈ Lᵠ(μ.restrict S')` represent the extension-by-zero pullbacks of the
    *same* functional `φ ∈ (Lᵖ(μ))*` on `Lᵖ(μ.restrict S)` and `Lᵖ(μ.restrict S')`
    respectively. Then `g_S = g_{S'}` a.e. on `S`.

    The two extension-by-zero maps enter only through their coeFn characterization
    `extS f =ᵐ[μ] S.indicator f`, so they are abstract `Lᵖ`-continuous-linear
    hypotheses; the concrete `extByZeroCLM` (either the decoupled or in-chain version)
    satisfies them. -/
theorem representer_ae_eq_of_subset
    {p q : ℝ≥0∞} (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)]
    {S S' : Set α} (hS : MeasurableSet S) (hS' : MeasurableSet S') (hSS' : S ⊆ S')
    (φ : Lp ℝ p μ →L[ℝ] ℝ)
    {gS gS' : α → ℝ}
    (hgS : MemLp gS q (μ.restrict S)) (hgS' : MemLp gS' q (μ.restrict S'))
    (extS : Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ)
    (hextS : ∀ f : Lp ℝ p (μ.restrict S),
      (extS f : α → ℝ) =ᵐ[μ] S.indicator (f : α → ℝ))
    (extS' : Lp ℝ p (μ.restrict S') →L[ℝ] Lp ℝ p μ)
    (hextS' : ∀ f : Lp ℝ p (μ.restrict S'),
      (extS' f : α → ℝ) =ᵐ[μ] S'.indicator (f : α → ℝ))
    (hrepS : ∀ f : Lp ℝ p (μ.restrict S),
      φ (extS f) = ∫ a, (f : α → ℝ) a * gS a ∂(μ.restrict S))
    (hrepS' : ∀ f : Lp ℝ p (μ.restrict S'),
      φ (extS' f) = ∫ a, (f : α → ℝ) a * gS' a ∂(μ.restrict S')) :
    gS =ᵐ[μ.restrict S] gS' := by
  -- `q` is a genuine finite exponent `1 < q < ∞`.
  have hqtr : (1 : ℝ) < q.toReal := (Real.holderConjugate_iff.mp hpq.symm).1
  have hqtr0 : q.toReal ≠ 0 := ne_of_gt (lt_trans one_pos hqtr)
  obtain ⟨hq0, hqtop⟩ := ENNReal.toReal_ne_zero.mp hqtr0
  have hq1 : (1 : ℝ≥0∞) ≤ q := by
    have h := ENNReal.toReal_le_toReal (a := (1 : ℝ≥0∞)) (by simp) hqtop
    rw [ENNReal.toReal_one] at h
    exact h.mp hqtr.le
  -- `g_{S'}` also lies in `Lᵠ(μ.restrict S)` (restrict the bigger-set membership).
  have hgS'_S : MemLp gS' q (μ.restrict S) := by
    have h := hgS'.restrict S
    rwa [Measure.restrict_restrict hS, Set.inter_eq_left.mpr hSS'] at h
  -- Core: set-integrals over `t ⊆ S` (finite measure) agree, via the shared functional.
  have key : ∀ t : Set α, MeasurableSet t → t ⊆ S → μ t < ∞ →
      ∫ x in t, gS x ∂μ = ∫ x in t, gS' x ∂μ := by
    intro t ht htS htfin
    -- the `Lᵖ` indicator of `t` on each restricted space
    have hνt : μ.restrict S t ≠ ∞ := by
      rw [Measure.restrict_apply ht, Set.inter_eq_left.mpr htS]; exact htfin.ne
    have hν't : μ.restrict S' t ≠ ∞ := by
      rw [Measure.restrict_apply ht, Set.inter_eq_left.mpr (htS.trans hSS')]; exact htfin.ne
    have hmemS : MemLp (t.indicator (fun _ => (1 : ℝ))) p (μ.restrict S) :=
      memLp_indicator_const p ht 1 (Or.inr hνt)
    have hmemS' : MemLp (t.indicator (fun _ => (1 : ℝ))) p (μ.restrict S') :=
      memLp_indicator_const p ht 1 (Or.inr hν't)
    set cs := hmemS.toLp _ with hcs_def
    set cs' := hmemS'.toLp _ with hcs'_def
    have hcs_coe : (cs : α → ℝ) =ᵐ[μ.restrict S] t.indicator (fun _ => (1 : ℝ)) :=
      hmemS.coeFn_toLp
    have hcs'_coe : (cs' : α → ℝ) =ᵐ[μ.restrict S'] t.indicator (fun _ => (1 : ℝ)) :=
      hmemS'.coeFn_toLp
    -- both extensions are `μ`-a.e. equal to `𝟙_t`, hence equal as `Lᵖ(μ)` elements
    have hextScoe : (extS cs : α → ℝ) =ᵐ[μ] t.indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [hextS cs, (ae_restrict_iff' hS).mp hcs_coe] with a ha hcoe
      rw [ha]
      by_cases haS : a ∈ S
      · rw [Set.indicator_of_mem haS, hcoe haS]
      · rw [Set.indicator_of_notMem haS, Set.indicator_of_notMem (fun h => haS (htS h))]
    have hextS'coe : (extS' cs' : α → ℝ) =ᵐ[μ] t.indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [hextS' cs', (ae_restrict_iff' hS').mp hcs'_coe] with a ha hcoe
      rw [ha]
      by_cases haS' : a ∈ S'
      · rw [Set.indicator_of_mem haS', hcoe haS']
      · rw [Set.indicator_of_notMem haS',
          Set.indicator_of_notMem (fun h => haS' (htS.trans hSS' h))]
    have hφeq : φ (extS cs) = φ (extS' cs') := by
      rw [Lp.ext (hextScoe.trans hextS'coe.symm)]
    -- evaluate each side as `∫_t · ∂μ`
    have hgSval : φ (extS cs) = ∫ x in t, gS x ∂μ := by
      rw [hrepS cs]
      have h1 : (fun a => (cs : α → ℝ) a * gS a) =ᵐ[μ.restrict S] t.indicator gS := by
        filter_upwards [hcs_coe] with a ha
        rw [ha]
        by_cases hat : a ∈ t
        · rw [Set.indicator_of_mem hat, Set.indicator_of_mem hat, one_mul]
        · rw [Set.indicator_of_notMem hat, Set.indicator_of_notMem hat, zero_mul]
      rw [integral_congr_ae h1, integral_indicator ht,
        Measure.restrict_restrict ht, Set.inter_eq_left.mpr htS]
    have hgS'val : φ (extS' cs') = ∫ x in t, gS' x ∂μ := by
      rw [hrepS' cs']
      have h1 : (fun a => (cs' : α → ℝ) a * gS' a) =ᵐ[μ.restrict S'] t.indicator gS' := by
        filter_upwards [hcs'_coe] with a ha
        rw [ha]
        by_cases hat : a ∈ t
        · rw [Set.indicator_of_mem hat, Set.indicator_of_mem hat, one_mul]
        · rw [Set.indicator_of_notMem hat, Set.indicator_of_notMem hat, zero_mul]
      rw [integral_congr_ae h1, integral_indicator ht,
        Measure.restrict_restrict ht, Set.inter_eq_left.mpr (htS.trans hSS')]
    calc ∫ x in t, gS x ∂μ = φ (extS cs) := hgSval.symm
      _ = φ (extS' cs') := hφeq
      _ = ∫ x in t, gS' x ∂μ := hgS'val
  -- Apply the `setIntegral` uniqueness criterion on `μ.restrict S`.
  refine AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq ?_ ?_ ?_
    (hgS.aefinStronglyMeasurable hq0 hqtop) (hgS'_S.aefinStronglyMeasurable hq0 hqtop)
  · -- `gS` integrable on finite-measure subsets
    intro s _ hνs
    haveI : IsFiniteMeasure ((μ.restrict S).restrict s) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hνs⟩
    exact (hgS.restrict s).integrable hq1
  · -- `gS'` integrable on finite-measure subsets
    intro s _ hνs
    haveI : IsFiniteMeasure ((μ.restrict S).restrict s) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hνs⟩
    exact (hgS'_S.restrict s).integrable hq1
  · -- set-integrals agree, reduced to `key` on `s ∩ S`
    intro s hs hνs
    have hsS_fin : μ (s ∩ S) < ∞ := by
      rwa [Measure.restrict_apply hs] at hνs
    have e1 : ∫ x in s, gS x ∂(μ.restrict S) = ∫ x in (s ∩ S), gS x ∂μ := by
      rw [Measure.restrict_restrict hs]
    have e2 : ∫ x in s, gS' x ∂(μ.restrict S) = ∫ x in (s ∩ S), gS' x ∂μ := by
      rw [Measure.restrict_restrict hs]
    rw [e1, e2]
    exact key (s ∩ S) (hs.inter hS) Set.inter_subset_right hsS_fin

end RieszLpDualityConsistency

end
