/-
# Radon-Nikodým Route to Lp Duality (cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01)

## Open Question

"Can Mathlib's Radon-Nikodým machinery (MeasureTheory.SignedMeasure.rnDeriv)
be composed with Lp membership to eliminate the surjectivity axiom?"

## Answer: YES, IN PRINCIPLE — with ~200 lines of composition

Mathlib has all the necessary pieces:
  1. SignedMeasure.rnDeriv : α → ℝ (Radon-Nikodým derivative)
  2. Measure.withDensityᵥ : constructs vector measures from densities
  3. absolutelyContinuous_iff_withDensity_rnDeriv_eq : AC ↔ RN reconstruction
  4. InnerProductSpace.toDual : L2 case (already proved in parent file)
  5. ENNReal.lintegral_mul_le_Lp_mul_Lq : Hölder inequality

The gap is composing these into a single surjectivity proof. This file
formalizes the key intermediate steps, proving what Mathlib supports
directly and isolating the remaining infrastructure needs as explicit sorries.

## Proof Architecture (Rudin, Theorem 6.16)

Given φ ∈ (Lp)*, we construct g ∈ Lq with φ(f) = ∫ fg dμ:

  Step 1. φ induces a signed measure: ν(E) = φ(indicator_E)
  Step 2. ν ≪ μ (if μ(E) = 0 then indicator_E = 0 in Lp, so φ(indicator_E) = 0)
  Step 3. Radon-Nikodým: g = dν/dμ exists as α → ℝ
  Step 4. g ∈ Lq (uses Hölder tightness + uniform boundedness)
  Step 5. φ(f) = ∫ fg dμ (extends from simple functions by density)

Steps 1-3 are formalized below. Steps 4-5 require Lp norm estimates
that need ~100-200 lines of additional infrastructure.

## References

- Rudin, Real and Complex Analysis, Theorem 6.16
- Mathlib: MeasureTheory.SignedMeasure.rnDeriv
- Mathlib: MeasureTheory.Measure.withDensityᵥ
- Mathlib: ENNReal.lintegral_mul_le_Lp_mul_Lq
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszLpSurjectivity

/-
## Step 1: Indicator Functions in Lp

For a finite measure set E, the indicator function 1_E belongs to Lp
for any 1 ≤ p < ∞. This is the entry point for constructing the
signed measure from a functional.
-/

/-- Indicator of a finite-measure measurable set is in Lp for 1 ≤ p < ∞. -/
theorem indicator_memLp {E : Set α} (hE : MeasurableSet E) (hfin : μ E ≠ ⊤)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤) :
    Memℒp (E.indicator (fun _ => (1 : ℝ))) p μ := by
  apply Memℒp.indicator hE
  exact memℒp_const 1

/-- The Lp norm of an indicator function: ‖1_E‖_p = μ(E)^{1/p}. -/
theorem indicator_snorm {E : Set α} (hE : MeasurableSet E) (hfin : μ E ≠ ⊤)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤) :
    eLpNorm (E.indicator (fun _ => (1 : ℝ))) p μ = (μ E) ^ (1 / p) := by
  rw [eLpNorm_indicator_const hE (1 : ℝ) hptop]
  simp [ENNReal.nnnorm_one]

/-
## Step 2: Functional Induces Absolute Continuity

Key insight: if φ is a bounded linear functional on Lp and μ(E) = 0,
then 1_E = 0 a.e., so ‖1_E‖_p = 0, so |φ(1_E)| ≤ ‖φ‖ · 0 = 0.

This means the set function E ↦ φ(1_E) is absolutely continuous
with respect to μ.
-/

/-- If μ(E) = 0 and f = indicator_E, then f = 0 a.e. -/
theorem indicator_ae_zero_of_measure_zero {E : Set α} (hE : μ E = 0) :
    ∀ᵐ x ∂μ, E.indicator (fun _ => (1 : ℝ)) x = 0 := by
  filter_upwards [ae_of_all μ (fun x => True)] with x _
  · by_cases hx : x ∈ E
    · exact absurd hx (fun h => by
        have := measure_mono (singleton_subset_iff.mpr h)
        simp [hE, le_antisymm (hE ▸ this) (zero_le _)] at this)
    · simp [indicator_apply, hx]

/-- Indicator of a null set has zero eLpNorm. -/
theorem indicator_eLpNorm_zero {E : Set α} (hE : MeasurableSet E) (hμE : μ E = 0)
    (p : ℝ≥0∞) :
    eLpNorm (E.indicator (fun _ => (1 : ℝ))) p μ = 0 := by
  apply eLpNorm_eq_zero_of_ae_zero
  · exact (aestronglyMeasurable_const.indicator hE)
  · filter_upwards [measure_zero_iff_ae_nmem.mp hμE] with x hx
    simp [indicator_apply, hx]

/-
## Step 3: From Functional to Signed Measure via setToFun

Mathlib's `setToL1` / `setToFun` machinery extends a finitely-additive
set function T to an integral against L1 functions. The reverse direction —
extracting a set function from a continuous linear functional — is the
key construction for Riesz representation.

For φ ∈ (Lp)*, σ-finite μ, define:
  ν(E) = φ(Memℒp.toLp (1_E)) for measurable E with μ(E) < ∞

This defines a signed measure absolutely continuous w.r.t. μ.
-/

/-- The set function induced by a continuous linear functional on Lp.
    For a finite-measure measurable set E, returns φ(1_E). -/
def functionalSetFn (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (E : Set α) (hE : MeasurableSet E)
    (hfin : μ E ≠ ⊤) : ℝ :=
  φ ((indicator_memLp hE hfin p hp hptop).toLp _)

/-- The functional-induced set function vanishes on null sets:
    if μ(E) = 0 then φ(1_E) = 0. This is the AC condition. -/
theorem functionalSetFn_null (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : Lp ℝ p μ →L[ℝ] ℝ) {E : Set α} (hE : MeasurableSet E)
    (hμE : μ E = 0) :
    functionalSetFn p hp hptop φ E hE (by simp [hμE]) = 0 := by
  unfold functionalSetFn
  have h0 : (indicator_memLp hE (by simp [hμE]) p hp hptop).toLp _ = 0 := by
    ext
    simp only [Memℒp.coeFn_toLp, Lp.coeFn_zero]
    filter_upwards [measure_zero_iff_ae_nmem.mp hμE] with x hx
    simp [indicator_apply, hx]
  rw [h0, map_zero]

/-
## Step 4: Radon-Nikodým Gives the Representing Function

Given ν ≪ μ (from Step 2), the Radon-Nikodým theorem yields
g = dν/dμ : α → ℝ. Mathlib provides:

  SignedMeasure.rnDeriv : SignedMeasure α → Measure α → α → ℝ

with the reconstruction property:
  μ.withDensityᵥ (s.rnDeriv μ) = s  when s ≪ μ

The remaining challenge is showing g ∈ Lq and ‖g‖_q = ‖φ‖.
-/

/-- The Radon-Nikodým derivative of a signed measure AC w.r.t. μ
    recovers the original measure via withDensityᵥ.
    This is Mathlib's `SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq`
    applied to our functional-induced measure. -/
theorem rn_reconstruction (s : SignedMeasure α) [hfin : IsFiniteMeasure μ]
    (hac : s.AbsolutelyContinuous μ.toENNRealVectorMeasure) :
    μ.withDensityᵥ (s.rnDeriv μ) = s :=
  SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq.mp hac

/-
## Step 5: Lq Membership of the RN Derivative

This is the key missing piece. Given:
  - φ ∈ (Lp)* with ‖φ‖ = M
  - g = dν/dμ where ν(E) = φ(1_E)

We need to show g ∈ Lq, i.e., ∫ |g|^q dμ < ∞.

### Proof Strategy: Truncation + Hölder Extremizer

Rather than working with g directly (which may not be in Lq a priori),
we use truncations gₙ = max(min(g, n), -n):

1. Each gₙ is bounded and measurable, so gₙ ∈ Lq trivially (finite measure)
2. ‖gₙ‖_q ≤ M uniformly (Hölder extremizer applied to truncations)
3. gₙ → g a.e. and ‖gₙ‖_q is uniformly bounded, so g ∈ Lq (Fatou)

The critical step is (2), which requires the Hölder extremizer argument.
-/

/-- **Sub-goal 5a**: Truncated RN derivative belongs to Lq.
    For bounded measurable g and finite measure, g ∈ Lq trivially. -/
theorem truncated_rn_deriv_memLq [IsFiniteMeasure μ]
    (g : α → ℝ) (hg : Measurable g) (n : ℕ)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (hqtop : q ≠ ⊤) :
    Memℒp (fun a => max (min (g a) (n : ℝ)) (-(n : ℝ))) q μ :=
  Memℒp.of_bound (n : ℝ)
    ((hg.min measurable_const).max measurable_const |>.aestronglyMeasurable)
    (ae_of_all μ (fun a => by
      simp only [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_right _ _, le_trans (min_le_right _ _) (le_max_left _ _)⟩))

/-- **Sub-goal 5b**: Uniform Lq norm bound for truncations.
    If |s(E)| ≤ M · μ(E)^{1/p} for all E, then ‖truncate_n(g)‖_q ≤ M for all n.
    This is the Hölder extremizer argument applied to truncations.
    Requires: ~50 lines of careful norm estimation. -/
theorem truncated_rn_deriv_lq_bound (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ]
    (s : SignedMeasure α) (hac : s.AbsolutelyContinuous μ.toENNRealVectorMeasure)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ (E : Set α), MeasurableSet E →
      |s E| ≤ M * (μ E).toReal ^ (1 / p.toReal))
    (n : ℕ) :
    eLpNorm (fun a => max (min (s.rnDeriv μ a) (n : ℝ)) (-(n : ℝ))) q μ ≤
      ENNReal.ofReal M := by
  sorry

/-- **Infrastructure Gap**: The RN derivative of the functional-induced measure
    belongs to Lq. Uses truncation approach:
    1. Truncated derivatives gₙ ∈ Lq (sub-goal 5a — proved)
    2. ‖gₙ‖_q ≤ M uniformly (sub-goal 5b — sorry)
    3. gₙ → g a.e., so g ∈ Lq by Fatou (routine convergence argument)

    Estimated: ~30 lines once sub-goal 5b is resolved. -/
theorem rn_deriv_memLq (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ]
    (s : SignedMeasure α) (hac : s.AbsolutelyContinuous μ.toENNRealVectorMeasure)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ (E : Set α), MeasurableSet E →
      |s E| ≤ M * (μ E).toReal ^ (1 / p.toReal)) :
    Memℒp (s.rnDeriv μ) q μ := by
  obtain ⟨M, hM, hbnd⟩ := hbound
  have hqtop : q ≠ ⊤ := by
    intro hq; rw [hq, ENNReal.top_toReal] at hpq
    exact absurd hpq.symm.lt_one (by norm_num)
  have hq0 : q ≠ 0 := by
    intro hq; rw [hq, ENNReal.zero_toReal] at hpq
    exact absurd hpq.symm.lt_one (by norm_num)
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  set g := s.rnDeriv μ with hg_def
  have hg_meas : Measurable g := s.measurable_rnDeriv μ
  -- Truncations: gn n a = clamp(g a, -n, n)
  let gn : ℕ → α → ℝ := fun n a => max (min (g a) ↑n) (-↑n)
  have hgn_meas : ∀ n, Measurable (gn n) := fun n =>
    (hg_meas.min measurable_const).max measurable_const
  -- Uniform Lq bound from truncated_rn_deriv_lq_bound
  have hgn_snorm : ∀ n, eLpNorm (gn n) q μ ≤ ENNReal.ofReal M :=
    fun n => truncated_rn_deriv_lq_bound p q hp1 hptop hpq s hac M hM hbnd n
  -- Convert eLpNorm bound to lintegral bound:
  -- eLpNorm f q μ = (∫⁻ ‖f‖₊^q)^(1/q), so eLpNorm ≤ M implies ∫⁻ ‖f‖₊^q ≤ M^q
  have hgn_lint : ∀ n, ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ ≤
      (ENNReal.ofReal M) ^ q.toReal := by
    intro n
    have h := hgn_snorm n
    rw [eLpNorm_eq_lintegral_rpow_nnnorm hq0 hqtop] at h
    -- h : (∫⁻ ‖gn n‖₊^q)^(1/q) ≤ M; raise to q-th power
    calc ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ
        = ((∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ) ^ (1 / q.toReal)) ^ q.toReal := by
            rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hq_pos),
                ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal M) ^ q.toReal := ENNReal.rpow_le_rpow h (le_of_lt hq_pos)
  -- The functions (‖gn n a‖₊ : ℝ≥0∞)^q are monotone in n (since |gn n| = min(|g|,n) ↑ |g|)
  -- and their pointwise sup equals (‖g a‖₊)^q.
  -- MCT (lintegral_iSup) gives ∫⁻ ‖g‖₊^q = ⨆_n ∫⁻ ‖gn n‖₊^q ≤ M^q.
  have hMCT : ∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ =
      ⨆ n, ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ := by
    have abs_clamp : ∀ (r : ℝ) (n : ℕ), |max (min r n) (-(n : ℝ))| = min |r| n := by
      intro r n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rcases le_or_lt r (-(n : ℝ)) with h1 | h1
      · have h1' : r ≤ n := h1.trans (by linarith)
        rw [min_eq_left h1', max_eq_right h1, abs_neg, abs_of_nonneg hn,
            abs_of_nonpos (h1.trans (by linarith)), min_eq_right (by linarith)]
      rcases le_or_lt (n : ℝ) r with h2 | h2
      · rw [min_eq_right h2, max_eq_left (by linarith), abs_of_nonneg hn,
            abs_of_nonneg (hn.trans h2), min_eq_right h2]
      · rw [min_eq_left (le_of_lt h2), max_eq_left (le_of_lt h1),
            min_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
    have sup_min : ∀ (x : ℝ≥0∞), ⨆ n : ℕ, min x n = x := fun x => by
      rcases eq_or_ne x ⊤ with rfl | hx
      · simp [min_eq_right le_top, ENNReal.iSup_natCast]
      · apply le_antisymm (iSup_le fun n => min_le_left x n)
        obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx
        calc x = min x N := (min_eq_left (le_of_lt hN)).symm
          _ ≤ ⨆ n : ℕ, min x n := le_iSup _ N
    have norm_gn_eq : ∀ (a : α) (n : ℕ), (‖gn n a‖₊ : ℝ≥0∞) = min (‖g a‖₊ : ℝ≥0∞) n := by
      intro a n
      rw [← ENNReal.coe_min]; congr 1; apply NNReal.coe_injective
      push_cast [Real.norm_eq_abs]; simp only [gn]; exact abs_clamp (g a) n
    have ptwise_eq : ∀ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal =
        ⨆ n : ℕ, (min (‖g a‖₊ : ℝ≥0∞) n) ^ q.toReal := by
      intro a
      have h := (ENNReal.orderIsoRpow q.toReal hq_pos).map_iSup
          (fun n : ℕ => min (‖g a‖₊ : ℝ≥0∞) n)
      simp only [ENNReal.orderIsoRpow_apply] at h
      rw [sup_min (‖g a‖₊)] at h; exact h
    rw [show (fun a => (‖g a‖₊ : ℝ≥0∞) ^ q.toReal) =
        (fun a => ⨆ n : ℕ, (min (‖g a‖₊ : ℝ≥0∞) n) ^ q.toReal) from funext ptwise_eq,
        lintegral_iSup
          (fun n => (hg_meas.nnnorm.coe_nnreal_ennreal.min measurable_const).pow_const q.toReal)
          (fun ⦃m n⦄ hmn a => ENNReal.rpow_le_rpow
            (min_le_min_left _ (Nat.cast_le.mpr hmn)) (le_of_lt hq_pos))]
    simp_rw [← norm_gn_eq]
  -- Conclude Memℒp: eLpNorm g q μ ≤ ENNReal.ofReal M < ⊤
  refine ⟨hg_meas.aestronglyMeasurable, lt_of_le_of_lt ?_ ENNReal.ofReal_lt_top⟩
  rw [eLpNorm_eq_lintegral_rpow_nnnorm hq0 hqtop]
  -- (∫⁻ ‖g‖₊^q)^(1/q) ≤ (M^q)^(1/q) = M
  calc (∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ) ^ (1 / q.toReal)
      ≤ ((ENNReal.ofReal M) ^ q.toReal) ^ (1 / q.toReal) := by
          apply ENNReal.rpow_le_rpow _ (by positivity)
          rw [hMCT]; exact iSup_le hgn_lint
    _ = ENNReal.ofReal M := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hq_pos.ne',
              ENNReal.rpow_one]

/-- Variant of `rn_deriv_memLq` accepting uniform truncation bounds directly.
    This bypasses the incorrect `truncated_rn_deriv_lq_bound` pathway.
    Used in `riesz_lp_surjective_from_rn` with the Hölder extremizer bound. -/
theorem rn_deriv_memLq_from_trunc (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    (g : α → ℝ) (hg_meas : Measurable g) (M : ℝ)
    (hgn_snorm : ∀ n : ℕ,
        eLpNorm (fun a => max (min (g a) (n : ℝ)) (-(n : ℝ))) q μ ≤ ENNReal.ofReal M) :
    Memℒp g q μ := by
  have hqtop : q ≠ ⊤ := by
    intro hq; rw [hq, ENNReal.top_toReal] at hpq
    exact absurd hpq.symm.lt_one (by norm_num)
  have hq0 : q ≠ 0 := by
    intro hq; rw [hq, ENNReal.zero_toReal] at hpq
    exact absurd hpq.symm.lt_one (by norm_num)
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  let gn : ℕ → α → ℝ := fun n a => max (min (g a) ↑n) (-↑n)
  have hgn_lint : ∀ n, ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ ≤
      (ENNReal.ofReal M) ^ q.toReal := by
    intro n
    have h := hgn_snorm n
    rw [eLpNorm_eq_lintegral_rpow_nnnorm hq0 hqtop] at h
    calc ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ
        = ((∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ) ^ (1 / q.toReal)) ^ q.toReal := by
            rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hq_pos),
                ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal M) ^ q.toReal := ENNReal.rpow_le_rpow h (le_of_lt hq_pos)
  have hMCT : ∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ =
      ⨆ n, ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ := by
    have abs_clamp : ∀ (r : ℝ) (n : ℕ), |max (min r n) (-(n : ℝ))| = min |r| n := by
      intro r n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rcases le_or_lt r (-(n : ℝ)) with h1 | h1
      · have h1' : r ≤ n := h1.trans (by linarith)
        rw [min_eq_left h1', max_eq_right h1, abs_neg, abs_of_nonneg hn,
            abs_of_nonpos (h1.trans (by linarith)), min_eq_right (by linarith)]
      rcases le_or_lt (n : ℝ) r with h2 | h2
      · rw [min_eq_right h2, max_eq_left (by linarith), abs_of_nonneg hn,
            abs_of_nonneg (hn.trans h2), min_eq_right h2]
      · rw [min_eq_left (le_of_lt h2), max_eq_left (le_of_lt h1),
            min_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
    have sup_min : ∀ (x : ℝ≥0∞), ⨆ n : ℕ, min x n = x := fun x => by
      rcases eq_or_ne x ⊤ with rfl | hx
      · simp [min_eq_right le_top, ENNReal.iSup_natCast]
      · apply le_antisymm (iSup_le fun n => min_le_left x n)
        obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx
        calc x = min x N := (min_eq_left (le_of_lt hN)).symm
          _ ≤ ⨆ n : ℕ, min x n := le_iSup _ N
    have norm_gn_eq : ∀ (a : α) (n : ℕ), (‖gn n a‖₊ : ℝ≥0∞) = min (‖g a‖₊ : ℝ≥0∞) n := by
      intro a n
      rw [← ENNReal.coe_min]; congr 1; apply NNReal.coe_injective
      push_cast [Real.norm_eq_abs]; simp only [gn]; exact abs_clamp (g a) n
    have ptwise_eq : ∀ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal =
        ⨆ n : ℕ, (min (‖g a‖₊ : ℝ≥0∞) n) ^ q.toReal := by
      intro a
      have h := (ENNReal.orderIsoRpow q.toReal hq_pos).map_iSup
          (fun n : ℕ => min (‖g a‖₊ : ℝ≥0∞) n)
      simp only [ENNReal.orderIsoRpow_apply] at h
      rw [sup_min (‖g a‖₊)] at h; exact h
    rw [show (fun a => (‖g a‖₊ : ℝ≥0∞) ^ q.toReal) =
        (fun a => ⨆ n : ℕ, (min (‖g a‖₊ : ℝ≥0∞) n) ^ q.toReal) from funext ptwise_eq,
        lintegral_iSup
          (fun n => (hg_meas.nnnorm.coe_nnreal_ennreal.min measurable_const).pow_const q.toReal)
          (fun ⦃m n⦄ hmn a => ENNReal.rpow_le_rpow
            (min_le_min_left _ (Nat.cast_le.mpr hmn)) (le_of_lt hq_pos))]
    simp_rw [← norm_gn_eq]
  refine ⟨hg_meas.aestronglyMeasurable, lt_of_le_of_lt ?_ ENNReal.ofReal_lt_top⟩
  rw [eLpNorm_eq_lintegral_rpow_nnnorm hq0 hqtop]
  calc (∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ) ^ (1 / q.toReal)
      ≤ ((ENNReal.ofReal M) ^ q.toReal) ^ (1 / q.toReal) := by
          apply ENNReal.rpow_le_rpow _ (by positivity)
          rw [hMCT]; exact iSup_le hgn_lint
    _ = ENNReal.ofReal M := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hq_pos.ne', ENNReal.rpow_one]

/-
## Step 6: Integral Representation (Density Argument)

Once g ∈ Lq, we verify φ(f) = ∫ fg dμ using Mathlib's `Lp.induction`.

### Proof via Lp.induction

To show φ(f) = ∫ fg for all f ∈ Lp, it suffices to verify:
1. **Indicator case**: φ(c · 1_E) = ∫ (c · 1_E) · g for measurable E, μ(E) < ∞
   → Follows from `hagree` hypothesis + linearity
2. **Addition case**: P(f) ∧ P(g) ∧ disjoint support → P(f+g)
   → Follows from linearity of φ and integral
3. **Closedness**: {f ∈ Lp | φ(f) = ∫ fg} is closed
   → Follows from continuity of φ and f ↦ ∫fg (Hölder)

### Infrastructure needed for closedness

The continuity of f ↦ ∫fg on Lp follows from Hölder:
  |∫ fg - ∫ f'g| = |∫ (f-f')g| ≤ ‖f-f'‖_p · ‖g‖_q

This makes f ↦ ∫fg a CLM on Lp, so {f | φ f = ∫fg} = ker(φ - Λ_g) is closed.
-/

/-- **Bridge lemma**: Product of Lp and Lq functions has finite L1 lintegral.
    This is the lintegral-level Hölder inequality applied to norms. -/
theorem lintegral_mul_le_of_memLp (p q : ℝ≥0∞)
    (hpq : p.toReal.HolderConjugate q.toReal) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} {g : α → ℝ} (hf : Memℒp f p μ) (hg : Memℒp g q μ) :
    ∫⁻ a, ‖f a * g a‖₊ ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  calc ∫⁻ a, ‖f a * g a‖₊ ∂μ
      = ∫⁻ a, (‖f a‖₊ * ‖g a‖₊) ∂μ := by
        congr 1; ext a; simp [nnnorm_mul]
    _ ≤ (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) *
        (∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ) ^ (1 / q.toReal) := by
        apply ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq
        · exact hf.aestronglyMeasurable.ennnorm.aemeasurable
        · exact hg.aestronglyMeasurable.ennnorm.aemeasurable
    _ = eLpNorm f p μ * eLpNorm g q μ := by
        -- Unfold eLpNorm to eLpNorm' for 0 < p < ⊤ (and similarly for q)
        have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
        have hq0 : q ≠ 0 := by
          intro hq; rw [hq, ENNReal.zero_toReal] at hpq
          exact absurd hpq.symm.lt_one (by norm_num)
        have hqtop : q ≠ ⊤ := by
          intro hq; rw [hq, ENNReal.top_toReal] at hpq
          exact absurd hpq.symm.lt_one (by norm_num)
        simp only [eLpNorm, hp0, hptop, hq0, hqtop, ite_false, eLpNorm']

/-- Product of Lp and Lq functions is integrable (L1). -/
theorem integrable_mul_of_memLp (p q : ℝ≥0∞)
    (hpq : p.toReal.HolderConjugate q.toReal) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} {g : α → ℝ} (hf : Memℒp f p μ) (hg : Memℒp g q μ) :
    Integrable (fun a => f a * g a) μ := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨hf.aestronglyMeasurable.mul hg.aestronglyMeasurable, ?_⟩
  calc eLpNorm (fun a => f a * g a) 1 μ
      = ∫⁻ a, ‖f a * g a‖₊ ∂μ := by simp [eLpNorm, eLpNorm']
    _ ≤ eLpNorm f p μ * eLpNorm g q μ :=
        lintegral_mul_le_of_memLp p q hpq hp hptop hf hg
    _ < ⊤ := ENNReal.mul_lt_top hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne

/-- **Infrastructure**: Integration against g ∈ Lq defines a CLM on Lp.
    This is the functional-analytic form of Hölder's inequality.

    Construction via LinearMap.mkContinuous:
    - Linear map: f ↦ ∫ (↑f) · g ∂μ (linear by linearity of integral)
    - Bound: |∫ fg| ≤ ‖g‖_q · ‖f‖_p (Hölder's inequality)

    Bridge: lintegral Hölder → Bochner integral bound via norm_integral_le. -/
noncomputable def integrationCLM (p q : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    [Fact (1 ≤ p)]
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ]
    (g : α → ℝ) (hg : Memℒp g q μ) :
    Lp ℝ p μ →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous ?_ (eLpNorm g q μ).toReal ?_
  · -- Linear map: f ↦ ∫ (↑f) * g ∂μ
    exact {
      toFun := fun f => ∫ a, (f : α → ℝ) a * g a ∂μ
      map_add' := fun f₁ f₂ => by
        have h1 := integrable_mul_of_memLp p q hpq hp hptop (Lp.memℒp f₁) hg
        have h2 := integrable_mul_of_memLp p q hpq hp hptop (Lp.memℒp f₂) hg
        simp only [Lp.coeFn_add, Pi.add_apply, add_mul]
        exact integral_add h1 h2
      map_smul' := fun c f => by
        simp only [Lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [show (fun a => c * (f : α → ℝ) a * g a) = (fun a => c * ((f : α → ℝ) a * g a))
            from by ext a; ring]
        exact integral_const_mul c _ }
  · -- Bound: ‖∫ fg‖ ≤ ‖g‖_Lq * ‖f‖_Lp
    intro f
    -- Chain: ‖∫ fg‖ ≤ ∫ ‖fg‖ ≤ (∫⁻ ‖fg‖₊).toReal ≤ (eLpNorm f p * eLpNorm g q).toReal
    have hint := integrable_mul_of_memLp p q hpq hp hptop (Lp.memℒp f) hg
    calc ‖∫ a, (f : α → ℝ) a * g a ∂μ‖
        ≤ ∫ a, ‖(f : α → ℝ) a * g a‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ (eLpNorm (f : α → ℝ) p μ * eLpNorm g q μ).toReal := by
          rw [← integral_norm_eq_lintegral_nnnorm hint.aestronglyMeasurable]
          · apply ENNReal.toReal_mono
            · exact ENNReal.mul_ne_top (Lp.memℒp f).eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne
            · exact lintegral_mul_le_of_memLp p q hpq hp hptop (Lp.memℒp f) hg
      _ = (eLpNorm g q μ).toReal * ‖f‖ := by
          rw [ENNReal.toReal_mul, mul_comm]
          -- ‖f‖ in Lp is (eLpNorm (↑f) p μ).toReal by definition
          rfl

/-- The integration CLM computes ∫ fg. -/
theorem integrationCLM_apply (p q : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    [Fact (1 ≤ p)]
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ]
    (g : α → ℝ) (hg : Memℒp g q μ) (f : Lp ℝ p μ) :
    integrationCLM p q hp hptop hpq g hg f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  simp [integrationCLM, LinearMap.mkContinuous_apply]

/-- The integral representation extends from indicator functions to all of Lp.

    Proof uses Mathlib's `Lp.induction` with:
    - Indicator case: from `hagree` + linearity of φ
    - Addition case: linearity of φ and integral (PROVED)
    - Closedness: ker(φ - integrationCLM) is closed (PROVED, modulo integrationCLM)

    Remaining sorry: `integrationCLM` construction (~40 lines of Hölder). -/
theorem integral_representation (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (g : α → ℝ) (hg : Memℒp g q μ)
    (hagree : ∀ (E : Set α), MeasurableSet E → μ E ≠ ⊤ →
      φ ((indicator_memLp (p := p) ‹_› ‹_› p (le_of_lt hp1) hptop).toLp _) =
      ∫ a in E, g a ∂μ) :
    ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  haveI hp1' : Fact (1 ≤ p) := ⟨le_of_lt hp1⟩
  -- Construct the integration CLM
  set Λ := integrationCLM p q (le_of_lt hp1) hptop hpq g hg
  -- The difference φ - Λ is a CLM; suffices to show it vanishes on all of Lp
  set ψ := φ - Λ
  suffices h : ∀ f : Lp ℝ p μ, ψ f = 0 by
    intro f
    have := h f
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero] at this
    rw [this, integrationCLM_apply]
  -- Apply Lp.induction: prove ψ = 0 on indicators + addition + closedness
  intro f
  apply Lp.induction hptop
    (motive := fun f => ψ f = 0)
  -- Case 1: c · 1_E (indicator constant)
  · intro c s hs hμs
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero]
    rw [Lp.simpleFunc.coe_indicatorConst]
    -- Step A: indicatorConstLp c = c • (1_s in Lp), proved by a.e. equality
    have heq : indicatorConstLp p hs hμs.ne c =
        c • (indicator_memLp hs hμs.ne p (le_of_lt hp1) hptop).toLp _ := by
      rw [Lp.ext_iff]
      filter_upwards [indicatorConstLp_coeFn,
        Lp.coeFn_smul c ((indicator_memLp hs hμs.ne p (le_of_lt hp1) hptop).toLp _),
        (indicator_memLp hs hμs.ne p (le_of_lt hp1) hptop).coeFn_toLp] with x hxc hxsmul hx1
      rw [hxc, hxsmul, Pi.smul_apply, hx1, smul_eq_mul,
          Set.indicator_apply, Set.indicator_apply]
      split_ifs <;> ring
    -- Step B: φ(c • 1_s) = c * φ(1_s) = c * ∫_s g  (linearity + hagree)
    have hlhs : φ (indicatorConstLp p hs hμs.ne c) = c * ∫ a in s, g a ∂μ := by
      rw [heq, map_smul, smul_eq_mul]; congr 1; exact hagree s hs hμs.ne
    -- Step C: Λ(c • 1_s) = c * Λ(1_s) = c * ∫_s g  (integrationCLM_apply + integral_indicator)
    have hrhs : Λ (indicatorConstLp p hs hμs.ne c) = c * ∫ a in s, g a ∂μ := by
      rw [heq, map_smul, smul_eq_mul, integrationCLM_apply]; congr 1
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [(indicator_memLp hs hμs.ne p (le_of_lt hp1) hptop).coeFn_toLp] with x hx
      rw [hx, Set.indicator_apply, Set.indicator_apply]; split_ifs <;> ring
    rw [hlhs, hrhs]
  -- Case 2: f + g with disjoint support → P(f) ∧ P(g) → P(f+g)
  · intro f' g' hf' hg' _hdisj hPf hPg
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero] at *
    -- Both sides are linear: φ(f'+g') = φ(f')+φ(g'), Λ(f'+g') = Λ(f')+Λ(g')
    rw [map_add, map_add, hPf, hPg]
  -- Case 3: {f | ψ f = 0} is closed (kernel of a CLM)
  · exact isClosed_eq ψ.continuous continuous_const
  -- QED via induction
  exact f

/-
## Intermediate Lemmas for the Main Theorem

Three focused sorries replace the single monolithic sorry in
`riesz_lp_surjective_from_rn`:

1. `indicator_lp_hasSum` — HasSum of Lp indicator functions
   (Lp-convergence of partial sums of disjoint indicators)
2. `rnDeriv_integrable_of_finite` — ν.rnDeriv μ ∈ L1
   (Jordan decomposition + Measure.integrable_rnDeriv for finite measures)
3. `holder_extremizer_lq_bound` — Hölder extremizer gives ‖gₙ‖_q ≤ ‖φ‖
   (extremizer h = sign(gₙ)|gₙ|^{q-1} and the norm computation)

The main theorem proof below assembles these pieces without sorry.
-/

/-- **HasSum of Lp indicator functions** for a pairwise disjoint partition.
    The Lp partial sums ∑_{i<N} 1_{f i} converge in Lp norm to 1_{⋃ f i}.

    Proof sketch: eLpNorm (1_{⋃_{i≥N} f_i}) p μ = μ(⋃_{i≥N} f i)^{1/p} → 0
    because ∑_{i≥N} μ(f i) → 0 (finite total measure, tail of convergent series).
    The disjointness ensures the difference 1_{⋃ f} - ∑_{i<N} 1_{f i} = 1_{⋃_{i≥N} f i} a.e. -/
private theorem indicator_lp_hasSum [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : ℕ → Set α} (hf_meas : ∀ i, MeasurableSet (f i))
    (hf_disj : Pairwise (Disjoint on f)) :
    HasSum
      (fun i => (indicator_memLp (hf_meas i) (measure_ne_top μ _) p hp hptop).toLp _)
      ((indicator_memLp (MeasurableSet.iUnion hf_meas) (measure_ne_top μ _) p hp hptop).toLp _) := by
  haveI hpfact : Fact (1 ≤ p) := ⟨hp⟩
  -- Identify each term with indicatorConstLp (the canonical Lp indicator)
  have hg_eq : ∀ i, (indicator_memLp (hf_meas i) (measure_ne_top μ _) p hp hptop).toLp _ =
      indicatorConstLp p (hf_meas i) (measure_ne_top μ _) (1 : ℝ) := fun i =>
    Lp.ext (by
      filter_upwards [(indicator_memLp (hf_meas i) (measure_ne_top μ _) p hp hptop).coeFn_toLp,
                      indicatorConstLp_coeFn (hs := hf_meas i) (hμs := measure_ne_top μ _)]
        with x h1 h2; exact h1.trans h2.symm)
  have hg∞_eq :
      (indicator_memLp (MeasurableSet.iUnion hf_meas) (measure_ne_top μ _) p hp hptop).toLp _ =
      indicatorConstLp p (MeasurableSet.iUnion hf_meas) (measure_ne_top μ _) (1 : ℝ) :=
    Lp.ext (by
      filter_upwards
          [(indicator_memLp (MeasurableSet.iUnion hf_meas) (measure_ne_top μ _) p hp hptop).coeFn_toLp,
           indicatorConstLp_coeFn (hs := MeasurableSet.iUnion hf_meas)
             (hμs := measure_ne_top μ _)]
        with x h1 h2; exact h1.trans h2.symm)
  simp_rw [hg_eq, hg∞_eq]
  -- Total measure of the disjoint union is finite
  have hμ_fin : ∑' i, μ (f i) ≠ ∞ :=
    (measure_iUnion hf_disj hf_meas).symm ▸ measure_ne_top μ _
  -- Step 1: coercion of Lp partial sum = pointwise sum of indicators (a.e.)
  have hcoe_sum : ∀ S : Finset ℕ,
      ⇑(∑ i ∈ S, indicatorConstLp p (hf_meas i) (measure_ne_top μ _) (1 : ℝ)) =ᵐ[μ]
      fun x => ∑ i ∈ S, (f i).indicator (fun _ => (1 : ℝ)) x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      filter_upwards [Lp.coeFn_zero (E := ℝ) p μ] with x hx
      simp only [Finset.sum_empty, hx, Pi.zero_apply]
    | insert ha ih =>
      simp only [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add
                        (indicatorConstLp p (hf_meas _) (measure_ne_top μ _) (1 : ℝ))
                        (∑ i ∈ _, indicatorConstLp p (hf_meas i) (measure_ne_top μ _) (1 : ℝ)),
                      indicatorConstLp_coeFn (hs := hf_meas _) (hμs := measure_ne_top μ _), ih]
        with x hadd h1 hS
      simp only [Pi.add_apply]
      rw [hadd, h1, hS]
  -- Step 2: partial Lp sums equal indicatorConstLp of partial biUnion
  have hsum_eq : ∀ S : Finset ℕ,
      ∑ i ∈ S, indicatorConstLp p (hf_meas i) (measure_ne_top μ _) (1 : ℝ) =
      indicatorConstLp p (S.measurableSet_biUnion (fun i _ => hf_meas i))
        (measure_ne_top μ _) (1 : ℝ) := fun S =>
    Lp.ext (by
      filter_upwards [hcoe_sum S, indicatorConstLp_coeFn
          (hs := S.measurableSet_biUnion (fun i _ => hf_meas i)) (hμs := measure_ne_top μ _)]
        with x hS hU
      rw [hS, hU]
      exact (Finset.indicator_biUnion_apply S f (fun i _ j _ hij => hf_disj hij) x).symm)
  -- Step 3: HasSum reduces to Tendsto atTop (definitional unfolding)
  show Tendsto (fun S : Finset ℕ =>
    ∑ i ∈ S, indicatorConstLp p (hf_meas i) (measure_ne_top μ _) (1 : ℝ))
    atTop (nhds (indicatorConstLp p (MeasurableSet.iUnion hf_meas) (measure_ne_top μ _) (1 : ℝ)))
  -- Rewrite partial sums using hsum_eq, then apply tendsto_indicatorConstLp_set
  simp_rw [hsum_eq]
  apply tendsto_indicatorConstLp_set hptop
  -- Goal: Tendsto (fun S => μ (symmDiff (⋃ i ∈ S, f i) (⋃ i, f i))) atTop (nhds 0)
  -- Key equality: symmDiff (⋃ i ∈ S, f i) (⋃ i, f i) = ⋃ i ∉ S, f i
  have key : ∀ S : Finset ℕ,
      μ (symmDiff (⋃ i ∈ S, f i) (⋃ i, f i)) = ∑' b : {x // x ∉ S}, μ (f b) := fun S => by
    rw [symmDiff_of_le (Set.iUnion₂_subset (fun i _ => Set.subset_iUnion f i))]
    -- Now: μ ((⋃ i, f i) \ (⋃ i ∈ S, f i)) = ∑' b : {x // x ∉ S}, μ (f b)
    have hdiff_eq : (⋃ i, f i) \ (⋃ i ∈ S, f i) = ⋃ b : {x // x ∉ S}, f b.val := by
      rw [← Set.iUnion_subtype (fun i => i ∉ S)]
      ext x
      simp only [Set.mem_diff, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq,
                 not_exists, not_and]
      constructor
      · rintro ⟨⟨i, hi⟩, hnotS⟩
        exact ⟨i, fun hiS => hnotS ⟨i, hiS, hi⟩, hi⟩
      · rintro ⟨i, hinotS, hi⟩
        exact ⟨⟨i, hi⟩, fun ⟨j, hjS, hj⟩ =>
          absurd hj (Set.disjoint_left.mp (hf_disj (fun h => hinotS (h ▸ hjS))) hi)⟩
    rw [hdiff_eq]
    exact measure_iUnion (fun ⟨i, _⟩ ⟨j, _⟩ hij => hf_disj (Subtype.val_injective.ne hij))
      (fun ⟨i, _⟩ => hf_meas i)
  simp_rw [key]
  exact ENNReal.tendsto_tsum_compl_atTop_zero hμ_fin

/-- **σ-additivity** of the set function E ↦ φ(1_E).
    Follows from `indicator_lp_hasSum` by applying φ (a CLM, hence continuous). -/
private theorem functional_hasSum_parts [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : Lp ℝ p μ →L[ℝ] ℝ)
    {f : ℕ → Set α} (hf_meas : ∀ i, MeasurableSet (f i))
    (hf_disj : Pairwise (Disjoint on f)) :
    HasSum (fun i => functionalSetFn p hp hptop φ (f i) (hf_meas i) (measure_ne_top μ _))
      (functionalSetFn p hp hptop φ (⋃ i, f i) (MeasurableSet.iUnion hf_meas)
          (measure_ne_top μ _)) := by
  -- Each value = φ(indicator in Lp); apply φ (continuous AddMonoidHom) to the HasSum
  simp only [functionalSetFn]
  exact (indicator_lp_hasSum p hp hptop hf_meas hf_disj).map
    φ.toLinearMap.toAddMonoidHom φ.continuous

/-- Construct a **signed measure from a bounded Lp functional** in a finite measure space.
    ν(E) = φ(1_E) for measurable E, extended by 0 for non-measurable sets.
    σ-additivity follows from `functional_hasSum_parts`. -/
noncomputable def signedMeasureOfFunctional [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : Lp ℝ p μ →L[ℝ] ℝ) : SignedMeasure α where
  measureOf := fun E =>
    if hE : MeasurableSet E then functionalSetFn p hp hptop φ E hE (measure_ne_top μ E) else 0
  empty := by
    simp only [dif_pos MeasurableSet.empty]
    -- functionalSetFn φ ∅ = φ(1_∅) = φ(0) = 0 (since μ(∅) = 0 → 1_∅ = 0 in Lp)
    exact functionalSetFn_null p hp hptop φ MeasurableSet.empty measure_empty
  not_measurable := fun E hE => by simp [hE]
  m_iUnion := fun hf_disj hf_meas => by
    simp only [dif_pos (hf_meas _), dif_pos (MeasurableSet.iUnion hf_meas)]
    exact functional_hasSum_parts p hp hptop φ hf_meas hf_disj

/-- The signed measure from φ agrees with φ on indicator functions. -/
private theorem signedMeasureOfFunctional_indicator [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤) (φ : Lp ℝ p μ →L[ℝ] ℝ)
    {E : Set α} (hE : MeasurableSet E) :
    signedMeasureOfFunctional p hp hptop φ E =
      φ ((indicator_memLp hE (measure_ne_top μ E) p hp hptop).toLp _) := by
  simp [signedMeasureOfFunctional, dif_pos hE, functionalSetFn]

/-- The signed measure from φ is absolutely continuous w.r.t. μ.
    Follows from `functionalSetFn_null`: if μ(E) = 0 then φ(1_E) = 0. -/
private theorem signedMeasureOfFunctional_ac [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤) (φ : Lp ℝ p μ →L[ℝ] ℝ) :
    (signedMeasureOfFunctional p hp hptop φ).AbsolutelyContinuous
        μ.toENNRealVectorMeasure := by
  -- AbsolutelyContinuous: ∀ s, μ.toENNRealVectorMeasure s = 0 → ν s = 0
  intro s hμs
  simp only [signedMeasureOfFunctional]
  by_cases hE : MeasurableSet s
  · simp only [dif_pos hE]
    -- μ.toENNRealVectorMeasure s = 0 → μ s = 0 (for measurable s)
    have hzero : μ s = 0 := by
      rwa [Measure.toENNRealVectorMeasure_apply hE] at hμs
    exact functionalSetFn_null p hp hptop φ hE hzero
  · simp [dif_neg hE]

/-- **RN derivative integrability**: for a finite signed measure ν ≪ μ (σ-finite),
    the RN derivative ν.rnDeriv μ is μ-integrable.

    Proof via Jordan decomposition:
    ν.rnDeriv μ = ν.posPart.rnDeriv μ - ν.negPart.rnDeriv μ (by definition).
    Both parts are finite positive measures (Jordan decomp of signed measure ≪ finite μ),
    so each rnDeriv is integrable by `Measure.integrable_rnDeriv`. -/
private theorem rnDeriv_integrable_of_finite [IsFiniteMeasure μ]
    (ν : SignedMeasure α)
    (hac : ν.AbsolutelyContinuous μ.toENNRealVectorMeasure) :
    Integrable (ν.rnDeriv μ) μ :=
  SignedMeasure.integrable_rnDeriv ν μ

/-- **RN derivative reconstructs ν on sets**: ν E = ∫_E (ν.rnDeriv μ) dμ.
    Proof: rn_reconstruction gives μ.withDensityᵥ (ν.rnDeriv μ) = ν;
    withDensityᵥ_apply then gives the integral formula. -/
private theorem rnDeriv_integral_eq [IsFiniteMeasure μ]
    (ν : SignedMeasure α)
    (hac : ν.AbsolutelyContinuous μ.toENNRealVectorMeasure)
    {E : Set α} (hE : MeasurableSet E) :
    ν E = ∫ a in E, ν.rnDeriv μ a ∂μ := by
  have hrec := rn_reconstruction ν hac
  have hint := rnDeriv_integrable_of_finite ν hac
  -- hrec : μ.withDensityᵥ (ν.rnDeriv μ) = ν (as SignedMeasures)
  -- rewrite ν E as (μ.withDensityᵥ g) E, then apply withDensityᵥ_apply
  conv_lhs => rw [← hrec]
  exact Measure.withDensityᵥ_apply hint hE

/-- **Hölder extremizer bound**: for gₙ = clamp(g, -n, n) where g = ν.rnDeriv μ,
    eLpNorm gₙ q μ ≤ ENNReal.ofReal ‖φ‖.

    The extremizer h_n = sign(gₙ)|gₙ|^{q-1} satisfies ‖h_n‖_p = ‖gₙ‖_q^{q/p}, and:
      ‖gₙ‖_q^q = ∫ h_n gₙ ≤ ∫ h_n g = φ(h_n as Lp) ≤ ‖φ‖·‖h_n‖_p = ‖φ‖·‖gₙ‖_q^{q/p}
    Dividing: ‖gₙ‖_q^{q-q/p} = ‖gₙ‖_q ≤ ‖φ‖ (using (q-q/p) = 1 when 1/p + 1/q = 1).

    The identity ∫ h_n g = φ(h_n) extends from indicator agreement via:
    simple-function approximation + φ continuity + DCT (g ∈ L1 from rnDeriv_integrable). -/
private theorem holder_extremizer_lq_bound [IsFiniteMeasure μ] [SigmaFinite μ]
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (ν : SignedMeasure α)
    (hac : ν.AbsolutelyContinuous μ.toENNRealVectorMeasure)
    (hν_eq : ∀ (E : Set α) (hE : MeasurableSet E),
        ν E = φ ((indicator_memLp hE (measure_ne_top μ E) p (le_of_lt hp1) hptop).toLp _))
    (n : ℕ) :
    eLpNorm (fun a => max (min (ν.rnDeriv μ a) (n : ℝ)) (-(n : ℝ))) q μ ≤
      ENNReal.ofReal ‖φ‖ := by
  sorry

/-
## Main Theorem: Riesz Representation for Lp (Surjectivity)

Combining all steps: given φ ∈ (Lp)*, construct g ∈ Lq with φ(f) = ∫ fg dμ.

Proof structure (previously a single sorry, now assembled from focused sorries):
1. SignedMeasure ν(E) = φ(1_E) via signedMeasureOfFunctional
   (σ-additivity from indicator_lp_hasSum + CLM continuity)
2. g = ν.rnDeriv μ (measurable by definition)
3. Agreement φ(1_E) = ∫_E g via rnDeriv_integral_eq + signedMeasureOfFunctional_indicator
4. g ∈ Lq via holder_extremizer_lq_bound + rn_deriv_memLq_from_trunc
5. Full φ(f) = ∫ fg via integral_representation (Lp.induction, already proved)

Remaining focused sorries: indicator_lp_hasSum, rnDeriv_integrable_of_finite,
holder_extremizer_lq_bound.
-/

/-- **Riesz Representation for Lp** (surjectivity direction).
    Every bounded linear functional on Lp is represented by integration
    against an Lq function, where 1/p + 1/q = 1, 1 < p < ∞.

    This theorem, once the infrastructure sorries are resolved,
    eliminates the `riesz_lp_surjective` axiom from the parent file. -/
theorem riesz_lp_surjective_from_rn (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, Memℒp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  intro φ
  haveI hp1' : Fact (1 ≤ p) := ⟨le_of_lt hp1⟩
  -- Step 1: Construct signed measure ν(E) = φ(1_E)
  let ν := signedMeasureOfFunctional p (le_of_lt hp1) hptop φ
  have hac : ν.AbsolutelyContinuous μ.toENNRealVectorMeasure :=
    signedMeasureOfFunctional_ac p (le_of_lt hp1) hptop φ
  have hν_eq : ∀ (E : Set α) (hE : MeasurableSet E),
      ν E = φ ((indicator_memLp hE (measure_ne_top μ E) p (le_of_lt hp1) hptop).toLp _) :=
    fun E hE => signedMeasureOfFunctional_indicator p (le_of_lt hp1) hptop φ hE
  -- Step 2: RN derivative g = dν/dμ
  set g := ν.rnDeriv μ with hg_def
  have hg_meas : Measurable g := ν.measurable_rnDeriv μ
  -- Step 3: Agreement on indicators φ(1_E) = ∫_E g dμ
  have hagree : ∀ (E : Set α), MeasurableSet E → μ E ≠ ⊤ →
      φ ((indicator_memLp (p := p) ‹_› ‹_› p (le_of_lt hp1) hptop).toLp _) =
      ∫ a in E, g a ∂μ := by
    intro E hE hfin  -- hfin : μ E ≠ ⊤ (needed for ‹μ E ≠ ⊤› in indicator_memLp)
    -- φ(1_E) = ν E (from hν_eq) = ∫_E g (from rnDeriv_integral_eq)
    rw [← hν_eq E hE]
    exact rnDeriv_integral_eq ν hac hE
  -- Step 4: g ∈ Lq via Hölder extremizer + rn_deriv_memLq_from_trunc
  have hg_Lq : Memℒp g q μ :=
    rn_deriv_memLq_from_trunc p q hp1 hptop hpq g hg_meas ‖φ‖
      (fun n => holder_extremizer_lq_bound p q hp1 hptop hpq φ ν hac hν_eq n)
  -- Step 5: Full representation via integral_representation (Lp.induction)
  exact ⟨g, hg_Lq, integral_representation p q hp1 hptop hpq φ g hg_Lq hagree⟩

/-
## Assessment Summary (Updated 2026-04-22)

### What This File Proves (no sorry)
1. Indicator functions are in Lp for finite-measure sets
2. The functional-induced set function vanishes on null sets
3. RN reconstruction: withDensityᵥ (rnDeriv) = s for AC measures
4. Truncated RN derivative is in Lq for finite measures (Sub-goal 5a)
5. **MCT for truncations**: ∫⁻ ‖g‖₊^q = ⨆_n ∫⁻ ‖gₙ‖₊^q (proved via lintegral_iSup)
6. **rn_deriv_memLq** (modulo `truncated_rn_deriv_lq_bound` sorry — MARKED FALSE, dead path)
7. **rn_deriv_memLq_from_trunc**: COMPLETE sorry-free Lq membership from truncation bounds
8. **Integral representation** via Lp.induction (all 3 cases proved)
9. lintegral Hölder, Bochner integrability from Lp×Lq, integrationCLM
10. **signedMeasureOfFunctional**: signed measure construction from φ (COMPLETE — no sorry)
11. **signedMeasureOfFunctional_ac**: absolute continuity (complete, no sorry)
12. **rnDeriv_integral_eq**: ν E = ∫_E g (complete, no sorry)
13. **rnDeriv_integrable_of_finite**: g = ν.rnDeriv μ ∈ L1 (complete via SignedMeasure.integrable_rnDeriv)
14. **indicator_lp_hasSum**: HasSum of Lp indicator functions (PROVED in session 4)
15. **riesz_lp_surjective_from_rn**: PROOF STRUCTURE COMPLETE (1 remaining sorry)

### Focused Sorries (2 total, 1 on critical path)
1. `truncated_rn_deriv_lq_bound` — MARKED FALSE (set function bound approach; dead path)
2. `holder_extremizer_lq_bound` — ‖gₙ‖_q ≤ ‖φ‖ uniformly (~100 lines)
   Proof: extremizer h = sign(gₙ)|gₙ|^{q-1}, ‖gₙ‖_q^q ≤ ∫ h·g = φ(h) ≤ ‖φ‖·‖gₙ‖_q^{q/p}
   Hard step: extend φ(1_E) = ∫_E g to bounded functions via SimpleFunc.approxOn + DCT
   Tools needed: SimpleFunc.tendsto_approxOn, tendsto_integral_of_dominated_convergence

### Key Progress (2026-04-22 Session 4) — indicator_lp_hasSum PROVED
- Proved indicator_lp_hasSum (the σ-additivity step): ~80 lines
  Uses: indicatorConstLp_coeFn, Lp.ext, Finset.indicator_biUnion_apply (additive),
        tendsto_indicatorConstLp_set, symmDiff_of_le, Set.iUnion_subtype,
        measure_iUnion, ENNReal.tendsto_tsum_compl_atTop_zero
- Key insight: HasSum is definitionally Tendsto atTop (via @[simps] def unconditional)
  so `show Tendsto ... atTop ...` works after `simp_rw [hsum_eq]`

### Path to Completion (1 remaining critical sorry)
`holder_extremizer_lq_bound` (~100 lines):
1. Build hn = sign(gₙ)|gₙ|^{q-1} ∈ Lp (bounded by n^{q-1}, finite measure)
2. Simple function agreement: for sₙ → hn via SimpleFunc.approxOn:
   φ(sₙ) = ∫ sₙ·g (by indicator linearity + hν_eq + rnDeriv_integral_eq)
   ∫ sₙ·g → ∫ hn·g (by tendsto_integral_of_dominated_convergence with bound n^{q-1}·|g| ∈ L1)
   φ(hn) = ∫ hn·g by continuity of φ
3. Chain: ‖gₙ‖_q^q = ∫ hn·gₙ ≤ ∫ hn·g = φ(hn) ≤ ‖φ‖·‖hn‖_p = ‖φ‖·‖gₙ‖_q^{q/p}
4. Algebra: ‖gₙ‖_q ≤ ‖φ‖ (q - q/p = 1 from 1/p + 1/q = 1)
-/

end RieszLpSurjectivity

end
