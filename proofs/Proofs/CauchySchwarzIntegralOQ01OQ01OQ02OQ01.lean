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
    MemLp (E.indicator (fun _ => (1 : ℝ))) p μ := by
  apply MemLp.indicator hE
  exact memLp_const 1

/-
## Step 3: From Functional to Signed Measure via setToFun

Mathlib's `setToL1` / `setToFun` machinery extends a finitely-additive
set function T to an integral against L1 functions. The reverse direction —
extracting a set function from a continuous linear functional — is the
key construction for Riesz representation.

For φ ∈ (Lp)*, σ-finite μ, define:
  ν(E) = φ(MemLp.toLp (1_E)) for measurable E with μ(E) < ∞

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
    have hae : E.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] 0 := by
      filter_upwards [measure_zero_iff_ae_nmem.mp hμE] with x hx
      simp [indicator_apply, hx]
    rw [MemLp.toLp_congr _ MemLp.zero hae]
    exact MemLp.zero.toLp_zero
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
  SignedMeasure.withDensityᵥ_rnDeriv_eq s μ hac

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
    MemLp (fun a => max (min (g a) (n : ℝ)) (-(n : ℝ))) q μ :=
  MemLp.of_bound
    ((hg.min measurable_const).max measurable_const |>.aestronglyMeasurable)
    (n : ℝ)
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
    MemLp (s.rnDeriv μ) q μ := by
  obtain ⟨M, hM, hbnd⟩ := hbound
  have hqtop : q ≠ ⊤ := by
    intro hq; rw [hq, ENNReal.toReal_top] at hpq
    exact absurd hpq.symm.lt_one (by norm_num)
  have hq0 : q ≠ 0 := by
    intro hq; rw [hq, ENNReal.toReal_zero] at hpq
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
    rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop] at h
    simp_rw [enorm_eq_nnnorm] at h
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
      rcases le_or_gt r (-(n : ℝ)) with h1 | h1
      · have h1' : r ≤ n := h1.trans (by linarith)
        rw [min_eq_left h1', max_eq_right h1, abs_neg, abs_of_nonneg hn,
            abs_of_nonpos (h1.trans (by linarith)), min_eq_right (by linarith)]
      rcases le_or_gt (n : ℝ) r with h2 | h2
      · rw [min_eq_right h2, max_eq_left (by linarith), abs_of_nonneg hn,
            abs_of_nonneg (hn.trans h2), min_eq_right h2]
      · rw [min_eq_left (le_of_lt h2), max_eq_left (le_of_lt h1),
            min_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
    have sup_min : ∀ (x : ℝ≥0∞), ⨆ n : ℕ, min x n = x := fun x => by
      rcases eq_or_ne x ⊤ with rfl | hx
      · simp [min_eq_right le_top, ENNReal.iSup_natCast]
      · refine le_antisymm ?_ ?_
        · exact iSup_le fun n => min_le_left x n
        · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx
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
  -- Conclude MemLp: eLpNorm g q μ ≤ ENNReal.ofReal M < ⊤
  refine ⟨hg_meas.aestronglyMeasurable, lt_of_le_of_lt ?_ ENNReal.ofReal_lt_top⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop]
  simp_rw [enorm_eq_nnnorm]
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
    MemLp g q μ := by
  have hqtop : q ≠ ⊤ := by
    intro hq; rw [hq, ENNReal.toReal_top] at hpq
    exact absurd hpq.symm.lt_one (by norm_num)
  have hq0 : q ≠ 0 := by
    intro hq; rw [hq, ENNReal.toReal_zero] at hpq
    exact absurd hpq.symm.lt_one (by norm_num)
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  let gn : ℕ → α → ℝ := fun n a => max (min (g a) ↑n) (-↑n)
  have hgn_lint : ∀ n, ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ ≤
      (ENNReal.ofReal M) ^ q.toReal := by
    intro n
    have h := hgn_snorm n
    rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop] at h
    simp_rw [enorm_eq_nnnorm] at h
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
      rcases le_or_gt r (-(n : ℝ)) with h1 | h1
      · have h1' : r ≤ n := h1.trans (by linarith)
        rw [min_eq_left h1', max_eq_right h1, abs_neg, abs_of_nonneg hn,
            abs_of_nonpos (h1.trans (by linarith)), min_eq_right (by linarith)]
      rcases le_or_gt (n : ℝ) r with h2 | h2
      · rw [min_eq_right h2, max_eq_left (by linarith), abs_of_nonneg hn,
            abs_of_nonneg (hn.trans h2), min_eq_right h2]
      · rw [min_eq_left (le_of_lt h2), max_eq_left (le_of_lt h1),
            min_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
    have sup_min : ∀ (x : ℝ≥0∞), ⨆ n : ℕ, min x n = x := fun x => by
      rcases eq_or_ne x ⊤ with rfl | hx
      · simp [min_eq_right le_top, ENNReal.iSup_natCast]
      · refine le_antisymm ?_ ?_
        · exact iSup_le fun n => min_le_left x n
        · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx
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
  rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop]
  simp_rw [enorm_eq_nnnorm]
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
    {f : α → ℝ} {g : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
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
          intro hq; rw [hq, ENNReal.toReal_zero] at hpq
          exact absurd hpq.symm.lt_one (by norm_num)
        have hqtop : q ≠ ⊤ := by
          intro hq; rw [hq, ENNReal.toReal_top] at hpq
          exact absurd hpq.symm.lt_one (by norm_num)
        simp only [eLpNorm, hp0, hptop, hq0, hqtop, ite_false, eLpNorm']

/-- Product of Lp and Lq functions is integrable (L1). -/
theorem integrable_mul_of_memLp (p q : ℝ≥0∞)
    (hpq : p.toReal.HolderConjugate q.toReal) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} {g : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun a => f a * g a) μ := by
  rw [← memLp_one_iff_integrable]
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
    (g : α → ℝ) (hg : MemLp g q μ) :
    Lp ℝ p μ →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous ?_ (eLpNorm g q μ).toReal ?_
  · -- Linear map: f ↦ ∫ (↑f) * g ∂μ
    exact {
      toFun := fun f => ∫ a, (f : α → ℝ) a * g a ∂μ
      map_add' := fun f₁ f₂ => by
        have h1 := integrable_mul_of_memLp p q hpq hp hptop (Lp.memLp f₁) hg
        have h2 := integrable_mul_of_memLp p q hpq hp hptop (Lp.memLp f₂) hg
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
    have hint := integrable_mul_of_memLp p q hpq hp hptop (Lp.memLp f) hg
    calc ‖∫ a, (f : α → ℝ) a * g a ∂μ‖
        ≤ ∫ a, ‖(f : α → ℝ) a * g a‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ (eLpNorm (f : α → ℝ) p μ * eLpNorm g q μ).toReal := by
          rw [← integral_norm_eq_lintegral_nnnorm hint.aestronglyMeasurable]
          · apply ENNReal.toReal_mono
            · exact ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne
            · exact lintegral_mul_le_of_memLp p q hpq hp hptop (Lp.memLp f) hg
      _ = (eLpNorm g q μ).toReal * ‖f‖ := by
          rw [ENNReal.toReal_mul, mul_comm]
          -- ‖f‖ in Lp is (eLpNorm (↑f) p μ).toReal by definition
          rfl

/-- The integration CLM computes ∫ fg. -/
theorem integrationCLM_apply (p q : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    [Fact (1 ≤ p)]
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ]
    (g : α → ℝ) (hg : MemLp g q μ) (f : Lp ℝ p μ) :
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
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (g : α → ℝ) (hg : MemLp g q μ)
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
    The Lp partial sums ∑_{i∈F} 1_{f i} (over finite F) converge in Lp norm to 1_{⋃ f i}.

    Proof: Use tendsto_indicatorConstLp_set with the measure of the symmetric difference
    (⋃_{i∈F} f i) ∆ (⋃ f i) = ⋃_{i∉F} f i → 0, which follows from tail measure → 0. -/
private theorem indicator_lp_hasSum [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : ℕ → Set α} (hf_meas : ∀ i, MeasurableSet (f i))
    (hf_disj : Pairwise (Disjoint on f)) :
    HasSum
      (fun i => (indicator_memLp (hf_meas i) (measure_ne_top μ _) p hp hptop).toLp _)
      ((indicator_memLp (MeasurableSet.iUnion hf_meas) (measure_ne_top μ _) p hp hptop).toLp _) := by
  haveI hp1' : Fact (1 ≤ p) := ⟨hp⟩
  -- Step 1: Convert .toLp _ to indicatorConstLp (same function a.e.)
  have hconv : ∀ (E : Set α) (hE : MeasurableSet E),
      (indicator_memLp hE (measure_ne_top μ E) p hp hptop).toLp _ =
      indicatorConstLp p hE (measure_ne_top μ E) (1 : ℝ) := fun E hE =>
    MemLp.toLp_congr (indicator_memLp hE _ p hp hptop)
      (memLp_indicator_const p hE 1 (Or.inr (measure_ne_top μ E)))
      (ae_eq_refl _)
  simp_rw [hconv]
  -- Step 2: Partial sums = indicatorConstLp of partial union
  have hF_sum : ∀ F : Finset ℕ,
      ∑ i ∈ F, indicatorConstLp p (hf_meas i) (measure_ne_top μ _) (1 : ℝ) =
      indicatorConstLp p (F.measurableSet_biUnion hf_meas) (measure_ne_top μ _) (1 : ℝ) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simp [indicatorConstLp_empty]
    | insert ha ih =>
      rename_i a F' ha ih
      rw [Finset.sum_insert ha, ih,
          ← indicatorConstLp_disjoint_union (hf_meas a) (F'.measurableSet_biUnion hf_meas)
              (measure_ne_top μ _) (measure_ne_top μ _)
              (Set.disjoint_iUnion₂_right.mpr (fun i hi => hf_disj (fun h => ha (h ▸ hi))))]
      -- The two indicatorConstLp calls represent the same indicator function a.e.
      apply Lp.ext_iff.mpr
      filter_upwards [indicatorConstLp_coeFn (hs := (hf_meas a).union (F'.measurableSet_biUnion hf_meas))
                        (hμs := by finiteness) (c := (1:ℝ)),
                      indicatorConstLp_coeFn (hs := (insert a F').measurableSet_biUnion hf_meas)
                        (hμs := measure_ne_top μ _) (c := (1:ℝ))] with x hx1 hx2
      rw [hx1, hx2, set_biUnion_insert]
  -- Step 3: Tail sets ⋃_{i≥N} f i are antitone with empty intersection → measure → 0
  let tail : ℕ → Set α := fun N => ⋃ i, if N ≤ i then f i else ∅
  have htail_anti : Antitone tail := fun m n hmn x => by
    simp only [tail, Set.mem_iUnion, Set.mem_ite_empty_right]
    exact fun ⟨i, hi, hx⟩ => ⟨i, hmn.trans hi, hx⟩
  have htail_iInter : ⋂ N, tail N = ∅ := by
    ext x
    simp only [tail, Set.mem_iInter, Set.mem_iUnion, Set.mem_ite_empty_right,
               Set.mem_empty_iff_false, iff_false, not_forall, not_exists]
    push_neg
    intro h
    by_contra habs
    push_neg at habs
    obtain ⟨k₀, hxk₀⟩ : ∃ k, x ∈ f k := by obtain ⟨k, _, hxk⟩ := h 0; exact ⟨k, hxk⟩
    use k₀ + 1
    intro k hk hxk
    exact absurd (Set.mem_inter hxk₀ hxk) ((hf_disj (by omega)).inter_eq ▸ Set.not_mem_empty x)
  have htail_tendsto : Tendsto (fun N => μ (tail N)) atTop (𝓝 0) := by
    have hconv' := tendsto_measure_iInter_atTop (s := tail)
      (hs := fun N => (MeasurableSet.iUnion fun i =>
        (by split_ifs <;> [exact hf_meas i; exact MeasurableSet.empty])).nullMeasurableSet)
      (hm := htail_anti) ⟨0, measure_ne_top μ _⟩
    rw [htail_iInter, measure_empty] at hconv'; exact hconv'
  -- Step 4: Symmetric difference (⋃_{i∈F} f i) ∆ (⋃ f i) ⊆ tail N when F ⊇ range N
  have hΔ_bound : ∀ (N : ℕ) (F : Finset ℕ), Finset.range N ⊆ F →
      (⋃ i ∈ F, f i) ∆ (⋃ i, f i) ⊆ tail N := by
    intro N F hF x hx
    rcases Set.mem_symmDiff.mp hx with ⟨⟨i, _, hxi⟩, habs⟩ | ⟨⟨i, hxi⟩, hnotF⟩
    · exact absurd (Set.mem_iUnion.mpr ⟨i, hxi⟩) habs
    · simp only [Set.mem_biUnion, not_exists, not_and] at hnotF
      have hi_notF : i ∉ F := fun hi => hnotF i hi hxi
      have hi_ge : N ≤ i := Nat.le_of_not_lt (fun h => hi_notF (hF (Finset.mem_range.mpr h)))
      simp only [tail, Set.mem_iUnion, Set.mem_ite_empty_right]
      exact ⟨i, hi_ge, hxi⟩
  -- Step 5: Symmetric difference measure → 0 as F → atTop
  have hΔ_tendsto : Tendsto (fun F : Finset ℕ => μ ((⋃ i ∈ F, f i) ∆ (⋃ i, f i))) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := ENNReal.tendsto_atTop_zero.mp htail_tendsto ε hε
    exact ⟨Finset.range N₀, fun F hF =>
      (measure_mono (hΔ_bound N₀ F hF)).trans (hN₀ N₀ le_rfl)⟩
  -- Step 6: Apply tendsto_indicatorConstLp_set
  rw [HasSum]
  simp_rw [hF_sum]
  exact tendsto_indicatorConstLp_set hptop hΔ_tendsto

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
  simp [signedMeasureOfFunctional]

/-- The signed measure from φ is absolutely continuous w.r.t. μ.
    Follows from `functionalSetFn_null`: if μ(E) = 0 then φ(1_E) = 0. -/
private theorem signedMeasureOfFunctional_ac [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤) (φ : Lp ℝ p μ →L[ℝ] ℝ) :
    (signedMeasureOfFunctional p hp hptop φ).AbsolutelyContinuous
        μ.toENNRealVectorMeasure := by
  intro s hμs
  by_cases hE : MeasurableSet s
  · rw [signedMeasureOfFunctional_indicator p hp hptop φ hE]
    apply functionalSetFn_null p hp hptop φ hE
    rwa [Measure.toENNRealVectorMeasure_apply hE] at hμs
  · exact (signedMeasureOfFunctional p hp hptop φ).not_measurable hE

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
  exact withDensityᵥ_apply hint hE

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
    [hpFact : Fact (1 ≤ p)]
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
    [IsFiniteMeasure μ] [SigmaFinite μ] [_ : Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
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
  have hg_Lq : MemLp g q μ :=
    rn_deriv_memLq_from_trunc p q hp1 hptop hpq g hg_meas ‖φ‖
      (fun n => holder_extremizer_lq_bound p q hp1 hptop hpq φ ν hac hν_eq n)
  -- Step 5: Full representation via integral_representation (Lp.induction)
  exact ⟨g, hg_Lq, integral_representation p q hp1 hptop hpq φ g hg_Lq hagree⟩

/-
## Assessment Summary (Updated 2026-04-21)

### What This File Proves (no sorry)
1. Indicator functions are in Lp for finite-measure sets
2. The functional-induced set function vanishes on null sets
3. RN reconstruction: withDensityᵥ (rnDeriv) = s for AC measures
4. Truncated RN derivative is in Lq for finite measures (Sub-goal 5a)
5. **MCT for truncations**: ∫⁻ ‖g‖₊^q = ⨆_n ∫⁻ ‖gₙ‖₊^q (proved via lintegral_iSup)
6. **rn_deriv_memLq** (modulo `truncated_rn_deriv_lq_bound` sorry — MARKED FALSE)
7. **rn_deriv_memLq_from_trunc**: COMPLETE sorry-free Lq membership from truncation bounds
8. **Integral representation** via Lp.induction (all 3 cases proved)
9. lintegral Hölder, Bochner integrability from Lp×Lq, integrationCLM
10. **signedMeasureOfFunctional**: signed measure construction from φ (modulo indicator_lp_hasSum)
11. **signedMeasureOfFunctional_ac**: absolute continuity (complete, no sorry)
12. **rnDeriv_integral_eq**: ν E = ∫_E g (modulo rnDeriv_integrable_of_finite)
13. **riesz_lp_surjective_from_rn**: PROOF STRUCTURE COMPLETE (modulo 3 focused sorries)

### Focused Sorries (4 total, 3 on critical path)
1. `truncated_rn_deriv_lq_bound` — MARKED FALSE (set function bound insufficient; dead end)
2. `indicator_lp_hasSum` — Lp convergence of indicator partial sums (~60 lines)
   Proof: tail Lp norm = μ(⋃_{i≥N} f i)^{1/p} → 0 (finite measure + disjoint)
3. `rnDeriv_integrable_of_finite` — ν.rnDeriv μ ∈ L1 (~20 lines)
   Proof: Jordan decomp + Measure.integrable_rnDeriv for each finite part
4. `holder_extremizer_lq_bound` — ‖gₙ‖_q ≤ ‖φ‖ uniformly (~50 lines)
   Proof: extremizer h = sign(gₙ)|gₙ|^{q-1}, ‖gₙ‖_q^q ≤ ∫ h·g = φ(h) ≤ ‖φ‖·‖gₙ‖_q^{q/p}

### Key Progress (2026-04-21 Session 3)
- Structured the main proof: riesz_lp_surjective_from_rn now assembles 5 clean steps
- Proved signedMeasureOfFunctional_ac (no sorry: uses functionalSetFn_null directly)
- Proved rnDeriv_integral_eq structure (relies on rnDeriv_integrable_of_finite sorry)
- Proved functional_hasSum_parts (reduces to indicator_lp_hasSum + CLM continuity)
- 5-step proof structure: ν construction → g=dν/dμ → hagree → g∈Lq → integral_representation

### Path to Completion (3 focused sorries, estimated ~130 lines total)
1. `indicator_lp_hasSum` (~60 lines): Show Lp partial sums of 1_{f i} → 1_{⋃ f i} in norm
   - HasSum ↔ tail Lp norm → 0
   - Tail norm = μ(⋃_{i≥N} f i)^{1/p}; finite measure + disjoint → μ-tail → 0
2. `rnDeriv_integrable_of_finite` (~20 lines):
   - simp [SignedMeasure.rnDeriv]; apply Integrable.sub
   - Each Jordan part: Measure.integrable_rnDeriv needs [IsFiniteMeasure ν] [SigmaFinite μ]
3. `holder_extremizer_lq_bound` (~50 lines):
   - Build h_n = sign(gₙ)|gₙ|^{q-1} ∈ Lp (bounded, finite measure)
   - Extend φ(1_E) = ∫_E g to bounded functions via simple-fn approximation + DCT
   - ‖gₙ‖_q^q = ∫ h_n·gₙ ≤ ∫ h_n·g = φ(h_n) ≤ ‖φ‖·‖h_n‖_p = ‖φ‖·‖gₙ‖_q^{q/p}
   - Algebra: ‖gₙ‖_q ≤ ‖φ‖ (using q - q/p = 1 from 1/p + 1/q = 1)
-/

end RieszLpSurjectivity

end
