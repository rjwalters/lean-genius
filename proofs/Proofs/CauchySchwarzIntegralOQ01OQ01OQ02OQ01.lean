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

/-- **WARNING: This theorem is FALSE as stated.**

    COUNTEREXAMPLE: On [0,1] with Lebesgue measure, p = 2, q = 2:
    Let g = x^{-1/2}. Then s(E) = ∫_E x^{-1/2} dx satisfies
      |s(E)| ≤ 2·μ(E)^{1/2} for all E  (layer cake optimality: max is at E = [0,m])
    But ‖gₙ‖_2 = (2·ln n + 1)^{1/2} → ∞, so ‖gₙ‖_q ≤ M = 2 fails for large n.

    ROOT CAUSE: The set function bound |s(E)| ≤ M·μ(E)^{1/p} alone does not bound ‖g‖_q.
    It only bounds ‖1_E‖_q norms. The correct hypothesis is that s arises from a bounded
    functional φ ∈ (Lp)* with ‖φ‖ ≤ M (which does NOT follow from the set function bound).

    The correct version is `lq_norm_bound_from_functional` below, which takes φ directly.
    This sorry therefore CANNOT be filled from the current hypotheses. -/
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
  -- This sorry CANNOT be filled. See warning above.
  -- The correct path: use lq_norm_bound_from_functional with φ as hypothesis.
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
    -- Sub-lemma 1: |max(min(r,n), -n)| = min(|r|, n) for r : ℝ, n : ℕ
    have abs_clamp : ∀ (r : ℝ) (n : ℕ), |max (min r n) (-(n : ℝ))| = min |r| n := by
      intro r n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rcases le_or_lt r (-(n : ℝ)) with h1 | h1
      · -- r ≤ -n: gn = -n, |gn| = n = min |r| n (since |r| = -r ≥ n)
        have h1' : r ≤ n := h1.trans (by linarith)
        rw [min_eq_left h1', max_eq_right h1, abs_neg, abs_of_nonneg hn,
            abs_of_nonpos (h1.trans (by linarith)), min_eq_right (by linarith)]
      rcases le_or_lt (n : ℝ) r with h2 | h2
      · -- r ≥ n ≥ 0: gn = n, |gn| = n = min |r| n (since |r| = r ≥ n)
        rw [min_eq_right h2, max_eq_left (by linarith), abs_of_nonneg hn,
            abs_of_nonneg (hn.trans h2), min_eq_right h2]
      · -- -n < r < n: gn = r, |gn| = |r| = min |r| n (since |r| < n)
        rw [min_eq_left (le_of_lt h2), max_eq_left (le_of_lt h1),
            min_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
    -- Sub-lemma 2: ⨆ n : ℕ, min x n = x for x : ℝ≥0∞
    have sup_min : ∀ (x : ℝ≥0∞), ⨆ n : ℕ, min x n = x := fun x => by
      rcases eq_or_ne x ⊤ with rfl | hx
      · simp [min_eq_right le_top, ENNReal.iSup_natCast]
      · apply le_antisymm (iSup_le fun n => min_le_left x n)
        obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx
        calc x = min x N := (min_eq_left (le_of_lt hN)).symm
          _ ≤ ⨆ n : ℕ, min x n := le_iSup _ N
    -- Sub-lemma 3: (‖gn n a‖₊ : ℝ≥0∞) = min (‖g a‖₊ : ℝ≥0∞) n
    have norm_gn_eq : ∀ (a : α) (n : ℕ), (‖gn n a‖₊ : ℝ≥0∞) = min (‖g a‖₊ : ℝ≥0∞) n := by
      intro a n
      rw [← ENNReal.coe_min]
      congr 1
      apply NNReal.coe_injective
      push_cast [Real.norm_eq_abs]
      simp only [gn]
      exact abs_clamp (g a) n
    -- Sub-lemma 4: (‖g a‖₊)^q = ⨆ n, (min (‖g a‖₊) n)^q by orderIsoRpow
    have ptwise_eq : ∀ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal =
        ⨆ n : ℕ, (min (‖g a‖₊ : ℝ≥0∞) n) ^ q.toReal := by
      intro a
      have h := (ENNReal.orderIsoRpow q.toReal hq_pos).map_iSup
          (fun n : ℕ => min (‖g a‖₊ : ℝ≥0∞) n)
      simp only [ENNReal.orderIsoRpow_apply] at h
      rw [sup_min (‖g a‖₊)] at h
      exact h
    -- Main: rewrite LHS as ∫⁻ iSup, apply lintegral_iSup, then match RHS via norm_gn_eq
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
## Main Theorem: Riesz Representation for Lp (Surjectivity)

Combining all steps: given φ ∈ (Lp)*, construct g ∈ Lq with φ(f) = ∫ fg dμ.

### Remaining Infrastructure (4 targeted sorries)

1. `integrationCLM` + `integrationCLM_apply` — CLM f ↦ ∫fg via Hölder (~40 lines)
   Needs: LinearMap.mkContinuous, Hölder at integral level
2. `truncated_rn_deriv_lq_bound` — Uniform Lq bound for truncations (~50 lines)
   Needs: Hölder extremizer construction applied to truncations
3. `rn_deriv_memLq` — Full Lq membership from truncation bounds (~30 lines)
   Needs: Fatou's lemma applied to uniformly bounded truncation sequence
4. `riesz_lp_surjective_from_rn` — Main theorem assembly (~50 lines)
   Needs: Signed measure construction from functional (countable additivity)
-/

/-
## Corrected Architecture: Lq Bound Requires Functional, Not Set Function Bound

IMPORTANT CORRECTION (2026-04-14):
The theorem `truncated_rn_deriv_lq_bound` above has WRONG hypotheses and is unprovable.
The counterexample g = x^{-1/q} on [0,1] (p = q = 2) shows that |s(E)| ≤ M·μ(E)^{1/p}
does NOT bound the Lq norm of the RN derivative.

### Correct Proof Architecture (Rudin RCA Theorem 6.16)

Given φ ∈ (Lp)*, construct g ∈ Lq via:
1. ν(E) = φ(1_E) defines a signed measure (σ-additivity from Lp convergence)
2. ν ≪ μ, so g = dν/dμ exists via RN
3. Hölder extremizer: for each n, set gₙ = clamp(g,-n,n) and hₙ = sign(gₙ)|gₙ|^{q-1}
   - hₙ ∈ Lp (bounded by n^{q-1})
   - For bounded measurable h: φ(h) = ∫ h·g dμ  [proved via simple fn approx + RN]
   - ∫ hₙ g dμ ≥ ∫ hₙ gₙ dμ = ‖gₙ‖_q^q  [sign property: hₙ(g - gₙ) ≥ 0]
   - |φ(hₙ)| ≤ ‖φ‖·‖hₙ‖_p = ‖φ‖·‖gₙ‖_q^{q/p}
   - Chain: ‖gₙ‖_q^q ≤ ‖φ‖·‖gₙ‖_q^{q/p} ⟹ ‖gₙ‖_q ≤ ‖φ‖
4. MCT: ‖g‖_q ≤ ‖φ‖ (from uniform truncation bound + lintegral_iSup)
5. φ(f) = ∫ fg for all f ∈ Lp (by integral_representation)

The key difference: step 3 uses φ DIRECTLY (not just the set function bound).

### Pointwise Sign Property (key lemma for step 3)
For hₙ = sign(gₙ)|gₙ|^{q-1} and gₙ = clamp(g,-n,n):
- g(a) ≥ n: gₙ = n, hₙ = n^{q-1} ≥ 0, g - gₙ = g - n ≥ 0 → product ≥ 0
- g(a) ≤ -n: gₙ = -n, hₙ = -n^{q-1} ≤ 0, g - gₙ = g + n ≤ 0 → product ≥ 0
- |g(a)| < n: gₙ = g, g - gₙ = 0 → product = 0
So hₙ(a)·(g(a) - gₙ(a)) ≥ 0 for all a.

### Remaining Sorries (2)
1. `rn_signed_measure_from_functional`: σ-additive signed measure ν(E) = φ(1_E)
   Hard part: showing Lp-convergence of indicator sums gives σ-additivity.
2. `functional_identity_bounded`: φ applied to bounded h ∈ Lp equals ∫ h·g dμ
   Via: simple fn approx of h in Lp, convergence of both sides.
-/

/-- The pointwise sign property: the Hölder test function hₙ = sign(gₙ)|gₙ|^{q-1}
    satisfies hₙ(a) · (g(a) - gₙ(a)) ≥ 0 for all a.

    Proof sketch (3 cases):
    - g(a) ≥ n: gₙ = n, hₙ = n^{q-1} ≥ 0, g - gₙ = g(a)-n ≥ 0. Product ≥ 0.
    - g(a) ≤ -n: gₙ = -n, hₙ = -n^{q-1} ≤ 0, g - gₙ = g(a)+n ≤ 0. Product ≥ 0.
    - |g(a)| < n: gₙ = g(a), g - gₙ = 0. Product = 0.
    This ensures ∫ hₙ · g ≥ ∫ hₙ · gₙ = ‖gₙ‖_q^q. -/
lemma holder_test_sign_property (g : α → ℝ) (n : ℕ) (q : ℝ≥0∞) (hq : 0 < q.toReal) :
    ∀ a, (Real.sign (max (min (g a) n) (-(n : ℝ))) *
          |max (min (g a) n) (-(n : ℝ))| ^ (q.toReal - 1)) *
         (g a - max (min (g a) n) (-(n : ℝ))) ≥ 0 := by
  intro a
  set gn := max (min (g a) (n : ℝ)) (-(n : ℝ))
  set hn := Real.sign gn * |gn| ^ (q.toReal - 1)
  -- Case split on whether g(a) ≥ n, g(a) ≤ -n, or |g(a)| < n
  rcases le_or_lt (n : ℝ) (g a) with h1 | h1
  · -- g(a) ≥ n: gn = n ≥ 0, hn ≥ 0, g - gn ≥ 0
    have hgn : gn = n := by
      simp only [gn, min_eq_right h1, max_eq_left (le_of_eq rfl)]
    have hdiff : g a - gn ≥ 0 := by simp [hgn]; linarith
    have hhn : hn ≥ 0 := by
      simp only [hn, hgn]
      apply mul_nonneg
      · exact Real.sign_nonneg.mpr (Nat.cast_nonneg n)
      · positivity
    exact mul_nonneg hhn hdiff
  · rcases le_or_lt (g a) (-(n : ℝ)) with h2 | h2
    · -- g(a) ≤ -n: gn = -n ≤ 0, hn ≤ 0, g - gn ≤ 0
      have hgn : gn = -(n : ℝ) := by
        have : min (g a) (n : ℝ) = g a := min_eq_left (h2.trans (by linarith [Nat.cast_nonneg n]))
        simp only [gn, this, max_eq_right h2]
      have hdiff : g a - gn ≤ 0 := by simp [hgn]; linarith
      have hhn : hn ≤ 0 := by
        simp only [hn, hgn]
        rcases Nat.eq_zero_or_pos n with rfl | hn_pos
        · simp
        · have hgn_neg : -(n : ℝ) < 0 := neg_neg_of_neg (Nat.cast_pos.mpr hn_pos)
          have := Real.sign_neg hgn_neg
          simp [this]; exact neg_nonpos.mpr (by positivity)
      -- hn ≤ 0 and hdiff ≤ 0, so product ≥ 0
      have : hn * (g a - gn) = ((-hn) * (-(g a - gn))) := by ring
      rw [this]
      exact mul_nonneg (neg_nonneg.mpr hhn) (neg_nonneg.mpr hdiff)
    · -- |g(a)| < n: gn = g(a), product = 0
      have hgn : gn = g a := by
        simp only [gn, min_eq_left (le_of_lt h1), max_eq_left (le_of_lt h2)]
      simp [hn, hgn, sub_self]

/-- MCT path to Lq membership: if truncations gₙ = clamp(g,-n,n) have uniformly bounded
    Lq norms (≤ M), then g ∈ Lq.

    This extracts the Monotone Convergence Theorem argument from `rn_deriv_memLq`,
    now taking the truncation bounds directly (from the Hölder extremizer) rather than
    deriving them from the false set-function bound `truncated_rn_deriv_lq_bound`. -/
lemma memLq_of_uniform_truncation_bound
    (g : α → ℝ) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M)
    (q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ⊤)
    (hgn_bound : ∀ n : ℕ, eLpNorm (fun a => max (min (g a) (n : ℝ)) (-(n : ℝ))) q μ ≤
        ENNReal.ofReal M) :
    Memℒp g q μ := by
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  let gn : ℕ → α → ℝ := fun n a => max (min (g a) ↑n) (-↑n)
  -- Convert eLpNorm bound to lintegral bound
  have hgn_lint : ∀ n, ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ ≤
      (ENNReal.ofReal M) ^ q.toReal := by
    intro n
    have h := hgn_bound n
    rw [eLpNorm_eq_lintegral_rpow_nnnorm hq0 hqtop] at h
    calc ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ
        = ((∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ) ^ (1 / q.toReal)) ^ q.toReal := by
            rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hq_pos),
                ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal M) ^ q.toReal := ENNReal.rpow_le_rpow h (le_of_lt hq_pos)
  -- MCT: ∫⁻ ‖g‖₊^q = ⨆_n ∫⁻ ‖gn n‖₊^q (monotone increasing truncations converge to g)
  have hMCT : ∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ =
      ⨆ n, ∫⁻ a, (‖gn n a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ := by
    -- Sub-lemma 1: |max(min(r,n), -n)| = min(|r|, n)
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
    -- Sub-lemma 2: ⨆ n : ℕ, min x n = x for x : ℝ≥0∞
    have sup_min : ∀ (x : ℝ≥0∞), ⨆ n : ℕ, min x n = x := fun x => by
      rcases eq_or_ne x ⊤ with rfl | hx
      · simp [min_eq_right le_top, ENNReal.iSup_natCast]
      · apply le_antisymm (iSup_le fun n => min_le_left x n)
        obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx
        calc x = min x N := (min_eq_left (le_of_lt hN)).symm
          _ ≤ ⨆ n : ℕ, min x n := le_iSup _ N
    -- Sub-lemma 3: ‖gn n a‖₊ = min ‖g a‖₊ n (as ℝ≥0∞)
    have norm_gn_eq : ∀ (a : α) (n : ℕ), (‖gn n a‖₊ : ℝ≥0∞) = min (‖g a‖₊ : ℝ≥0∞) n := by
      intro a n
      rw [← ENNReal.coe_min]
      congr 1
      apply NNReal.coe_injective
      push_cast [Real.norm_eq_abs]
      simp only [gn]
      exact abs_clamp (g a) n
    -- Sub-lemma 4: ‖g a‖₊^q = ⨆_n (min ‖g a‖₊ n)^q (orderIsoRpow)
    have ptwise_eq : ∀ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal =
        ⨆ n : ℕ, (min (‖g a‖₊ : ℝ≥0∞) n) ^ q.toReal := by
      intro a
      have h := (ENNReal.orderIsoRpow q.toReal hq_pos).map_iSup
          (fun n : ℕ => min (‖g a‖₊ : ℝ≥0∞) n)
      simp only [ENNReal.orderIsoRpow_apply] at h
      rw [sup_min (‖g a‖₊)] at h
      exact h
    rw [show (fun a => (‖g a‖₊ : ℝ≥0∞) ^ q.toReal) =
        (fun a => ⨆ n : ℕ, (min (‖g a‖₊ : ℝ≥0∞) n) ^ q.toReal) from funext ptwise_eq,
        lintegral_iSup
          (fun n => (hg.nnnorm.coe_nnreal_ennreal.min measurable_const).pow_const q.toReal)
          (fun ⦃m n⦄ hmn a => ENNReal.rpow_le_rpow
            (min_le_min_left _ (Nat.cast_le.mpr hmn)) (le_of_lt hq_pos))]
    simp_rw [← norm_gn_eq]
  -- Conclude: eLpNorm g q μ ≤ ENNReal.ofReal M < ⊤
  refine ⟨hg.aestronglyMeasurable, lt_of_le_of_lt ?_ ENNReal.ofReal_lt_top⟩
  rw [eLpNorm_eq_lintegral_rpow_nnnorm hq0 hqtop]
  calc (∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ) ^ (1 / q.toReal)
      ≤ ((ENNReal.ofReal M) ^ q.toReal) ^ (1 / q.toReal) := by
          apply ENNReal.rpow_le_rpow _ (by positivity)
          rw [hMCT]; exact iSup_le hgn_lint
    _ = ENNReal.ofReal M := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hq_pos.ne',
              ENNReal.rpow_one]

/-- **Riesz Representation for Lp** (surjectivity direction).
    Every bounded linear functional on Lp is represented by integration
    against an Lq function, where 1/p + 1/q = 1, 1 < p < ∞.

    Proof architecture: Construct ν(E) = φ(1_E) as signed measure, apply RN to get g,
    use Hölder extremizer with test function hₙ = sign(gₙ)|gₙ|^{q-1} to bound ‖gₙ‖_q ≤ ‖φ‖,
    then MCT gives g ∈ Lq. Two sorry sub-goals remain (see comments in proof).

    This theorem, once the sorry sub-goals are resolved, eliminates the
    `riesz_lp_surjective` axiom from the parent file. -/
theorem riesz_lp_surjective_from_rn (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, Memℒp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  intro φ
  haveI hp1' : Fact (1 ≤ p) := ⟨le_of_lt hp1⟩
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_of_lt hp1))
  have hq0 : q ≠ 0 := by
    intro hq; rw [hq, ENNReal.zero_toReal] at hpq
    exact absurd hpq.symm.lt_one (by norm_num)
  have hqtop : q ≠ ⊤ := by
    intro hq; rw [hq, ENNReal.top_toReal] at hpq
    exact absurd hpq.symm.lt_one (by norm_num)
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  -- Step 1: Construct signed measure ν from φ.
  -- ν(E) := φ(indicator 1_E in Lp). σ-additivity follows from Lp-convergence of
  -- partial sums of indicator functions (DCT in Lp).
  -- ν ≪ μ: if μ(E) = 0 then 1_E = 0 in Lp, so φ(1_E) = 0.
  obtain ⟨ν, hac, hagree, hν_int⟩ :
      ∃ ν : SignedMeasure α,
        ν.AbsolutelyContinuous μ.toENNRealVectorMeasure ∧
        (∀ (E : Set α) (hE : MeasurableSet E) (hfin : μ E ≠ ⊤),
          ν E = φ ((indicator_memLp hE hfin p (le_of_lt hp1) hptop).toLp _)) ∧
        (∀ (h : α → ℝ) (hh : Memℒp h p μ) (C : ℝ) (_ : ∀ a, |h a| ≤ C),
          φ (hh.toLp h) = ∫ a, h a * ν.rnDeriv μ a ∂μ) := by
    -- SORRY 1: σ-additive signed measure construction + functional identity.
    -- Hard part: countable additivity of E ↦ φ(1_E).
    -- Key idea: 1_{∪ Eₙ} - Σ_{k≤N} 1_{Eₖ} → 0 in Lp as N → ∞ (by DCT in Lp),
    -- so φ(1_{∪ Eₙ}) = lim_N Σ_{k≤N} φ(1_{Eₖ}) by continuity.
    -- The identity φ(h) = ∫ h·g extends from simple functions by Lp density + DCT
    -- (using g ∈ L^1 on finite measure space + uniform bound on h).
    sorry
  set g := ν.rnDeriv μ with hg_def
  have hg_meas : Measurable g := ν.measurable_rnDeriv μ
  -- Step 2: Uniform Lq bound on truncations via Hölder extremizer.
  -- For each n, the test function hₙ = sign(gₙ)|gₙ|^{q-1} ∈ Lp (bounded)
  -- satisfies: ‖gₙ‖_q^q ≤ ∫ hₙ g ≤ |φ(hₙ)| ≤ ‖φ‖·‖hₙ‖_p = ‖φ‖·‖gₙ‖_q^{q/p}
  have hgn_bound : ∀ n : ℕ, eLpNorm (fun a => max (min (g a) n) (-(n : ℝ))) q μ ≤
      ENNReal.ofReal ‖φ‖ := by
    intro n
    -- SORRY 2: Hölder extremizer algebra.
    -- Requires: (a) hₙ ∈ Lp with ‖hₙ‖_p = ‖gₙ‖_q^{q/p} [norm computation]
    --           (b) φ(hₙ) = ∫ hₙ g [from hν_int applied to bounded hₙ]
    --           (c) ∫ hₙ g ≥ ‖gₙ‖_q^q [from holder_test_sign_property]
    --           (d) chain: ‖gₙ‖_q ≤ ‖φ‖ [algebra from b,c + op norm bound]
    -- The sign property (c) is proved above as holder_test_sign_property.
    sorry
  -- Step 3: MCT gives g ∈ Lq from uniform truncation bound.
  -- Use memLq_of_uniform_truncation_bound with hgn_bound (from Hölder extremizer above).
  -- No sorry needed here — the MCT argument is fully proved in the helper lemma.
  have hg_memLq : Memℒp g q μ := memLq_of_uniform_truncation_bound g hg_meas ‖φ‖
      (ContinuousLinearMap.opNorm_nonneg φ) q hq0 hqtop hgn_bound
  -- Step 4: φ(f) = ∫ fg for all f ∈ Lp (by integral_representation).
  -- hagree gives: φ(1_E) = ν(E) = ∫_E g dμ  (from RN: withDensityᵥ g = ν)
  refine ⟨g, hg_memLq, integral_representation p q hp1 hptop hpq φ g hg_memLq
    (fun E hE hfin => ?_)⟩
  -- Goal: φ(1_E in Lp) = ∫_E g dμ
  -- After rewrite: ν(E) = ∫_E g dμ  (from RN: withDensityᵥ g = ν)
  rw [hagree E hE hfin]
  have hrn : μ.withDensityᵥ (ν.rnDeriv μ) = ν :=
    SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq.mp hac
  -- ν E = (withDensityᵥ g) E = ∫_E g dμ
  conv_lhs => rw [← hrn]
  exact (Measure.withDensityᵥ_apply hg_meas.aestronglyMeasurable hE).symm

/-
## Assessment Summary (Updated 2026-04-14, Session 2)

### What This File Proves (from Mathlib, no sorry)
1. Indicator functions are in Lp for finite-measure sets (Step 1)
2. The functional-induced set function vanishes on null sets (Step 2)
3. RN reconstruction: withDensityᵥ (rnDeriv) = s for AC measures (Step 3)
4. Truncated RN derivative is in Lq for finite measures (Sub-goal 5a)
5. **Integral representation via Lp.induction** (all 3 cases proved)
6. **Pointwise sign property**: holder_test_sign_property — hₙ(g-gₙ) ≥ 0
7. **Corrected architecture** for riesz_lp_surjective_from_rn using φ directly
8. **MCT argument**: memLq_of_uniform_truncation_bound — NEW, fully proved

### Mathematical Error Discovered
`truncated_rn_deriv_lq_bound` is FALSE. The set function bound |s(E)| ≤ M·μ(E)^{1/p}
is insufficient to bound ‖gₙ‖_q — the correct hypothesis requires φ ∈ (Lp)*.

### Architecture Fix (Session 2)
Replaced broken `rn_deriv_memLq` call (which used the false truncated_rn_deriv_lq_bound)
with `memLq_of_uniform_truncation_bound`, which takes the Hölder extremizer truncation
bounds directly. Sorry 3 (set function bound) is now eliminated from the proof.

### What Remains (2 sorries, reduced from 4)
1. **Sorry 1** (σ-additive signed measure): inside riesz_lp_surjective_from_rn.
   Construct ν(E) = φ(1_E) as σ-additive signed measure.
   Hard part: 1_{∪ Eₙ} → 1_∪Eₙ in Lp → φ(1_∪Eₙ) = Σ φ(1_{Eₙ}).
   Also: φ(h) = ∫ h·g for bounded h via simple fn approx + DCT.
   Key Mathlib tools: Lp.simpleFunc.dense, tendsto_setToFun_of_L1.

2. **Sorry 2** (Hölder extremizer): inside riesz_lp_surjective_from_rn.
   Show ‖gₙ‖_q ≤ ‖φ‖ using test function hₙ = sign(gₙ)|gₙ|^{q-1}.
   Steps: (a) hₙ ∈ Lp with ‖hₙ‖_p = ‖gₙ‖_q^{q/p} [Hölder conjugate norm]
          (b) φ(hₙ) = ∫ hₙ·g [from hν_int with bounded hₙ]
          (c) ∫ hₙ·g ≥ ‖gₙ‖_q^q [sign property, proved as holder_test_sign_property]
          (d) chain: ‖gₙ‖_q ≤ ‖φ‖ [algebra with q/p + 1/p = 1]
   The sign property (c) is PROVED. Steps (a)(b)(d) remain.

### Note on truncated_rn_deriv_lq_bound
This theorem (line 208) has a sorry and is mathematically FALSE. It is dead code —
no longer called by the proof. It is kept for historical documentation only.

### Path to Completion
Estimated: 100-150 additional lines (reduced from 150-200).
Sorry 1 is harder (needs DCT in Lp machinery).
Sorry 2 is more mechanical (Hölder conjugate algebra + norm computation).
-/

end RieszLpSurjectivity

end
