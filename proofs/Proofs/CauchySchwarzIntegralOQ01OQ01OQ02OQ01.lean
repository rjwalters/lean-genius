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
    MemLp (E.indicator (fun _ => (1 : ℝ))) p μ :=
  memLp_indicator_const p hE 1 (Or.inr hfin)

/-
## Step 2: Functional Induces Absolute Continuity

Key insight: if φ is a bounded linear functional on Lp and μ(E) = 0,
then 1_E = 0 a.e., so ‖1_E‖_p = 0, so |φ(1_E)| ≤ ‖φ‖ · 0 = 0.

This means the set function E ↦ φ(1_E) is absolutely continuous
with respect to μ.
-/

/-- Indicator of a null set has zero eLpNorm. -/
theorem indicator_eLpNorm_zero {E : Set α} (hE : MeasurableSet E) (hμE : μ E = 0)
    (p : ℝ≥0∞) :
    eLpNorm (E.indicator (fun _ => (1 : ℝ))) p μ = 0 := by
  apply eLpNorm_eq_zero_of_ae_zero
  filter_upwards [measure_zero_iff_ae_nmem.mp hμE] with x hx
  simp [indicator_apply, hx]

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
def functionalSetFn (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)] (hptop : p ≠ ⊤)
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (E : Set α) (hE : MeasurableSet E)
    (hfin : μ E ≠ ⊤) : ℝ :=
  φ ((indicator_memLp hE hfin p hp hptop).toLp _)

/-- The functional-induced set function vanishes on null sets:
    if μ(E) = 0 then φ(1_E) = 0. This is the AC condition. -/
theorem functionalSetFn_null (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)] (hptop : p ≠ ⊤)
    (φ : Lp ℝ p μ →L[ℝ] ℝ) {E : Set α} (hE : MeasurableSet E)
    (hμE : μ E = 0) :
    functionalSetFn p hp hptop φ E hE (by simp [hμE]) = 0 := by
  sorry

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
    MemLp (fun a => max (min (g a) (n : ℝ)) (-(n : ℝ))) q μ := by
  sorry

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
  sorry

/-- Variant of `rn_deriv_memLq` accepting uniform truncation bounds directly.
    This bypasses the incorrect `truncated_rn_deriv_lq_bound` pathway.
    Used in `riesz_lp_surjective_from_rn` with the Hölder extremizer bound. -/
theorem rn_deriv_memLq_from_trunc (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    (g : α → ℝ) (hg_meas : Measurable g) (M : ℝ)
    (hgn_snorm : ∀ n : ℕ,
        eLpNorm (fun a => max (min (g a) (n : ℝ)) (-(n : ℝ))) q μ ≤ ENNReal.ofReal M) :
    MemLp g q μ := by
  sorry

/-- **Bridge lemma**: Product of Lp and Lq functions has finite L1 lintegral.
    This is the lintegral-level Hölder inequality applied to norms. -/
theorem lintegral_mul_le_of_memLp (p q : ℝ≥0∞)
    (hpq : p.toReal.HolderConjugate q.toReal) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} {g : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ∫⁻ a, ‖f a * g a‖₊ ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hq0 : q ≠ 0 := by
    intro hq; rw [hq, ENNReal.toReal_zero] at hpq; linarith [hpq.symm.pos]
  have hqtop : q ≠ ⊤ := by
    intro hq; rw [hq, ENNReal.toReal_top] at hpq; linarith [hpq.symm.pos]
  -- nnnorm is multiplicative: ‖fg‖₊ = ‖f‖₊ * ‖g‖₊
  have hmul : ∀ a, (‖f a * g a‖₊ : ℝ≥0∞) = (‖f a‖₊ : ℝ≥0∞) * ‖g a‖₊ := fun a => by
    simp only [← ENNReal.coe_mul, nnnorm_mul]
  simp_rw [hmul]
  -- Rewrite eLpNorm into lintegral form (uses enorm = nnnorm-coe definitionally)
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop, eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop]
  -- Apply Hölder: ‖·‖ₑ = (‖·‖₊ : ℝ≥0∞) definitionally, so exact closes
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    hf.aestronglyMeasurable.enorm hg.aestronglyMeasurable.enorm

/-- Product of Lp and Lq functions is integrable (L1). -/
theorem integrable_mul_of_memLp (p q : ℝ≥0∞)
    (hpq : p.toReal.HolderConjugate q.toReal) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} {g : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun a => f a * g a) μ := by
  sorry

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
  sorry

/-- The integration CLM computes ∫ fg. -/
theorem integrationCLM_apply (p q : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    [Fact (1 ≤ p)]
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ]
    (g : α → ℝ) (hg : MemLp g q μ) (f : Lp ℝ p μ) :
    integrationCLM p q hp hptop hpq g hg f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  sorry

/-- The integral representation extends from indicator functions to all of Lp.

    Proof uses Mathlib's `Lp.induction` with:
    - Indicator case: from `hagree` + linearity of φ
    - Addition case: linearity of φ and integral (PROVED)
    - Closedness: ker(φ - integrationCLM) is closed (PROVED, modulo integrationCLM)

    Remaining sorry: `integrationCLM` construction (~40 lines of Hölder). -/
theorem integral_representation (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [IsFiniteMeasure μ] [SigmaFinite μ] [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (g : α → ℝ) (hg : MemLp g q μ)
    (hagree : ∀ (E : Set α) (hE : MeasurableSet E) (hfin : μ E ≠ ⊤),
      φ ((indicator_memLp hE hfin p (le_of_lt hp1) hptop).toLp _) =
      ∫ a in E, g a ∂μ) :
    ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  sorry

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
    (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)] (hptop : p ≠ ⊤)
    {f : ℕ → Set α} (hf_meas : ∀ i, MeasurableSet (f i))
    (hf_disj : Pairwise fun i j => Disjoint (f i) (f j)) :
    HasSum
      (fun i => (indicator_memLp (hf_meas i) (measure_ne_top μ _) p hp hptop).toLp _)
      ((indicator_memLp (MeasurableSet.iUnion hf_meas) (measure_ne_top μ _) p hp hptop).toLp _) := by
  sorry

/-- **σ-additivity** of the set function E ↦ φ(1_E).
    Follows from `indicator_lp_hasSum` by applying φ (a CLM, hence continuous). -/
private theorem functional_hasSum_parts [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)] (hptop : p ≠ ⊤)
    (φ : Lp ℝ p μ →L[ℝ] ℝ)
    {f : ℕ → Set α} (hf_meas : ∀ i, MeasurableSet (f i))
    (hf_disj : Pairwise fun i j => Disjoint (f i) (f j)) :
    HasSum (fun i => functionalSetFn p hp hptop φ (f i) (hf_meas i) (measure_ne_top μ _))
      (functionalSetFn p hp hptop φ (⋃ i, f i) (MeasurableSet.iUnion hf_meas)
          (measure_ne_top μ _)) := by
  sorry

/-- Construct a **signed measure from a bounded Lp functional** in a finite measure space.
    ν(E) = φ(1_E) for measurable E, extended by 0 for non-measurable sets.
    σ-additivity follows from `functional_hasSum_parts`. -/
noncomputable def signedMeasureOfFunctional [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)] (hptop : p ≠ ⊤)
    (φ : Lp ℝ p μ →L[ℝ] ℝ) : SignedMeasure α :=
  sorry

/-- The signed measure from φ agrees with φ on indicator functions. -/
private theorem signedMeasureOfFunctional_indicator [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (φ : Lp ℝ p μ →L[ℝ] ℝ)
    {E : Set α} (hE : MeasurableSet E) :
    signedMeasureOfFunctional p hp hptop φ E =
      φ ((indicator_memLp hE (measure_ne_top μ E) p hp hptop).toLp _) := by
  sorry

/-- The signed measure from φ is absolutely continuous w.r.t. μ.
    Follows from `functionalSetFn_null`: if μ(E) = 0 then φ(1_E) = 0. -/
private theorem signedMeasureOfFunctional_ac [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (φ : Lp ℝ p μ →L[ℝ] ℝ) :
    (signedMeasureOfFunctional p hp hptop φ).AbsolutelyContinuous
        μ.toENNRealVectorMeasure := by
  sorry

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
  sorry

/-- **Hölder extremizer bound**: for gₙ = clamp(g, -n, n) where g = ν.rnDeriv μ,
    eLpNorm gₙ q μ ≤ ENNReal.ofReal ‖φ‖.

    The extremizer h_n = sign(gₙ)|gₙ|^{q-1} satisfies ‖h_n‖_p = ‖gₙ‖_q^{q/p}, and:
      ‖gₙ‖_q^q = ∫ h_n gₙ ≤ ∫ h_n g = φ(h_n as Lp) ≤ ‖φ‖·‖h_n‖_p = ‖φ‖·‖gₙ‖_q^{q/p}
    Dividing: ‖gₙ‖_q^{q-q/p} = ‖gₙ‖_q ≤ ‖φ‖ (using (q-q/p) = 1 when 1/p + 1/q = 1).

    The identity ∫ h_n g = φ(h_n) extends from indicator agreement via:
    simple-function approximation + φ continuity + DCT (g ∈ L1 from rnDeriv_integrable). -/
private theorem holder_extremizer_lq_bound [IsFiniteMeasure μ] [SigmaFinite μ]
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (ν : SignedMeasure α)
    (hac : ν.AbsolutelyContinuous μ.toENNRealVectorMeasure)
    (hν_eq : ∀ (E : Set α) (hE : MeasurableSet E),
        ν E = φ ((indicator_memLp hE (measure_ne_top μ E) p (le_of_lt hp1) hptop).toLp _))
    (n : ℕ) :
    eLpNorm (fun a => max (min (ν.rnDeriv μ a) (n : ℝ)) (-(n : ℝ))) q μ ≤
      ENNReal.ofReal ‖φ‖ := by
  sorry
/-DEAD CODE START
  haveI hp1' : Fact (1 ≤ p) := ⟨le_of_lt hp1⟩
  -- Setup: g = ν.rnDeriv μ, gₙ = clamp(g, -n, n)
  set g := ν.rnDeriv μ
  set g_n := fun a => max (min (g a) (n : ℝ)) (-(n : ℝ))
  have hg_int : Integrable g μ := rnDeriv_integrable_of_finite ν hac
  have hg_meas : Measurable g := ν.measurable_rnDeriv μ
  have hq_pos : 0 < q.toReal := hpq.symm.pos
  have hqne_top : q ≠ ⊤ := by
    intro hq; rw [hq, ENNReal.toReal_top] at hpq; linarith [hpq.symm.one_lt_of_lt hp1]
  -- gₙ is bounded: |gₙ(a)| ≤ n for all a
  have hgn_bound : ∀ a, |g_n a| ≤ (n : ℝ) := fun a => by
    simp only [g_n, abs_le]
    constructor
    · linarith [le_max_right (min (g a) (n : ℝ)) (-(n : ℝ))]
    · exact max_le_iff.mpr ⟨min_le_right _ _, neg_le_self (Nat.cast_nonneg n)⟩
  -- gₙ is integrable (bounded × finite measure)
  have hgn_int : Integrable g_n μ := by
    rw [← memLp_one_iff_integrable]
    exact MemLp.of_bound (n : ℝ)
      (((hg_meas.min measurable_const).max measurable_const).aestronglyMeasurable)
      (ae_of_all μ fun a => by simpa [Real.norm_eq_abs] using hgn_bound a)
  -- Extremizer: hₙ = sign(gₙ) · |gₙ|^{q-1}
  let h_n := fun a => Real.sign (g_n a) * |g_n a| ^ (q.toReal - 1)
  -- hₙ is measurable
  have hhn_meas : Measurable h_n :=
    (((hg_meas.min measurable_const).max measurable_const).sign).mul
      (((hg_meas.min measurable_const).max measurable_const).abs.pow_const _)
  -- hₙ is bounded: ‖hₙ(a)‖ ≤ n^{q-1}
  have hhn_bound : ∀ᵐ a ∂μ, ‖h_n a‖ ≤ (n : ℝ) ^ (q.toReal - 1) :=
    ae_of_all μ fun a => by
      simp only [h_n, Real.norm_eq_abs, abs_mul]
      calc |Real.sign (g_n a)| * |g_n a| ^ (q.toReal - 1)
          ≤ 1 * |g_n a| ^ (q.toReal - 1) := by
            apply mul_le_mul_of_nonneg_right (Real.abs_sign_le_one _) (by positivity)
        _ = |g_n a| ^ (q.toReal - 1) := one_mul _
        _ ≤ (n : ℝ) ^ (q.toReal - 1) :=
            Real.rpow_le_rpow (abs_nonneg _) (hgn_bound a)
              (by linarith [hpq.symm.one_lt_of_lt hp1])
  -- hₙ ∈ Lp (bounded on finite measure space)
  have hhn_memLp : MemLp h_n p μ :=
    MemLp.of_bound ((n : ℝ) ^ (q.toReal - 1)) hhn_meas.aestronglyMeasurable hhn_bound
  -- Pointwise: hₙ(a) · g(a) ≥ hₙ(a) · gₙ(a) (sign(hₙ) matches sign of g - gₙ)
  have hpw : ∀ a, h_n a * g_n a ≤ h_n a * g a := fun a => by
    suffices h : 0 ≤ h_n a * (g a - g_n a) by linarith [mul_sub (h_n a) (g a) (g_n a)]
    simp only [h_n, g_n]
    rcases le_or_gt (g a) (-(n : ℝ)) with h1 | h1
    · -- g(a) ≤ -n: g_n = -n, sign(g_n) = -1 < 0, g - g_n = g + n ≤ 0, product ≥ 0
      have hgn_val : max (min (g a) (n : ℝ)) (-(n : ℝ)) = -(n : ℝ) :=
        max_eq_right (le_trans (min_le_left _ _) h1)
      rw [hgn_val]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        rw [Real.sign_of_neg (neg_lt_zero.mpr hn_pos)]
        have : g a - -(n : ℝ) ≤ 0 := by linarith
        exact mul_nonneg_of_nonpos_of_nonpos (mul_neg_of_neg_of_pos (by norm_num) (by positivity))
          this
    rcases le_or_gt (n : ℝ) (g a) with h2 | h2
    · -- g(a) ≥ n: g_n = n, sign(g_n) = 1 > 0, g - g_n ≥ 0, product ≥ 0
      have hgn_val : max (min (g a) (n : ℝ)) (-(n : ℝ)) = (n : ℝ) := by
        rw [min_eq_right h2, max_eq_left (neg_le_self (Nat.cast_nonneg n))]
      rw [hgn_val]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        rw [Real.sign_of_pos hn_pos]
        exact mul_nonneg (mul_nonneg zero_le_one (by positivity)) (by linarith)
    · -- -n < g(a) < n: g_n = g(a), product = 0
      have hgn_val : max (min (g a) (n : ℝ)) (-(n : ℝ)) = g a := by
        rw [min_eq_left h2.le, max_eq_left (le_of_lt h1)]
      rw [hgn_val, sub_self, mul_zero]
  -- Integrability of hₙ · gₙ and hₙ · g
  have hint_hgn : Integrable (fun a => h_n a * g_n a) μ :=
    (hgn_int.mul_bdd hhn_meas.aestronglyMeasurable hhn_bound).congr
      (ae_of_all μ fun a => mul_comm (g_n a) (h_n a))
  have hint_hg : Integrable (fun a => h_n a * g a) μ :=
    hg_int.bdd_mul hhn_meas.aestronglyMeasurable hhn_bound
  -- Integral inequality: ∫ hₙ gₙ ≤ ∫ hₙ g
  have hint_ineq : ∫ a, h_n a * g_n a ∂μ ≤ ∫ a, h_n a * g a ∂μ :=
    integral_mono hint_hgn hint_hg (fun a => hpw a)
  -- SORRY A: φ(hₙ as Lp) = ∫ hₙ · g dμ
  -- Proof: approxOn hₙ k → hₙ in Lp; φ(approxOn k) = ∫ approxOn k · g by
  --   SimpleFunc.induction; CLM continuity + DCT gives the limit.
  have hphi_hn : φ (hhn_memLp.toLp _) = ∫ a, h_n a * g a ∂μ := by
    -- Step 1: For simple functions sf with MemLp, φ(sf as Lp) = ∫ sf * g
    have phi_simple_eq : ∀ (sf : SimpleFunc α ℝ) (hsf : MemLp ⇑sf p μ),
        φ (hsf.toLp ⇑sf) = ∫ a, ↑sf a * g a ∂μ := by
      intro sf
      induction sf using SimpleFunc.induction with
      | @const c E hE =>
        intro hsf
        have hcoe : ∀ a, ⇑(SimpleFunc.piecewise E hE (SimpleFunc.const α c) (SimpleFunc.const α 0)) a =
            E.indicator (fun _ => c) a := fun a => by
          simp [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_zero,
                Set.indicator_apply, Set.piecewise_apply]
        have hE_fin : μ E ≠ ⊤ := measure_ne_top μ E
        have hind : MemLp (E.indicator (fun _ => (1 : ℝ))) p μ :=
          indicator_memLp hE hE_fin p (le_of_lt hp1) hptop
        have heq_Lp : hsf.toLp ⇑(SimpleFunc.piecewise E hE (SimpleFunc.const α c) (SimpleFunc.const α 0)) =
            c • hind.toLp (E.indicator (fun _ => 1)) := by
          apply Lp.ext
          filter_upwards [hsf.coeFn_toLp,
            Lp.coeFn_smul c (hind.toLp (E.indicator (fun _ => (1 : ℝ)))),
            hind.coeFn_toLp] with a ha hsmul hind_ae
          rw [ha, hsmul, hind_ae, hcoe]
          simp [Pi.smul_apply, smul_eq_mul, Set.indicator_apply]
          split_ifs <;> ring
        rw [heq_Lp, map_smul, smul_eq_mul]
        have hphi_ind : φ (hind.toLp (E.indicator (fun _ => (1 : ℝ)))) = ν E := by
          rw [hν_eq E hE]
          congr 1
          apply Lp.ext
          filter_upwards [hind.coeFn_toLp,
            (indicator_memLp hE hE_fin p (le_of_lt hp1) hptop).coeFn_toLp] with a h1 h2
          exact h1.trans h2.symm
        rw [hphi_ind, rnDeriv_integral_eq ν hac hE]
        simp only [hcoe]
        calc c * ∫ a in E, g a ∂μ
            = ∫ a in E, c * g a ∂μ := (integral_mul_left c (fun a => g a)).symm
          _ = ∫ a, E.indicator (fun _ => c * g a) a ∂μ := (integral_indicator hE).symm
          _ = ∫ a, E.indicator (fun _ => c) a * g a ∂μ := by
                congr 1; ext a
                simp only [Set.indicator_apply]
                split_ifs <;> ring
      | @add sf₁ sf₂ hdisj IH₁ IH₂ =>
        intro h12
        have hsf₁_le : ∀ a, ‖(sf₁ : α → ℝ) a‖ ≤ ‖(sf₁ + sf₂ : SimpleFunc α ℝ) a‖ :=
          fun a => by
            simp only [SimpleFunc.coe_add, Pi.add_apply]
            by_cases ha : (sf₁ : α → ℝ) a = 0
            · simp [ha]
            · have : (sf₂ : α → ℝ) a = 0 := Function.nmem_support.mp
                  (disjoint_left.mp hdisj (Function.mem_support.mpr ha))
              simp [this]
        have hsf₂_le : ∀ a, ‖(sf₂ : α → ℝ) a‖ ≤ ‖(sf₁ + sf₂ : SimpleFunc α ℝ) a‖ :=
          fun a => by
            simp only [SimpleFunc.coe_add, Pi.add_apply]
            by_cases ha : (sf₂ : α → ℝ) a = 0
            · simp [ha]
            · have : (sf₁ : α → ℝ) a = 0 := Function.nmem_support.mp
                  (disjoint_left.mp hdisj.symm (Function.mem_support.mpr ha))
              rw [this, zero_add]; exact le_refl _
        have hsf₁ : MemLp ⇑sf₁ p μ := h12.mono
          sf₁.measurable.aestronglyMeasurable (ae_of_all μ hsf₁_le)
        have hsf₂ : MemLp ⇑sf₂ p μ := h12.mono
          sf₂.measurable.aestronglyMeasurable (ae_of_all μ hsf₂_le)
        have h12_split : h12.toLp ⇑(sf₁ + sf₂) = hsf₁.toLp ⇑sf₁ + hsf₂.toLp ⇑sf₂ := by
          apply Lp.ext
          filter_upwards [h12.coeFn_toLp,
            Lp.coeFn_add (hsf₁.toLp ⇑sf₁) (hsf₂.toLp ⇑sf₂),
            hsf₁.coeFn_toLp, hsf₂.coeFn_toLp] with a h12ae hadd hsf₁ae hsf₂ae
          rw [h12ae, hadd, Pi.add_apply, hsf₁ae, hsf₂ae]
          simp only [SimpleFunc.coe_add, Pi.add_apply]
        have hsf₁_bdd : ∀ᵐ a ∂μ, ‖(sf₁ : α → ℝ) a‖ ≤ sf₁.range.sum (fun c => ‖c‖) :=
          ae_of_all μ fun a =>
            Finset.single_le_sum (fun c _ => norm_nonneg c) _ (sf₁.mem_range_self a)
        have hsf₂_bdd : ∀ᵐ a ∂μ, ‖(sf₂ : α → ℝ) a‖ ≤ sf₂.range.sum (fun c => ‖c‖) :=
          ae_of_all μ fun a =>
            Finset.single_le_sum (fun c _ => norm_nonneg c) _ (sf₂.mem_range_self a)
        have hint₁ : Integrable (fun a => ↑sf₁ a * g a) μ :=
          hg_int.bdd_mul sf₁.measurable.aestronglyMeasurable hsf₁_bdd
        have hint₂ : Integrable (fun a => ↑sf₂ a * g a) μ :=
          hg_int.bdd_mul sf₂.measurable.aestronglyMeasurable hsf₂_bdd
        rw [h12_split, map_add, IH₁ hsf₁, IH₂ hsf₂, ← integral_add hint₁ hint₂]
        congr 1; ext a
        simp [SimpleFunc.coe_add, Pi.add_apply, add_mul]
    -- Step 2: Approximate h_n by simple functions in Lp
    have htendsto_Lp : Tendsto
        (fun k => (SimpleFunc.memLp_approxOn_range hhn_meas hhn_memLp k).toLp _)
        atTop (𝓝 (hhn_memLp.toLp h_n)) :=
      SimpleFunc.tendsto_approxOn_range_Lp hptop hhn_meas hhn_memLp
    -- Step 3: CLM continuity: φ(apx k) → φ(h_n)
    have htendsto_phi : Tendsto
        (fun k => φ ((SimpleFunc.memLp_approxOn_range hhn_meas hhn_memLp k).toLp _))
        atTop (𝓝 (φ (hhn_memLp.toLp h_n))) :=
      φ.continuous.continuousAt.tendsto.comp htendsto_Lp
    -- Step 4: φ(apx k) = ∫ (apx k) * g for each k
    have hphi_apx : ∀ k, φ ((SimpleFunc.memLp_approxOn_range hhn_meas hhn_memLp k).toLp _) =
        ∫ a, ↑(SimpleFunc.approxOn h_n hhn_meas (Set.range h_n ∪ {0}) 0 (by simp) k) a * g a ∂μ :=
      fun k => phi_simple_eq _ (SimpleFunc.memLp_approxOn_range hhn_meas hhn_memLp k)
    -- Step 5: DCT: ∫ (apx k) * g → ∫ h_n * g
    have htendsto_int : Tendsto
        (fun k => ∫ a, ↑(SimpleFunc.approxOn h_n hhn_meas (Set.range h_n ∪ {0}) 0 (by simp) k) a * g a ∂μ)
        atTop (𝓝 (∫ a, h_n a * g a ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence
          (fun a => 2 * (n : ℝ) ^ (q.toReal - 1) * ‖g a‖)
      · exact fun k => ((SimpleFunc.approxOn h_n hhn_meas (Set.range h_n ∪ {0}) 0 (by simp) k).measurable
            |>.aestronglyMeasurable.mul hg_meas.aestronglyMeasurable)
      · exact hg_int.norm.const_mul _
      · intro k
        filter_upwards [hhn_bound] with a ha
        simp only [Real.norm_eq_abs, abs_mul]
        have hbnd : ‖(SimpleFunc.approxOn h_n hhn_meas (Set.range h_n ∪ {0}) 0 (by simp) k : α → ℝ) a‖ ≤
            2 * ‖h_n a‖ := by
          have := SimpleFunc.norm_approxOn_zero_le hhn_meas
            (show (0 : ℝ) ∈ Set.range h_n ∪ {0} from by simp) a k
          simp only [Real.norm_eq_abs] at this ⊢; linarith
        calc |↑(SimpleFunc.approxOn h_n hhn_meas (Set.range h_n ∪ {0}) 0 (by simp) k) a| * |g a|
            ≤ 2 * ‖h_n a‖ * |g a| := mul_le_mul_of_nonneg_right hbnd (abs_nonneg _)
          _ ≤ 2 * (n : ℝ) ^ (q.toReal - 1) * |g a| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              simpa [Real.norm_eq_abs] using ha
      · apply ae_of_all; intro a
        have hapx : Tendsto
            (fun k => (SimpleFunc.approxOn h_n hhn_meas (Set.range h_n ∪ {0}) 0 (by simp) k : α → ℝ) a)
            atTop (𝓝 (h_n a)) :=
          SimpleFunc.tendsto_approxOn hhn_meas (by simp)
            (subset_closure (Set.mem_union_left _ (Set.mem_range_self a)))
        exact hapx.mul_const (g a)
    -- Step 6: Unique limits give φ(h_n) = ∫ h_n * g
    have htendsto_phi' : Tendsto
        (fun k => ∫ a, ↑(SimpleFunc.approxOn h_n hhn_meas (Set.range h_n ∪ {0}) 0 (by simp) k) a * g a ∂μ)
        atTop (𝓝 (φ (hhn_memLp.toLp h_n))) := by
      convert htendsto_phi using 1
      ext k; exact (hphi_apx k).symm
    exact tendsto_nhds_unique htendsto_phi' htendsto_int
  -- SORRY B: ∫ hₙ gₙ dμ = (eLpNorm gₙ q μ ^ q.toReal).toReal
  have hint_hn_gn : ∫ a, h_n a * g_n a ∂μ = (eLpNorm g_n q μ ^ q.toReal).toReal := by
    have hq_ne_zero : q ≠ 0 := by
      intro hq; rw [hq, ENNReal.toReal_zero] at hpq; linarith [hpq.symm.pos]
    -- Step 1: pointwise identity h_n a * g_n a = |g_n a| ^ q.toReal
    -- sign(x) * x = |x| for all x : ℝ, so sign(gₙ)|gₙ|^{q-1} * gₙ = |gₙ|^q
    have hpw2 : ∀ a, h_n a * g_n a = |g_n a| ^ q.toReal := fun a => by
      simp only [h_n]
      have hsign : Real.sign (g_n a) * g_n a = |g_n a| := by
        rcases lt_trichotomy (g_n a) 0 with ha | rfl | ha
        · simp [Real.sign_of_neg ha, abs_of_neg ha]
        · simp
        · simp [Real.sign_of_pos ha, abs_of_pos ha]
      rw [show Real.sign (g_n a) * |g_n a| ^ (q.toReal - 1) * g_n a =
          |g_n a| ^ (q.toReal - 1) * (Real.sign (g_n a) * g_n a) from by ring,
          hsign, show |g_n a| = |g_n a| ^ (1 : ℝ) from (Real.rpow_one _).symm,
          ← Real.rpow_add (abs_nonneg _)]
      norm_num
    simp_rw [hpw2]
    -- Step 2: |g_n a|^q = ((‖g_n a‖₊ : ℝ≥0∞)^q).toReal
    -- Uses: ENNReal.coe_rpow_of_nonneg (coercion is ≠ ⊤), ENNReal.coe_toReal, NNReal.coe_rpow
    have hpw3 : ∀ a, |g_n a| ^ q.toReal = ((‖g_n a‖₊ : ℝ≥0∞) ^ q.toReal).toReal := fun a => by
      rw [ENNReal.coe_rpow_of_nonneg (le_of_lt hq_pos), ENNReal.coe_toReal, NNReal.coe_rpow]
      simp [Real.norm_eq_abs]
    simp_rw [hpw3]
    -- Step 3: ∫ ((‖g_n‖₊ : ℝ≥0∞)^q).toReal = (∫⁻ (‖g_n‖₊ : ℝ≥0∞)^q).toReal
    -- via integral_toReal (base is finite: coercion from ℝ≥0 is always ≠ ⊤)
    have hf_meas : AEMeasurable (fun a => (‖g_n a‖₊ : ℝ≥0∞) ^ q.toReal) μ :=
      ((hg_meas.min measurable_const).max measurable_const).nnnorm
        |>.coe_nnreal_ennreal |>.ennreal_rpow_const q.toReal |>.aemeasurable
    have hf_ne_top : ∀ᵐ a ∂μ, (‖g_n a‖₊ : ℝ≥0∞) ^ q.toReal ≠ ⊤ :=
      ae_of_all μ fun a => by
        rw [ENNReal.coe_rpow_of_nonneg (le_of_lt hq_pos)]; exact ENNReal.coe_ne_top
    rw [integral_toReal hf_meas hf_ne_top]
    -- Step 4: (∫⁻ (‖g_n‖₊ : ℝ≥0∞)^q).toReal = (eLpNorm g_n q μ ^ q.toReal).toReal
    -- via eLpNorm_eq_lintegral_rpow_enorm + ENNReal.rpow_mul
    congr 1
    rw [eLpNorm_eq_lintegral_rpow_enorm hq_ne_zero hqne_top, ← ENNReal.rpow_mul,
        one_div, inv_mul_cancel₀ hq_pos.ne', ENNReal.rpow_one]
  -- SORRY C: the chain gives eLpNorm gₙ q μ ≤ ENNReal.ofReal ‖φ‖
  -- Step C0: setup
  have hp_pos' : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans one_pos hp1)) hptop
  -- Step C1: gₙ ∈ Lq (bounded on finite measure)
  have hgn_memLq : MemLp g_n q μ :=
    truncated_rn_deriv_memLq g hg_meas n q
      (by linarith [hpq.symm.one_lt_of_lt hp1]) hqne_top
  have hgn_ne_top : eLpNorm g_n q μ ≠ ⊤ := (hgn_memLq.eLpNorm_lt_top).ne
  -- Step C2: eLpNorm h_n p μ = eLpNorm g_n q μ ^ (q.toReal / p.toReal)
  -- Proof: |h_n a|^p.toReal = |g_n a|^q.toReal pointwise (from p(q-1)=q via HolderConjugate),
  -- so ∫⁻ ‖h_n‖₊^p = ∫⁻ ‖g_n‖₊^q, hence eLpNorm h_n p^p = eLpNorm g_n q^q,
  -- hence eLpNorm h_n p = (eLpNorm g_n q^q)^(1/p) = eLpNorm g_n q^(q/p).
  have hn_eLpNorm : eLpNorm h_n p μ = eLpNorm g_n q μ ^ (q.toReal / p.toReal) := by
    have hp_ne : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp1)
    have hq_ne : q ≠ 0 := by
      intro hq; rw [hq, ENNReal.toReal_zero] at hq_pos; linarith
    -- p * q = p + q (from 1/p + 1/q = 1)
    have hpq_prod : p.toReal * q.toReal = p.toReal + q.toReal := by
      have h_conj : p.toReal⁻¹ + q.toReal⁻¹ = 1 := hpq.inv_add_inv_eq_one
      field_simp [ne_of_gt hp_pos', ne_of_gt hq_pos] at h_conj; linarith
    -- Pointwise: |h_n a|^p = |g_n a|^q (in ℝ)
    have hpw_real : ∀ a, |h_n a| ^ p.toReal = |g_n a| ^ q.toReal := fun a => by
      simp only [h_n]
      rcases eq_or_ne (g_n a) 0 with ha | ha
      · simp [ha]
      · have habs_pos : 0 < |g_n a| := abs_pos.mpr ha
        have hsign1 : |Real.sign (g_n a)| = 1 := by
          rcases lt_trichotomy (g_n a) 0 with h | h | h
          · simp [Real.sign_of_neg h]
          · exact absurd h ha
          · simp [Real.sign_of_pos h]
        rw [abs_mul, hsign1, one_mul,
            abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
            ← Real.rpow_mul (abs_nonneg _)]
        congr 1; nlinarith [hpq_prod]
    -- Lift pointwise equality to ℝ≥0∞ via NNReal coercions
    have hpw_enn : ∀ a, (‖h_n a‖₊ : ℝ≥0∞) ^ p.toReal =
        (‖g_n a‖₊ : ℝ≥0∞) ^ q.toReal := fun a => by
      rw [← ENNReal.coe_rpow_of_nonneg _ (le_of_lt hp_pos'),
          ← ENNReal.coe_rpow_of_nonneg _ (le_of_lt hq_pos)]
      norm_cast
      apply NNReal.coe_injective
      simp only [NNReal.coe_rpow, NNReal.coe_nnnorm, Real.norm_eq_abs]
      exact hpw_real a
    -- ∫⁻ ‖h_n‖ₑ^p = ∫⁻ ‖g_n‖ₑ^q (‖·‖ₑ = (‖·‖₊:ℝ≥0∞) definitionally, so hpw_enn applies)
    have hlint_eq : ∫⁻ a, ‖h_n a‖ₑ ^ p.toReal ∂μ =
        ∫⁻ a, ‖g_n a‖ₑ ^ q.toReal ∂μ := lintegral_congr (fun a => hpw_enn a)
    -- eLpNorm h_n p = eLpNorm g_n q ^ (q/p)
    -- Strategy: rewrite both sides using eLpNorm_eq_lintegral_rpow_enorm,
    -- apply hlint_eq to equate the lintegrals, then use rpow algebra.
    rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne hptop,
        eLpNorm_eq_lintegral_rpow_enorm hq_ne hqne_top,
        hlint_eq, ← ENNReal.rpow_mul]
    congr 1
    field_simp [ne_of_gt hp_pos', ne_of_gt hq_pos]
  -- Step C3: Lp norm of hhn_memLp.toLp h_n equals (eLpNorm h_n p μ).toReal
  have hn_norm : ‖hhn_memLp.toLp h_n‖ = (eLpNorm h_n p μ).toReal := by
    simp only [MeasureTheory.Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hhn_memLp.coeFn_toLp)
  -- Step C4: arithmetic identity q.toReal / p.toReal + 1 = q.toReal
  -- (from 1/p + 1/q = 1 → pq = p + q → q/p = q - 1 → q/p + 1 = q)
  have hqp_eq : q.toReal / p.toReal + 1 = q.toReal := by
    have h_conj : p.toReal⁻¹ + q.toReal⁻¹ = 1 := hpq.inv_add_inv_eq_one
    have hpq_prod : p.toReal * q.toReal = p.toReal + q.toReal := by
      have hp'' := ne_of_gt hp_pos'
      have hq'' := ne_of_gt hq_pos
      field_simp [hp'', hq''] at h_conj
      linarith
    field_simp [ne_of_gt hp_pos']
    linarith
  -- Step C5: the key chain — (‖gₙ‖_q)^q ≤ ‖φ‖ · (‖gₙ‖_q)^(q/p)
  set x := (eLpNorm g_n q μ).toReal with hx_def
  have hx_nn : 0 ≤ x := ENNReal.toReal_nonneg
  have hchain : x ^ q.toReal ≤ ‖φ‖ * x ^ (q.toReal / p.toReal) := by
    have hlhs : x ^ q.toReal = (eLpNorm g_n q μ ^ q.toReal).toReal := by
      simp [hx_def, ENNReal.toReal_rpow]
    have hrhs_eq : x ^ (q.toReal / p.toReal) = (eLpNorm h_n p μ).toReal := by
      rw [hn_eLpNorm, hx_def, ENNReal.toReal_rpow]
    rw [hlhs, hrhs_eq]
    calc (eLpNorm g_n q μ ^ q.toReal).toReal
        = ∫ a, h_n a * g_n a ∂μ := hint_hn_gn.symm
      _ ≤ ∫ a, h_n a * g a ∂μ := hint_ineq
      _ = φ (hhn_memLp.toLp h_n) := hphi_hn.symm
      _ ≤ ‖φ (hhn_memLp.toLp h_n)‖ := le_abs_self _
      _ ≤ ‖φ‖ * ‖hhn_memLp.toLp h_n‖ := ContinuousLinearMap.le_opNorm φ _
      _ = ‖φ‖ * (eLpNorm h_n p μ).toReal := by rw [hn_norm]
  -- Step C6: real arithmetic — x ≤ ‖φ‖
  have hx_le : x ≤ ‖φ‖ := by
    rcases le_or_gt x 0 with hx | hx
    · linarith [norm_nonneg φ]
    · -- x > 0: write x^q = x^(q/p) * x, then divide by x^(q/p) > 0
      have hrpow : x ^ q.toReal = x ^ (q.toReal / p.toReal) * x := by
        conv_lhs =>
          rw [show q.toReal = q.toReal / p.toReal + 1 from by linarith [hqp_eq]]
        rw [Real.rpow_add hx, Real.rpow_one]
      have hxqp_pos : 0 < x ^ (q.toReal / p.toReal) := Real.rpow_pos_of_pos hx _
      have hkey : x ^ (q.toReal / p.toReal) * x ≤ x ^ (q.toReal / p.toReal) * ‖φ‖ :=
        calc x ^ (q.toReal / p.toReal) * x
            = x ^ q.toReal := hrpow.symm
          _ ≤ ‖φ‖ * x ^ (q.toReal / p.toReal) := hchain
          _ = x ^ (q.toReal / p.toReal) * ‖φ‖ := mul_comm _ _
      exact le_of_mul_le_mul_left hkey hxqp_pos
  -- Step C7: lift back to ENNReal
  calc eLpNorm g_n q μ
      = ENNReal.ofReal (eLpNorm g_n q μ).toReal :=
          (ENNReal.ofReal_toReal hgn_ne_top).symm
    _ ≤ ENNReal.ofReal ‖φ‖ := ENNReal.ofReal_le_ofReal hx_le
DEAD CODE END-/

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
    [IsFiniteMeasure μ] [SigmaFinite μ] [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  intro φ
  -- Step 1: Construct signed measure ν(E) = φ(1_E)
  let ν := signedMeasureOfFunctional p (le_of_lt hp1) hptop φ
  have hac : ν.AbsolutelyContinuous μ.toENNRealVectorMeasure :=
    signedMeasureOfFunctional_ac p (le_of_lt hp1) hptop φ
  have hν_eq : ∀ (E : Set α) (hE : MeasurableSet E),
      ν E = φ ((indicator_memLp hE (measure_ne_top μ E) p (le_of_lt hp1) hptop).toLp _) :=
    fun E hE => signedMeasureOfFunctional_indicator p (le_of_lt hp1) hptop φ hE
  -- Step 2: RN derivative g = ν.rnDeriv μ (used directly without set to avoid let-binding issues)
  -- Step 3: Agreement on indicators φ(1_E) = ∫_E g dμ
  have hagree : ∀ (E : Set α) (hE : MeasurableSet E) (_hfin : μ E ≠ ⊤),
      φ ((indicator_memLp hE _hfin p (le_of_lt hp1) hptop).toLp _) =
      ∫ a in E, ν.rnDeriv μ a ∂μ := by
    intro E hE _hfin
    rw [← hν_eq E hE]
    exact rnDeriv_integral_eq ν hac hE
  -- Step 4: g ∈ Lq via Hölder extremizer + rn_deriv_memLq_from_trunc
  refine ⟨ν.rnDeriv μ, ?_, ?_⟩
  · -- Lq membership
    exact rn_deriv_memLq_from_trunc p q hp1 hptop hpq (ν.rnDeriv μ)
        (ν.measurable_rnDeriv μ) ‖φ‖
        (fun n => holder_extremizer_lq_bound p q hp1 hptop hpq φ ν hac hν_eq n)
  · -- Step 5: Full representation via integral_representation (Lp.induction)
    exact integral_representation p q hp1 hptop hpq φ (ν.rnDeriv μ)
        (rn_deriv_memLq_from_trunc p q hp1 hptop hpq (ν.rnDeriv μ)
          (ν.measurable_rnDeriv μ) ‖φ‖
          (fun n => holder_extremizer_lq_bound p q hp1 hptop hpq φ ν hac hν_eq n))
        hagree

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
