/-
  Aristotle targets for FairGamesTheoremOQ03
  (Martingale Application Theorems: Optional Stopping, Doob's Inequality)
  Routine supporting lemmas for automated proof search.
  See FairGamesTheoremOQ03.lean for the main formalization.

  These lemmas provide building blocks for:
  - stoppedValue and IsStoppingTime properties with ℕ∞
  - Optional stopping theorem helpers (submartingale direction)
  - NNReal to real conversion for measure-theoretic bounds
  - Doob's maximal inequality real-valued formulation
  - Integral monotonicity and equality helpers
-/
import Mathlib

open MeasureTheory

namespace FairGamesOQ03.Aristotle

/-
  ## Section 1: stoppedValue Properties
-/

/-- stoppedValue at a constant stopping time equals the process at that time -/
lemma stoppedValue_const {Ω : Type*} {m : MeasurableSpace Ω}
    (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    stoppedValue f (fun _ => (n : ℕ∞)) ω = f n ω := by
  simp [stoppedValue]

/-- stoppedValue at min(τ, N) equals stoppedValue at τ when τ ≤ N -/
lemma stoppedValue_eq_of_le {Ω : Type*} {m : MeasurableSpace Ω}
    (f : ℕ → Ω → ℝ) (τ : Ω → ℕ∞) (N : ℕ) (ω : Ω) (h : τ ω ≤ N) :
    stoppedValue f τ ω = stoppedValue f (fun ω' => min (τ ω') N) ω := by
  simp only [stoppedValue, min_eq_left h]

/-- Measurability of stoppedValue for adapted processes -/
lemma stoppedValue_measurable {Ω : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m} (f : ℕ → Ω → ℝ) (τ : Ω → ℕ∞)
    (hf : Adapted ℱ f) (hτ : IsStoppingTime ℱ τ) (N : ℕ) (hτN : ∀ ω, τ ω ≤ N) :
    Measurable (stoppedValue f τ) :=
  (stronglyMeasurable_stoppedValue_of_le hf.progMeasurable_of_discrete hτ hτN).mono
    (ℱ.le N) |>.measurable

/-
  ## Section 2: IsStoppingTime Helpers for ℕ∞
-/

/-- The constant function N is a ℕ∞-stopping time -/
lemma isStoppingTime_const {Ω : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m} (N : ℕ∞) :
    IsStoppingTime ℱ (fun _ : Ω => N) :=
  MeasureTheory.isStoppingTime_const ℱ N

/-- min of two stopping times is a stopping time -/
lemma isStoppingTime_min {Ω : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m} (τ π : Ω → ℕ∞)
    (hτ : IsStoppingTime ℱ τ) (hπ : IsStoppingTime ℱ π) :
    IsStoppingTime ℱ (fun ω => min (τ ω) (π ω)) :=
  hτ.min hπ

/-- A stopped ℕ∞-stopping time bounded by N gives integrability -/
lemma stoppedValue_integrable {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m} (f : ℕ → Ω → ℝ) (τ : Ω → ℕ∞)
    (hτ : IsStoppingTime ℱ τ) (hf : ∀ n, Integrable (f n) μ) (N : ℕ) (hτN : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue f τ) μ :=
  integrable_stoppedValue ℕ hτ hf hτN

/-
  ## Section 3: Optional Stopping Integral Helpers
-/

/-- For a martingale and bounded ℕ∞-stopping time τ ≤ π ≤ N:
    ∫ stoppedValue f τ = ∫ stoppedValue f π (via submartingale iff) -/
lemma martingale_stopped_integral_eq {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m} (f : ℕ → Ω → ℝ)
    (hf : Martingale f ℱ μ)
    (τ π : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ) (hπ : IsStoppingTime ℱ π)
    (hτπ : τ ≤ π) (N : ℕ) (hπN : ∀ ω, π ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, stoppedValue f π ω ∂μ := by
  have h₁ := hf.submartingale.expected_stoppedValue_mono hτ hπ hτπ hπN
  have h₂ := hf.supermartingale.neg.expected_stoppedValue_mono hτ hπ hτπ hπN
  simp only [stoppedValue, Pi.neg_apply, integral_neg] at h₁ h₂ ⊢
  linarith

/-- For a martingale, ∫ stoppedValue f τ = ∫ f 0 when τ ≤ N -/
lemma martingale_stopped_eq_initial {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m} (f : ℕ → Ω → ℝ)
    (hf : Martingale f ℱ μ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ) (N : ℕ) (hτN : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, f 0 ω ∂μ := by
  have h₁ := hf.submartingale.expected_stoppedValue_mono
    (MeasureTheory.isStoppingTime_const ℱ 0) hτ (fun _ => zero_le _) hτN
  have h₂ := hf.supermartingale.neg.expected_stoppedValue_mono
    (MeasureTheory.isStoppingTime_const ℱ 0) hτ (fun _ => zero_le _) hτN
  simp only [stoppedValue_const, stoppedValue, Pi.neg_apply, integral_neg] at h₁ h₂ ⊢
  linarith

/-
  ## Section 4: NNReal to Real Conversion Helpers
-/

/-- ENNReal.toReal of a probability measure of a set is ≤ 1 -/
lemma measure_toReal_le_one {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (s : Set Ω) :
    (μ s).toReal ≤ 1 :=
  ENNReal.toReal_le_one.mpr prob_le_one

/-- thresh * (μ s).toReal ≤ integral bound from Doob's maximal ineq via NNReal -/
lemma doob_maximal_real_of_nnreal {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m} (f : ℕ → Ω → ℝ)
    (hf : Submartingale f ℱ μ) (hpos : ∀ n ω, 0 ≤ f n ω)
    (N : ℕ) (thresh : ℝ) (hthresh : 0 < thresh)
    (s : Set Ω) (hs : s = {ω | ∃ n ≤ N, thresh ≤ f n ω}) :
    thresh * (μ s).toReal ≤ ∫ ω, f N ω ∂μ := by
  rw [hs]
  -- Convert to NNReal threshold for Mathlib's maximal_ineq
  set ε : ℝ≥0 := ⟨thresh, le_of_lt hthresh⟩
  -- The Mathlib-style set using sup over range
  set S := {ω | (ε : ℝ) ≤ (Finset.range (N + 1)).sup'
    Finset.nonempty_range_add_one fun k => f k ω} with hS_def
  -- Mathlib's ENNReal-valued Doob inequality
  have hmain := maximal_ineq hf (fun n => hpos n) N (ε := ε)
  -- Show our set equals the Mathlib set
  have hset_eq : {ω | ∃ n ≤ N, thresh ≤ f n ω} = S := by
    ext ω
    simp only [Set.mem_setOf_eq, hS_def, NNReal.coe_mk,
      Finset.le_sup'_iff Finset.nonempty_range_add_one,
      Finset.mem_range, Nat.lt_succ_iff, S]
  rw [hset_eq]
  calc thresh * (μ S).toReal
      = (ε : ℝ≥0∞).toReal * (μ S).toReal := by congr 1; simp [ε]
    _ = ((ε : ℝ≥0∞) * μ S).toReal := ENNReal.toReal_mul.symm
    _ ≤ (ENNReal.ofReal (∫ ω in S, f N ω ∂μ)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = ∫ ω in S, f N ω ∂μ :=
        ENNReal.toReal_ofReal (integral_nonneg fun ω => hpos N ω)
    _ ≤ ∫ ω, f N ω ∂μ :=
        setIntegral_le_integral (hf.integrable N) (eventually_of_forall (hpos N))

/-- The set {ω | ∃ n ≤ N, thresh ≤ f n ω} is measurable for adapted f -/
lemma maximal_set_measurable {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m} (f : ℕ → Ω → ℝ)
    (hf : Submartingale f ℱ μ)
    (N : ℕ) (thresh : ℝ) :
    MeasurableSet {ω | ∃ n ≤ N, thresh ≤ f n ω} := by
  -- Rewrite as finite union over {0,...,N}
  have heq : {ω | ∃ n ≤ N, thresh ≤ f n ω} =
      ⋃ n ∈ Finset.range (N + 1), {ω | thresh ≤ f n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨n, hn, h⟩; exact ⟨n, Nat.lt_succ_of_le hn, h⟩
    · rintro ⟨n, hn, h⟩; exact ⟨n, Nat.lt_succ_iff.mp hn, h⟩
  rw [heq]
  apply MeasurableSet.biUnion (Finset.toSet_finite _).countable
  intro n _
  -- {thresh ≤ f n} is measurable because f n is measurable (adapted, then filtered ≤ ambient)
  exact measurableSet_le measurable_const ((hf.adapted n).measurable.mono (ℱ.le n))

end FairGamesOQ03.Aristotle
