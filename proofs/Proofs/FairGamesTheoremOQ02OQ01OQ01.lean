import Mathlib
import Proofs.FairGamesTheoremOQ02OQ01

/-!
# Wald's Identity: Formalization via Mathlib

## Research Problem: fair-games-theorem-oq-02-oq-01-oq-01

**Open Question** (from FairGamesTheoremOQ02OQ01 / Doob's OST): Can Wald's Identity
itself be formalized in Lean 4? Wald's Identity is a companion to the Optional Stopping
Theorem that gives the expected value of a stopped sum of i.i.d. random variables.

**Answer**: Yes. This file provides a complete formalization of Wald's Identity using
Mathlib's probability infrastructure.

## Wald's Identity (1944)

Let (Ω, ℱ, P) be a probability space. Let X₀, X₁, X₂, ... be i.i.d. integrable random
variables with common mean e = E[X₀]. Let τ be a stopping time (w.r.t. the natural
filtration of the sequence) with E[τ] < ∞. Then:

    E[X₁ + X₂ + ... + X_τ] = e · E[τ]

## Proof Strategy

We use the **indicator decomposition**:

    X₁ + X₂ + ... + X_τ = ∑_{k≥0} X_{k+1} · 1_{τ > k}

The key independence fact: X_{k+1} is independent of {τ > k}, since:
- {τ > k} = {τ ≤ k}ᶜ ∈ ℱ_k (stopping time condition)
- X_{k+1} ⊥ ℱ_k by i.i.d. (via Mathlib's `iIndepFun.condExp_natural_ae_eq_of_lt`)

This gives: E[X_{k+1} · 1_{τ > k}] = E[X_{k+1}] · P(τ > k) = e · P(τ > k).

By Fubini and the tail sum formula E[τ] = ∑_{k≥0} P(τ > k):
    E[sum] = ∑_{k≥0} e · P(τ > k) = e · E[τ]

## Mathlib Infrastructure Used

- `iIndepFun.indep_comap_natural_of_lt`: X_{k+1} ⊥ ℱ_k
- `iIndepFun.condExp_natural_ae_eq_of_lt`: E[X_{k+1} | ℱ_k] = E[X_{k+1}]
- `condExp_mul_of_stronglyMeasurable_left`: pull-out property
- `integral_condExp`: E[E[f | m]] = E[f]
- `IndepFun.integral_fun_mul_eq_mul_integral`: E[f*g] = E[f]*E[g] for independent f,g
- `IdentDistrib.integral_eq`: E[X_n] = E[X_0] for identical distributions

## Tags: probability, martingale, stopping-time, wald, expectation, iid
-/

noncomputable section

open MeasureTheory MeasureTheory.Filtration ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ)
  (hX_meas : ∀ n, StronglyMeasurable (X n))
  (hX_indep : iIndepFun X μ)
  (hX_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
  (hX_int : Integrable (X 0) μ)

namespace WaldIdentity

/-! ### Natural Filtration -/

/-- The natural filtration of the process X. -/
abbrev ℱ : Filtration ℕ m0 := Filtration.natural X hX_meas

/-! ### Key Measurability Lemmas -/

/-- For a stopping time τ, the event {k < τ} is ℱ_k-measurable.
    This follows from {τ > k} = {τ ≤ k}ᶜ and {τ ≤ k} ∈ ℱ_k. -/
theorem stopping_gt_measurable
    (τ : Ω → ℕ) (hτ : IsStoppingTime (ℱ μ X hX_meas) τ) (k : ℕ) :
    MeasurableSet[(ℱ μ X hX_meas) k] {ω | k < τ ω} := by
  have : {ω : Ω | k < τ ω} = {ω | τ ω ≤ k}ᶜ := by
    ext ω; simp [not_le]
  rw [this]
  exact (hτ k).compl

/-- The indicator 1_{k < τ} is ℱ_k-StronglyMeasurable. -/
theorem indicator_gt_sm
    (τ : Ω → ℕ) (hτ : IsStoppingTime (ℱ μ X hX_meas) τ) (k : ℕ) :
    StronglyMeasurable[(ℱ μ X hX_meas) k]
      (Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ))) := by
  apply MeasurableSet.stronglyMeasurable_indicator stronglyMeasurable_const
  exact stopping_gt_measurable μ X hX_meas τ hτ k

/-- All X n are integrable (by IdentDistrib with X 0). -/
theorem X_integrable (n : ℕ) : Integrable (X n) μ :=
  (hX_ident n).integrable_iff.mpr hX_int

/-! ### The Core Independence Computation -/

/-- **Key Lemma**: E[X_{k+1} · 1_{τ > k}] = E[X 0] · P(τ > k)

    The proof uses:
    1. Tower property: E[f] = E[E[f | ℱ_k]]
    2. Pull-out: E[1_{τ>k} · X_{k+1} | ℱ_k] = 1_{τ>k} · E[X_{k+1} | ℱ_k]
       (since 1_{τ>k} is ℱ_k-measurable)
    3. Independence: E[X_{k+1} | ℱ_k] = E[X_{k+1}] = E[X 0]
       (by iIndepFun.condExp_natural_ae_eq_of_lt and IdentDistrib) -/
theorem integral_indicator_prod_eq
    (τ : Ω → ℕ) (hτ : IsStoppingTime (ℱ μ X hX_meas) τ)
    [SigmaFiniteFiltration μ (ℱ μ X hX_meas)] (k : ℕ) :
    ∫ ω, Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * X (k + 1) ω ∂μ =
      (∫ ω, X 0 ω ∂μ) * μ.real {ω | k < τ ω} := by
  -- Denote g := 1_{τ > k} and f := X (k+1)
  -- Step 1: Use tower property E[g * f] = E[E[g * f | ℱ_k]]
  have tower : ∫ ω, Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * X (k + 1) ω ∂μ =
    ∫ ω, μ[fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * X (k + 1) ω |
        (ℱ μ X hX_meas) k] ω ∂μ := by
    rw [integral_condExp (Filtration.le _ _)]
  -- Step 2: Pull-out property
  have pullout : μ[fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * X (k + 1) ω |
      (ℱ μ X hX_meas) k] =ᵐ[μ]
    fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω *
      μ[X (k + 1) | (ℱ μ X hX_meas) k] ω := by
    apply condExp_mul_of_stronglyMeasurable_left
    · exact indicator_gt_sm μ X hX_meas τ hτ k
    · -- Product is integrable: |indicator * X(k+1)| ≤ |X(k+1)|
      exact (X_integrable μ X hX_meas hX_ident hX_int (k+1)).mono
        (((indicator_gt_sm μ X hX_meas τ hτ k).mono (Filtration.le _ _)).aestronglyMeasurable.mul
          (hX_meas (k+1)).aestronglyMeasurable)
        (ae_of_all μ fun ω => by
          simp only [Set.indicator_apply, Pi.one_apply, norm_mul]
          split_ifs <;> simp)
    · exact X_integrable μ X hX_meas hX_ident hX_int (k+1)
  -- Step 3: E[X(k+1) | ℱ_k] = E[X(k+1)] = E[X 0]
  have indep_eq : μ[X (k + 1) | (ℱ μ X hX_meas) k] =ᵐ[μ] fun _ => μ[X (k + 1)] := by
    exact hX_indep.condExp_natural_ae_eq_of_lt hX_meas (Nat.lt_succ_self k)
  have ident_eq : μ[X (k + 1)] = μ[X 0] :=
    (hX_ident (k + 1)).integral_eq
  -- Combine: E[1_{τ>k} * X(k+1) | ℱ_k] = 1_{τ>k} * E[X 0]
  have condexp_eq : μ[fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * X (k + 1) ω |
      (ℱ μ X hX_meas) k] =ᵐ[μ]
    fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * μ[X 0] := by
    filter_upwards [pullout, indep_eq] with ω h1 h2
    rw [h1, h2, ident_eq]
  -- Take outer expectation
  rw [tower]
  rw [integral_congr_ae condexp_eq]
  -- E[1_{τ>k} * E[X 0]] = E[X 0] * P(τ > k)
  rw [integral_mul_const]
  ring_nf
  rw [mul_comm, ← measureReal_def]
  congr 1
  rw [integral_indicator ((ℱ μ X hX_meas).le k (stopping_gt_measurable μ X hX_meas τ hτ k))]
  simp [integral_const]

/-! ### Tail Sum Formula -/

/-- **Tail Sum Identity**: For τ : Ω → ℕ, we have (τ ω : ℝ) = ∑' k, 1_{k < τ ω}.
    This is the key arithmetic identity used in the tail sum formula. -/
theorem nat_cast_eq_tsum_indicator (n : ℕ) :
    (n : ℝ) = ∑' k : ℕ, Set.indicator {k' | k' < n} (fun _ => (1 : ℝ)) k := by
  rw [tsum_eq_sum (s := Finset.range n)]
  · simp [Set.indicator_apply, Finset.sum_ite_eq']
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    exact Set.indicator_of_not_mem (by simp [hk.not_lt])

-- ENNReal tail sum formula: ∫⁻ (τ ω : ℝ≥0∞) ∂μ = ∑' k, μ{k < τ}
private lemma lintegral_nat_eq_tsum_prob (τ : Ω → ℕ) (hτ_meas : Measurable τ) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ = ∑' k : ℕ, μ {ω | k < τ ω} := by
  -- Rewrite τ(ω) as ∑' k, 1_{k < τ(ω)} pointwise (using Ω-indexed indicator to match lintegral_indicator_one)
  have heq : ∀ ω, (τ ω : ℝ≥0∞) = ∑' k : ℕ, {ω' | k < τ ω'}.indicator (1 : Ω → ℝ≥0∞) ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (τ ω))]
    · -- Each term: indicator is 1 for k < τ ω, 0 otherwise
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))]
      simp [Finset.sum_const, Finset.card_range, Nat.smul_one_eq_cast]
    · -- Outside range: indicator = 0
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      exact Set.indicator_of_not_mem (not_lt.mpr hk) _
  simp_rw [heq]
  rw [lintegral_tsum (fun k =>
      (measurable_const.indicator (measurableSet_lt measurable_const hτ_meas)).aemeasurable)]
  simp_rw [lintegral_indicator_one (measurableSet_lt measurable_const hτ_meas)]

/-- **Tail Sum Formula**: E[τ] = ∑' k, P(τ > k). -/
theorem integral_tau_eq_tsum_prob
    (τ : Ω → ℕ) (hτ_meas : Measurable τ) (hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ) :
    ∫ ω, (τ ω : ℝ) ∂μ = ∑' k : ℕ, μ.real {ω | k < τ ω} := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all μ fun ω => Nat.cast_nonneg _) hτ_int.1]
  simp_rw [ENNReal.ofReal_natCast]
  rw [lintegral_nat_eq_tsum_prob μ τ hτ_meas]
  rw [ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ _)]
  congr 1; ext k; rfl

/-! ### Fubini Step -/

-- Norm version of integral_indicator_prod_eq: E[1_{τ>k} · ‖X(k+1)‖] = E[‖X₀‖] · P(τ > k)
private lemma integral_indicator_norm_eq
    (τ : Ω → ℕ) (hτ : IsStoppingTime (ℱ μ X hX_meas) τ)
    [SigmaFiniteFiltration μ (ℱ μ X hX_meas)] (k : ℕ) :
    ∫ ω, ‖Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * X (k + 1) ω‖ ∂μ =
      (∫ ω, ‖X 0 ω‖ ∂μ) * μ.real {ω | k < τ ω} := by
  -- ‖indicator * X(k+1)‖ = indicator * ‖X(k+1)‖ (since indicator ∈ {0, 1})
  have norm_eq : ∀ ω, ‖Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * X (k + 1) ω‖ =
      Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * ‖X (k + 1) ω‖ := fun ω => by
    simp only [Set.indicator_apply, Pi.one_apply]
    split_ifs <;> simp
  simp_rw [norm_eq]
  -- Tower property
  have tower : ∫ ω, Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * ‖X (k + 1) ω‖ ∂μ =
      ∫ ω, μ[fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * ‖X (k + 1) ω‖ |
          (ℱ μ X hX_meas) k] ω ∂μ :=
    (integral_condExp (Filtration.le _ _)).symm
  -- Pull-out: E[indicator * ‖X(k+1)‖ | ℱ_k] = indicator * E[‖X(k+1)‖ | ℱ_k]
  have pullout : μ[fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * ‖X (k + 1) ω‖ |
        (ℱ μ X hX_meas) k] =ᵐ[μ]
      fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω *
        μ[‖X (k + 1)‖ | (ℱ μ X hX_meas) k] ω := by
    apply condExp_mul_of_stronglyMeasurable_left
    · exact indicator_gt_sm μ X hX_meas τ hτ k
    · exact ((X_integrable μ X hX_meas hX_ident hX_int (k+1)).norm).mono
        (((indicator_gt_sm μ X hX_meas τ hτ k).mono (Filtration.le _ _)).aestronglyMeasurable.mul
          (hX_meas (k+1)).norm.aestronglyMeasurable)
        (ae_of_all μ fun ω => by
          simp only [Set.indicator_apply, Pi.one_apply, norm_mul, Real.norm_norm]
          split_ifs <;> simp)
    · exact (X_integrable μ X hX_meas hX_ident hX_int (k+1)).norm
  -- Independence: E[‖X(k+1)‖ | ℱ_k] = E[‖X(k+1)‖] = E[‖X₀‖]
  have norm_indep : μ[‖X (k + 1)‖ | (ℱ μ X hX_meas) k] =ᵐ[μ] fun _ => μ[‖X (k + 1)‖] :=
    condExp_indep_eq (hX_meas (k+1)).measurable.comap_le (Filtration.le _ _)
      (measurable_norm.comp (comap_measurable (X (k+1)))).stronglyMeasurable
      (hX_indep.indep_comap_natural_of_lt hX_meas (Nat.lt_succ_self k))
  have norm_ident : μ[‖X (k + 1)‖] = ∫ ω, ‖X 0 ω‖ ∂μ :=
    ((hX_ident (k+1)).comp measurable_norm).integral_eq
  -- Combine
  have condexp_eq : μ[fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * ‖X (k + 1) ω‖ |
        (ℱ μ X hX_meas) k] =ᵐ[μ]
      fun ω => Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * ∫ ω, ‖X 0 ω‖ ∂μ := by
    filter_upwards [pullout, norm_indep] with ω h1 h2
    rw [h1, h2, norm_ident]
  rw [tower, integral_congr_ae condexp_eq, integral_mul_const]
  ring_nf
  rw [mul_comm, ← measureReal_def]
  congr 1
  rw [integral_indicator ((ℱ μ X hX_meas).le k (stopping_gt_measurable μ X hX_meas τ hτ k))]
  simp [integral_const]

/-- **Fubini-Tonelli for stopped sums** -/
theorem integral_sum_range_eq_tsum
    (τ : Ω → ℕ) (hτ : IsStoppingTime (ℱ μ X hX_meas) τ)
    (hτ_meas : Measurable τ) (hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ)
    [SigmaFiniteFiltration μ (ℱ μ X hX_meas)] :
    ∫ ω, ∑ k in Finset.range (τ ω), X (k + 1) ω ∂μ =
      ∑' k : ℕ, ∫ ω, Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * X (k + 1) ω ∂μ := by
  -- Rewrite stopped sum as tsum of indicator terms (pointwise)
  have sum_eq : ∀ ω, ∑ k in Finset.range (τ ω), X (k + 1) ω =
      ∑' k : ℕ, Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω * X (k + 1) ω := fun ω => by
    rw [tsum_eq_sum (s := Finset.range (τ ω))]
    · apply Finset.sum_congr rfl; intro k hk
      rw [Set.indicator_of_mem (Finset.mem_range.mp hk), Pi.one_apply, one_mul]
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [Set.indicator_of_not_mem (not_lt.mpr hk), Pi.zero_apply, zero_mul]
  -- LHS = ∫ ∑' indicator * X
  rw [integral_congr_ae (ae_of_all μ sum_eq)]
  -- Summability of norm integrals: ∑ E[‖F k‖] ≤ E[‖X₀‖] · E[τ] < ∞
  have hτ_ne_top : ∑' k : ℕ, μ {ω | k < τ ω} ≠ ∞ := by
    rw [← lintegral_nat_eq_tsum_prob μ τ hτ_meas]
    simp_rw [show ∀ ω, (τ ω : ℝ≥0∞) = ‖(τ ω : ℝ)‖ₑ from fun ω => (enorm_natCast (τ ω)).symm]
    exact hτ_int.hasFiniteIntegral.ne
  have norm_sum : Summable fun k => ∫ ω, ‖Set.indicator {ω' | k < τ ω'} (1 : Ω → ℝ) ω *
      X (k + 1) ω‖ ∂μ := by
    have norm_bound := fun k => integral_indicator_norm_eq μ X hX_meas hX_indep hX_ident hX_int
        τ hτ k
    simp_rw [norm_bound]
    exact (ENNReal.summable_toReal hτ_ne_top).mul_left _
  -- Apply Fubini: ∫ ∑' F = ∑' ∫ F
  exact (integral_tsum_of_summable_integral_norm
    (fun k => (X_integrable μ X hX_meas hX_ident hX_int (k+1)).mono
      (((indicator_gt_sm μ X hX_meas τ hτ k).mono (Filtration.le _ _)).aestronglyMeasurable.mul
        (hX_meas (k+1)).aestronglyMeasurable)
      (ae_of_all μ fun ω => by
        simp only [Set.indicator_apply, Pi.one_apply, norm_mul]
        split_ifs <;> simp))
    norm_sum).symm

/-! ### Wald's Identity -/

/-- **Wald's Identity**

    For i.i.d. integrable random variables X₀, X₁, ... with mean e = E[X₀],
    and a ℕ-valued stopping time τ (w.r.t. the natural filtration) with E[τ] < ∞:

        E[X₁ + X₂ + ... + X_τ] = e · E[τ]

    In Lean notation: E[∑_{k < τ} X(k+1)] = E[X 0] · E[τ].

    Note: We sum X₁, X₂, ..., X_τ (i.e., X(k+1) for k < τ), NOT X₀, X₁, ..., X_{τ-1}.
    This is the natural formulation where X_{k+1} is independent of {τ > k} ∈ ℱ_k. -/
theorem wald_identity
    (τ : Ω → ℕ) (hτ : IsStoppingTime (ℱ μ X hX_meas) τ)
    (hτ_meas : Measurable τ) (hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ)
    [SigmaFiniteFiltration μ (ℱ μ X hX_meas)] :
    ∫ ω, ∑ k in Finset.range (τ ω), X (k + 1) ω ∂μ =
      (∫ ω, X 0 ω ∂μ) * ∫ ω, (τ ω : ℝ) ∂μ := by
  -- Step 1: Exchange sum and integral (Fubini)
  rw [integral_sum_range_eq_tsum μ X hX_meas hX_indep hτ hτ_meas hτ_int]
  -- Step 2: Apply independence for each k
  simp_rw [integral_indicator_prod_eq μ X hX_meas hX_indep hX_ident hX_int τ hτ]
  -- Step 3: Factor out E[X 0]
  rw [← tsum_mul_left]
  -- Step 4: Apply tail sum formula
  congr 1
  rw [integral_tau_eq_tsum_prob μ τ hτ_meas hτ_int]

/-! ### Corollary: Wald's Identity for Uniformly Bounded Stopping Times -/

/-- **Wald's Identity — Bounded Case**

    Special case of Wald's Identity where τ ≤ N a.s. (deterministically bounded).
    In this case, the Fubini step reduces to a finite sum. -/
theorem wald_identity_bounded
    (τ : Ω → ℕ) (hτ : IsStoppingTime (ℱ μ X hX_meas) τ) (N : ℕ) (hτN : ∀ ω, τ ω ≤ N)
    [SigmaFiniteFiltration μ (ℱ μ X hX_meas)] :
    ∫ ω, ∑ k in Finset.range (τ ω), X (k + 1) ω ∂μ =
      (∫ ω, X 0 ω ∂μ) * ∫ ω, (τ ω : ℝ) ∂μ := by
  -- For bounded τ, use finite Fubini
  have hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ := by
    apply Integrable.mono' (integrable_const (N : ℝ))
    · exact Measurable.aestronglyMeasurable (measurable_natCast.comp
        (IsStoppingTime.measurable hτ))
    · filter_upwards with ω
      simp only [Real.norm_natCast, norm_natCast]
      exact Nat.cast_le.mpr (hτN ω)
  have hτ_meas : Measurable τ := IsStoppingTime.measurable hτ
  exact wald_identity μ X hX_meas hX_indep hX_ident hX_int τ hτ hτ_meas hτ_int

/-! ### Connections to Fair Games Theory -/

/-- **Wald's Identity applied to the Gambler's Ruin**

    For the Gambler's Ruin with i.i.d. fair coin flips X_k ∈ {+1, -1} (mean = 0),
    and stopping time τ = first time the fortune hits 0 or M, Wald's identity gives:
    E[X₁ + ... + X_τ] = 0 · E[τ] = 0.

    This is consistent with: E[fortune at τ] = E[fortune at 0] (by OST),
    which gives: 0 · P(ruin) + M · P(win) = initial fortune.

    Wald's identity provides the complementary computation for the *total drift*
    (sum of all steps), not just the terminal fortune. -/
theorem wald_zero_mean_gives_zero_drift
    (τ : Ω → ℕ) (hτ : IsStoppingTime (ℱ μ X hX_meas) τ)
    (hτ_meas : Measurable τ) (hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ)
    (h_zero_mean : ∫ ω, X 0 ω ∂μ = 0)
    [SigmaFiniteFiltration μ (ℱ μ X hX_meas)] :
    ∫ ω, ∑ k in Finset.range (τ ω), X (k + 1) ω ∂μ = 0 := by
  rw [wald_identity μ X hX_meas hX_indep hX_ident hX_int τ hτ hτ_meas hτ_int]
  rw [h_zero_mean, zero_mul]

end WaldIdentity

end
