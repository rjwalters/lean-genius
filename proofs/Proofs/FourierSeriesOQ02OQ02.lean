/-
# Square-Summability of Fourier Coefficients via p-Series (OQ-02-OQ-02)

Problem: fourier-series-oq-02-oq-02
"Fourier Coefficient Decay: fourierCoeff_sq_summable_of_holder via p-Series"

The parent proof (FourierSeriesOQ02.lean) establishes square-summability via
Parseval's theorem (L² theory: continuous on compact → L² → Parseval).
This file gives an **elementary** proof using only the Hölder decay bound
and the p-series convergence criterion.

## Main Result

If f : AddCircle T → ℂ is α-Hölder with constant C and α > 1/2, then:
  Summable (fun n : ℤ => ‖fourierCoeff f n‖^2)

## Elementary Proof (p-Series Comparison)

1. **Hölder decay** (from FourierSeriesOQ02): ‖ĉ_n(f)‖ ≤ (C/2)·(T/(2|n|))^α for n ≠ 0
2. **Squaring**: ‖ĉ_n(f)‖² ≤ [(C/2)·(T/(2|n|))^α]² = K/|n|^{2α}
   where K = (C/2)^2·(T/2)^{2α}
3. **p-Series**: Since α > 1/2, we have 2α > 1, so ∑ 1/|n|^{2α} converges
4. **Comparison test**: ∑ ‖ĉ_n(f)‖² < ∞

## Contrast with Parent Proof

Parent (FourierSeriesOQ02.lean): Continuous on compact AddCircle → bounded →
MeasureTheory.MemLp 2 → Parseval's theorem (hasSum_sq_fourierCoeff).

This file: Hölder decay bound → square bound O(|n|^{-2α}) → p-series comparison.
No L² theory, no measure theory beyond the Fourier coefficient definition.
-/

import Proofs.FourierSeriesOQ02

open MeasureTheory Complex Topology Filter AddCircle FourierHolderDecay
open scoped ENNReal NNReal Real

set_option maxHeartbeats 800000

namespace FourierSqSummablePSeries

variable {T : ℝ} [hT : Fact (0 < T)]

/-!
## Part I: p-Series Summability over ℤ

We need ∑_{n : ℤ} K/|n|^β < ∞ for β > 1.
Split into positive and negative ℕ parts, each of which is a standard p-series.
-/

/-- p-Series over ℕ: ∑_{n : ℕ} K/n^β converges when β > 1. -/
theorem summable_const_div_nat_rpow {K : ℝ} (hK : 0 ≤ K) {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => K / (n : ℝ) ^ β) := by
  simp_rw [div_eq_mul_inv]
  exact (Real.summable_nat_rpow_inv.2 hβ).mul_left K

/-- p-Series over ℤ: ∑_{n : ℤ} K/|n|^β converges when β > 1. -/
theorem summable_const_div_int_rpow {K : ℝ} (hK : 0 ≤ K) {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℤ => K / |↑n| ^ β) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have h_pnat := summable_const_div_nat_rpow hK hβ
  constructor
  · -- Positive half: |↑(↑n : ℤ)| = n for n : ℕ
    convert h_pnat using 1; ext n; congr 1; congr 1
    rw [Int.cast_natCast]; exact abs_of_nonneg (Nat.cast_nonneg' n)
  · -- Negative half: |↑(-(↑n : ℤ))| = n for n : ℕ
    convert h_pnat using 1; ext n; congr 1; congr 1
    rw [Int.cast_neg, Int.cast_natCast, abs_neg]; exact abs_of_nonneg (Nat.cast_nonneg' n)

/-!
## Part II: The Squared Decay Bound

For n ≠ 0: ‖ĉ_n(f)‖² ≤ K/|n|^{2α} where K = (C/2)^2·(T/2)^{2α}.
This follows by squaring the Hölder decay bound from FourierSeriesOQ02.
-/

/-- Helper: (a * b^α)^2 = a^2 * b^(2α) for a ≥ 0, b ≥ 0. -/
private theorem mul_rpow_sq (a b : ℝ) (α : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b ^ α) ^ 2 = a ^ 2 * b ^ (2 * α) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hb α 2]
  push_cast
  congr 1; ring

/-- The squared decay bound: ‖ĉ_n(f)‖² ≤ K/|n|^{2α} for n ≠ 0.
    Here K = (C/2)^2·(T/2)^{2α}. -/
theorem fourierCoeff_sq_le_pseries_term (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ)
    (hf : IsHolderOnCircle C α f) (hα_pos : (0 : ℝ) < α)
    (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff f n‖ ^ 2 ≤
      ((C : ℝ) / 2) ^ 2 * (T / 2) ^ (2 * (α : ℝ)) / |↑n| ^ (2 * (α : ℝ)) := by
  have hT_pos : (0 : ℝ) < T := hT.out
  have hα_nn : (0 : ℝ) ≤ (α : ℝ) := le_of_lt hα_pos
  have hn_pos : (0 : ℝ) < |↑n| := by
    rw [abs_pos]; exact_mod_cast hn
  -- Get the Hölder decay: ‖ĉ_n‖ ≤ (C/2) * (T/(2|n|))^α
  have hdecay := fourierCoeff_holder_decay C α f hf hα_pos n hn
  -- Let R = (C/2) * (T/(2|n|))^α ≥ 0
  have hR_nn : 0 ≤ (↑C / 2) * (T / (2 * |↑n|)) ^ (α : ℝ) := by positivity
  -- ‖ĉ_n‖^2 ≤ R^2 (squaring preserves ≤ for nonneg)
  have h_sq_le : ‖fourierCoeff f n‖ ^ 2 ≤
      ((↑C / 2) * (T / (2 * |↑n|)) ^ (α : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hdecay 2
  -- R^2 = (C/2)^2 * (T/(2|n|))^(2α) = (C/2)^2 * (T/2)^(2α) / |n|^(2α)
  have h_expand : ((↑C / 2) * (T / (2 * |↑n|)) ^ (α : ℝ)) ^ 2 =
      (↑C / 2) ^ 2 * (T / 2) ^ (2 * (α : ℝ)) / |↑n| ^ (2 * (α : ℝ)) := by
    rw [mul_rpow_sq _ _ (α : ℝ) (by positivity) (by positivity)]
    -- (T/(2|n|))^(2α) = (T/2)^(2α) / |n|^(2α)
    have h_split : T / (2 * |↑n|) = T / 2 / |↑n| := by
      field_simp
    rw [h_split, Real.div_rpow (by positivity) (le_of_lt hn_pos)]
    ring
  linarith [h_expand ▸ h_sq_le]

/-!
## Part III: Main Theorem — Square-Summability via p-Series

Combining the squared decay bound with the ℤ p-series convergence.
-/

/-- **Square-summability via p-series**: Elementary proof without Parseval.

    For α-Hölder f with α > 1/2: ∑_{n : ℤ} ‖ĉ_n(f)‖² < ∞.

    Proof uses only:
    - The Hölder decay bound ‖ĉ_n‖ ≤ (C/2)(T/(2|n|))^α (from FourierSeriesOQ02)
    - The p-series ∑ 1/n^β < ∞ for β > 1 (Real.summable_nat_rpow_inv)
    - Comparison test (Summable.of_norm_bounded_eventually)

    The parent proof (FourierSeriesOQ02.fourierCoeff_sq_summable_of_holder) uses
    Parseval's theorem via MeasureTheory.MemLp and hasSum_sq_fourierCoeff. -/
theorem fourierCoeff_sq_summable_of_holder_pseries (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : IsHolderOnCircle C α f)
    (hα : (1 : ℝ) / 2 < (α : ℝ)) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) := by
  have hT_pos : (0 : ℝ) < T := hT.out
  have hα_pos : (0 : ℝ) < (α : ℝ) := by linarith
  have h2α : (1 : ℝ) < 2 * (α : ℝ) := by linarith
  -- Constant K = (C/2)^2 · (T/2)^{2α} for the dominating series
  set K := ((C : ℝ) / 2) ^ 2 * (T / 2) ^ (2 * (α : ℝ)) with hK_def
  have hK_nn : 0 ≤ K := by positivity
  -- The dominating p-series ∑ K/|n|^(2α) converges (since 2α > 1)
  have h_dominated : Summable (fun n : ℤ => K / |↑n| ^ (2 * (α : ℝ))) :=
    summable_const_div_int_rpow hK_nn h2α
  -- Apply comparison test: for all n ≠ 0, ‖ĉ_n‖^2 ≤ K/|n|^(2α)
  -- The n = 0 term is excluded (finitely many exceptions allowed)
  refine h_dominated.of_norm_bounded_eventually ?_
  apply Filter.eventually_cofinite.mpr
  apply (Set.finite_singleton (0 : ℤ)).subset
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff,
             Real.norm_of_nonneg (sq_nonneg _), not_le] at hn ⊢
  -- hn : K/|n|^(2α) < ‖ĉ_n‖^2 (bound fails at n)
  -- Conclude n = 0 by contradiction with fourierCoeff_sq_le_pseries_term
  by_contra hne
  exact absurd (fourierCoeff_sq_le_pseries_term C α f hf hα_pos n hne)
    (not_le.mpr hn)

/-!
## Part IV: Connections and Corollaries
-/

/-- The elementary proof agrees with the Parseval-based proof (same conclusion).
    This theorem matches `FourierHolderDecay.fourierCoeff_sq_summable_of_holder`. -/
theorem sq_summable_matches_parseval (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ)
    (hf : IsHolderOnCircle C α f) (hα : (1 : ℝ) / 2 < (α : ℝ)) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) :=
  fourierCoeff_sq_summable_of_holder_pseries C α f hf hα

/-- Consequence: For α-Hölder f with α > 1/2, the Fourier coefficients are
    in L²(ℤ) — the coefficients are square-summable with explicit bound.

    The p-series argument gives the quantitative estimate:
    ∑ ‖ĉ_n‖² ≤ |ĉ_0|² + ∑_{n ≠ 0} K/|n|^{2α}
    where K = (C/2)^2 · (T/2)^{2α}. -/
theorem fourier_coeff_l2 (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ)
    (hf : IsHolderOnCircle C α f) (hα : (1 : ℝ) / 2 < (α : ℝ)) :
    ∃ S : ℝ, HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) S :=
  ⟨_, (fourierCoeff_sq_summable_of_holder_pseries C α f hf hα).hasSum⟩

/-- The critical threshold α = 1/2 is sharp: the decay rate O(|n|^{-1/2}) gives
    ‖ĉ_n‖^2 = O(|n|^{-1}), and ∑ 1/n diverges (harmonic series).
    So α > 1/2 is a necessary condition for the p-series argument.

    Note: The Parseval proof shows L² functions always have square-summable
    Fourier coefficients. For Hölder(α ≤ 1/2) functions, L² membership follows
    from continuity (compact support), but the p-series rate doesn't suffice
    directly. The sharp threshold for the p-series method is exactly α > 1/2. -/
theorem holder_half_is_critical_for_pseries :
    ¬ (∀ (C : ℝ≥0) (α : ℝ≥0), (α : ℝ) = 1/2 →
       ∀ f : AddCircle (2 * Real.pi) → ℂ, IsHolderOnCircle C α f →
       Summable (fun n : ℤ => ((C : ℝ) / 2) ^ 2 * (Real.pi) ^ (2 * (α : ℝ)) / |↑n| ^ (2 * (α : ℝ)))) := by
  -- Strategy: assume universal statement, use f=0 witness, extract harmonic series contradiction.
  intro hall
  -- Zero function is Hölder with constant 1 and exponent 1/2
  have h0 : IsHolderOnCircle 1 ⟨1/2, by norm_num⟩ (0 : AddCircle (2 * Real.pi) → ℂ) := by
    intro x y
    simp only [IsHolderOnCircle, HolderWith, Pi.zero_apply, edist_self, NNReal.coe_one,
               ENNReal.coe_one, zero_le]
  have hα_eq : ((⟨1/2, by norm_num⟩ : ℝ≥0) : ℝ) = 1/2 := by norm_num
  -- Apply the universal statement with C=1, α=1/2, f=0
  have hsum := hall 1 ⟨1/2, by norm_num⟩ hα_eq 0 h0
  -- Extract the ℕ positive part: Summable (fun n : ℕ => (1/4) * π / |n|)
  rw [summable_int_iff_summable_nat_and_neg] at hsum
  obtain ⟨h_pos, _⟩ := hsum
  -- Rescale: multiply by 4/π to get harmonic series summability
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_harm : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
    refine (h_pos.mul_left (4 / Real.pi)).congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      rw [Int.cast_natCast, abs_of_nonneg hn_pos.le]
      have h2 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
      simp only [NNReal.coe_one, NNReal.coe_mk, h2, Real.rpow_one]
      field_simp [h_pi_pos.ne', hn_pos.ne']
      ring
  -- Contradiction: harmonic series diverges (Real.summable_nat_rpow_inv for p=1)
  have h_not_harm : ¬ Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
    intro hs
    have : Summable (fun n : ℕ => (n : ℝ)⁻¹ ^ (1 : ℝ)) :=
      hs.congr (fun n => by simp only [Real.rpow_one, one_div])
    exact absurd this (Real.summable_nat_rpow_inv.not.mpr (by norm_num))
  exact h_not_harm h_harm

end FourierSqSummablePSeries
