import Mathlib

/-
# Fair Games Theorem OQ-03: Substantive Application Theorems

## The Open Question

The main FairGamesTheorem.lean file contains several application theorem stubs
that were left as trivial placeholders (`(1 : ℕ) + 1 = 2 := rfl`). Can these
be given substantive formalized proofs?

## Answer

This file provides rigorous proofs for each stub, with honest reporting of
what can be proved cleanly and what requires further API work.

## Technical Note on Mathlib 4.26.0 API

In Mathlib 4.26.0, `IsStoppingTime` was updated to use `τ : Ω → WithTop ι`
instead of `τ : Ω → ι`. All stopping time theorems in FairGamesTheorem.lean
(which use `τ : Ω → ℕ`) therefore have pre-existing build failures.

The theorems in this file that use the Optional Stopping Theorem directly
use `τ : Ω → ℕ∞` (the correct Mathlib 4.26.0 type) and `stoppedValue`.

Fully proved (4): gamblers_ruin_win_prob, gamblers_ruin_lose_prob,
  gamblers_ruin_probs_sum_one, submartingale_of_stoppedValue_mono_proved.
Pending API resolution (5): martingale_time_invariance,
  any_bounded_strategy_preserves_expectation, two_strategies_same_expectation,
  risk_neutral_pricing_neutrality, doobs_maximal_inequality.

Tags: probability, martingale, optional-stopping, gambling, doob
-/

noncomputable section

open MeasureTheory

namespace FairGamesOQ03

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: MARTINGALE EXPECTED VALUE TIME-INVARIANCE

Key insight: The constant function τ(ω) = n is a valid ℕ∞-stopping time.
The Optional Stopping Theorem gives E[f_τ] = E[f_0], i.e., E[f_n] = E[f_0].

Alternatively: from Martingale.setIntegral_eq with s = Set.univ, i = 0, j = n.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- For a martingale, the expected value is constant across time: E[f_n] = E[f_0].

    This is the fundamental property of fair games: no matter when you look at
    the process, the expected value hasn't changed from the start.

    Proof strategy: Apply Martingale.setIntegral_eq with s = Set.univ, then
    use setIntegral_univ. Requires SigmaFiniteFiltration, which holds for
    probability measures (IsFiniteMeasure instance). -/
theorem martingale_time_invariance
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ) (n : ℕ) :
    ∫ ω, f n ω ∂μ = ∫ ω, f 0 ω ∂μ := by
  -- Strategy: use setIntegral_eq with s = Set.univ
  -- hf.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ gives
  -- ∫ �� in Set.univ, f 0 ω ∂μ = ∫ ω in Set.univ, f n ω ∂μ
  -- then setIntegral_univ converts to full integrals
  have h := hf.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  exact h.symm

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: GAMBLER'S RUIN PROBABILITY FORMULA

Key insight: If a game is fair (E[final wealth] = E[initial wealth] = W₀)
and the only outcomes are "win" (wealth becomes W₀ + a) or "lose" (wealth
becomes 0), then the win probability p must satisfy:
  p · (W₀ + a) + (1-p) · 0 = W₀
  ⟹ p = W₀ / (W₀ + a)
═══════════════════════════════════════════════════════════════════════════════
-/

/-- In a two-outcome fair game with outcomes +a (win) and bankruptcy (wealth = 0),
    the probability of winning is W₀ / (W₀ + a).

    This is an algebraic consequence of E[final wealth] = E[initial wealth]:
    if a player starts with W₀ and can either reach W₀ + a (win probability p)
    or go bankrupt (probability 1 - p), fairness forces:
      p · (W₀ + a) = W₀
    hence p = W₀ / (W₀ + a). -/
theorem gamblers_ruin_win_prob
    (W₀ a : ℝ) (hW : 0 < W₀) (ha : 0 < a)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hfair : p * (W₀ + a) = W₀) :
    p = W₀ / (W₀ + a) := by
  have hWa : W₀ + a ≠ 0 := ne_of_gt (by linarith)
  rw [eq_div_iff hWa]
  linarith

/-- The complementary result: the probability of ruin (losing all wealth)
    is a / (W₀ + a). -/
theorem gamblers_ruin_lose_prob
    (W₀ a : ℝ) (hW : 0 < W₀) (ha : 0 < a)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hfair : p * (W₀ + a) = W₀) :
    1 - p = a / (W₀ + a) := by
  have hWa : W₀ + a ≠ 0 := ne_of_gt (by linarith)
  have hp_eq : p = W₀ / (W₀ + a) := gamblers_ruin_win_prob W₀ a hW ha p hp hp1 hfair
  rw [hp_eq]
  field_simp [hWa]
  ring

/-- Win and ruin probabilities sum to 1 (as expected). -/
theorem gamblers_ruin_probs_sum_one
    (W₀ a : ℝ) (hW : 0 < W₀) (ha : 0 < a)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hfair : p * (W₀ + a) = W₀) :
    p + (1 - p) = 1 := by ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: BETTING SYSTEMS FAIL (FORMAL VERSION)

The Optional Stopping Theorem directly implies that no stopping strategy can
improve expected returns in a fair game.

Note: In Mathlib 4.26.0, stopping times are `τ : Ω → ℕ∞` (WithTop ℕ),
and expected values via the stopping time use `stoppedValue f τ`.
��══════════════════════════════════════════════════════════════════════════════
-/

/-- No betting strategy in a fair game can improve the expected outcome.

    For any martingale f (fair game) and bounded ℕ∞-stopping time τ (valid
    strategy), E[stoppedValue f τ] = E[f_0].

    The proof uses Submartingale.expected_stoppedValue_mono for both the
    submartingale and supermartingale directions. The stoppedValue simplification
    uses WithTop.untopD simp lemmas.

    Status: pending resolution of untopA simp API in Mathlib 4.26.0. -/
theorem any_bounded_strategy_preserves_expectation
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ)
    (N : ℕ) (hτN : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, f 0 ω ∂μ := by
  sorry

/-- Between any two bounded ℕ∞-stopping times τ ≤ π, the expected value is unchanged.

    Status: pending same API resolution as any_bounded_strategy_preserves_expectation. -/
theorem two_strategies_same_expectation
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ)
    (τ π : Ω → ℕ∞)
    (hτ : IsStoppingTime ℱ τ)
    (hπ : IsStoppingTime ℱ π)
    (hτπ : τ ≤ π)
    (N : ℕ) (hπN : ∀ ω, π ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, stoppedValue f π ω ∂μ := by
  sorry

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: OPTION PRICING NEUTRALITY
═══════════════════════════════════════════════════════════════════════════════
-/

/-- Under a risk-neutral measure, any exercise strategy has the same expected payoff.

    Status: pending same API resolution as any_bounded_strategy_preserves_expectation. -/
theorem risk_neutral_pricing_neutrality
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ)
    (N : ℕ) (hτN : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, f 0 ω ∂μ := by
  sorry

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: SUBMARTINGALE CHARACTERIZATION (AXIOM ELIMINATION)

FairGamesTheorem.lean contains an axiom `submartingale_of_stoppedValue_mono`
which is the backward direction of Mathlib's
`submartingale_iff_expected_stoppedValue_mono`.

Here we prove this as a theorem, eliminating the axiom.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The converse of the Optional Stopping monotonicity characterization.

    A process is a submartingale if and only if stopped expectations are monotone.
    This is the backward (⟸) direction of Mathlib's
    `submartingale_iff_expected_stoppedValue_mono`:

    If E[f_τ] ≤ E[f_π] for all bounded ℕ∞-stopping times τ ≤ π,
    then f is a submartingale.

    Proof: direct one-line application of the Mathlib iff. -/
theorem submartingale_of_stoppedValue_mono_proved
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (f : ℕ → Ω → ℝ)
    (hadapt : Adapted ℱ f)
    (hint : ∀ n, Integrable (f n) μ)
    (h : ∀ (τ π : Ω → ℕ∞), IsStoppingTime ℱ τ →
      IsStoppingTime ℱ π →
      τ ≤ π → (∃ N : ℕ, ∀ ω, π ω ≤ N) →
        ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, stoppedValue f π ω ∂μ) :
    Submartingale f ℱ μ := by
  rw [submartingale_iff_expected_stoppedValue_mono hadapt hint]
  exact h

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: DOOB'S MAXIMAL INEQUALITY (STATEMENT)

Doob's maximal inequality bounds exceedance probabilities for submartingales:
  P(∃ n ≤ N, f_n ≥ thresh) ≤ E[f_N] / thresh

Mathlib's `maximal_ineq` in OptionalStopping.lean proves this using NNReal
thresholds. The statement below uses real-valued formulation.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- Doob's Maximal Inequality: for a non-negative submartingale,
    the probability of exceeding threshold `thresh` by time N is bounded by E[f_N]/thresh.

    P(∃ n ≤ N, f_n ≥ thresh) ≤ E[f_N] / thresh

    Status: pending identification of exact NNReal-to-real conversion of
    Mathlib's `maximal_ineq`. -/
theorem doobs_maximal_inequality
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (f : ℕ → Ω → ℝ)
    (hf : Submartingale f ℱ μ)
    (hpos : ∀ n, 0 ≤ f n)
    (N : ℕ) (thresh : ℝ) (hthresh : 0 < thresh) :
    thresh * (μ {ω | ∃ n ≤ N, thresh ≤ f n ω}).toReal ≤ ∫ ω, f N ω ∂μ := by
  sorry

end FairGamesOQ03

end -- noncomputable section

/-
## Summary

**Part I: Martingale Time Invariance** (proved via setIntegral_eq)
- `martingale_time_invariance`: E[f_n] = E[f_0] using Martingale.setIntegral_eq

**Part II: Gambler's Ruin Formula** (proved — pure algebra)
- `gamblers_ruin_win_prob`: P(win) = W₀/(W₀+a) from E[final] = E[initial]
- `gamblers_ruin_lose_prob`: P(lose) = a/(W₀+a)
- `gamblers_ruin_probs_sum_one`: P(win) + P(lose) = 1

**Part III: Betting Systems Fail** (sorry — pending stoppedValue/untopA API)
- `any_bounded_strategy_preserves_expectation`
- `two_strategies_same_expectation`

**Part IV: Option Pricing** (sorry — same pending API)
- `risk_neutral_pricing_neutrality`

**Part V: Submartingale Characterization** (proved — eliminates axiom)
- `submartingale_of_stoppedValue_mono_proved`: Backward direction of Mathlib iff

**Part VI: Doob's Maximal Inequality** (sorry — pending NNReal API conversion)
- `doobs_maximal_inequality`

**Status**: 5 proved + 4 sorry, 0 axioms

**Pre-existing issue**: FairGamesTheorem.lean has Mathlib 4.26.0 regressions:
`IsStoppingTime` API changed from `τ : Ω → ι` to `τ : Ω → WithTop ι`.
This file is standalone and does not depend on FairGamesTheorem.
-/
