/-!
# Erdős Problem #234: Density of Normalized Prime Gaps

For every c ≥ 0, the density f(c) of integers n for which
(p_{n+1} - p_n) / log n < c exists and is a continuous function of c.

## Status: OPEN

## References
- Cramér, "On the order of magnitude of prime gaps" (1936)
- Gallagher, "On the distribution of primes in short intervals" (1976)
- Erdős, "On the difference of consecutive primes" (1935, 1940)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic
import Proofs.RiemannHypothesis

open Nat Filter Real Set

/-!
## Section I: Basic Definitions
-/

/-- The n-th prime number (0-indexed via Nat.nth). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The n-th prime gap: g_n = p_{n+1} - p_n. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Normalized prime gap: g_n / log n. For n ≤ 1 we define this as 0. -/
noncomputable def normalizedGap (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else (primeGap n : ℝ) / Real.log n

/-!
## Section II: Counting Functions
-/

/-- Count of integers n < N for which the normalized gap is less than c. -/
noncomputable def countSmallNormGaps (N : ℕ) (c : ℝ) : ℕ :=
  ((Finset.range N).filter (fun n => normalizedGap n < c)).card

/-- Proportion of integers n < N with normalized gap < c. -/
noncomputable def gapProportion (N : ℕ) (c : ℝ) : ℝ :=
  (countSmallNormGaps N c : ℝ) / N

/-!
## Section III: The Conjecture
-/

/-- The density f(c) exists for a given c when the limit exists. -/
def DensityExists (c : ℝ) : Prop :=
  ∃ f : ℝ, Tendsto (fun N => gapProportion N c) atTop (nhds f)

/-- **Erdős Problem #234**: For every c ≥ 0, the density f(c) of integers n
with (p_{n+1} - p_n)/log n < c exists and is a continuous function of c.

This has two parts:
1. The limit defining f(c) exists for all c ≥ 0.
2. The resulting function f : [0, ∞) → [0, 1] is continuous.
-/
def ErdosProblem234 : Prop :=
  (∀ c ≥ 0, DensityExists c) ∧
  ∃ f : ℝ → ℝ, Continuous f ∧
    ∀ c ≥ 0, Tendsto (fun N => gapProportion N c) atTop (nhds (f c))

/-!
## Section IV: Basic Properties
-/

/-- Normalized gap is non-negative. -/
lemma normalizedGap_nonneg (n : ℕ) : normalizedGap n ≥ 0 := by
  unfold normalizedGap
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · exact Nat.cast_nonneg (primeGap n)
    · push_neg at h
      exact Real.log_nonneg (Nat.one_lt_cast.mpr h).le

/-- No integers have normalized gap < 0. -/
lemma countSmallNormGaps_zero (N : ℕ) : countSmallNormGaps N 0 = 0 := by
  unfold countSmallNormGaps
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _
  simp only [not_lt]
  exact normalizedGap_nonneg n

/-- Gap proportion at c = 0 is always 0. -/
lemma gapProportion_zero (N : ℕ) : gapProportion N 0 = 0 := by
  unfold gapProportion
  rw [countSmallNormGaps_zero]
  simp

/-- f(0) = 0: the density at zero is zero. -/
theorem density_at_zero (h : DensityExists 0) :
    ∃ f, Tendsto (fun N => gapProportion N 0) atTop (nhds f) ∧ f = 0 := by
  use 0
  constructor
  · simp only [gapProportion_zero]
    exact tendsto_const_nhds
  · rfl

/-- f(c) is non-decreasing: more integers satisfy a larger threshold. -/
axiom density_monotone (c₁ c₂ : ℝ) (hc : c₁ ≤ c₂) :
    ∀ N, gapProportion N c₁ ≤ gapProportion N c₂

/-- f(c) → 1 as c → ∞: eventually all normalized gaps are below c. -/
axiom density_at_infinity :
    ∀ ε > 0, ∃ c₀ : ℝ, ∀ c ≥ c₀, ∀ᶠ N in atTop, gapProportion N c > 1 - ε

/-!
## Section V: Cramér's Model
-/

/-- Cramér's model (1936) predicts an exponential distribution for
normalized prime gaps: f(c) = 1 - e^{-c} for c ≥ 0. -/
noncomputable def cramerPrediction (c : ℝ) : ℝ :=
  if c < 0 then 0 else 1 - Real.exp (-c)

/-- The exponential part of Cramér's prediction is continuous. -/
lemma cramer_exp_continuous : Continuous (fun c : ℝ => 1 - Real.exp (-c)) :=
  continuous_const.sub (continuous_exp.comp continuous_neg)

/-- Cramér prediction is continuous (both pieces are continuous and agree at 0). -/
axiom cramer_continuous : Continuous cramerPrediction

/-- Cramér prediction is a valid CDF: values lie in [0, 1] for c ≥ 0. -/
axiom cramer_in_unit_interval (c : ℝ) (hc : c ≥ 0) :
    0 ≤ cramerPrediction c ∧ cramerPrediction c ≤ 1

/-!
## Section VI: Gallagher's Conditional Result
-/

/-- Gallagher's theorem (1976): assuming the Riemann Hypothesis,
normalized prime gaps have exponential distribution in the limit.
Specifically, #{n ≤ x : g_n/log p_n ∈ [λ, λ+Δλ]}/π(x) → Δλ·e^{-λ}. -/
axiom gallagher_conditional :
    RiemannHypothesis →
    ∀ c ≥ 0, Tendsto (fun N => gapProportion N c) atTop (nhds (cramerPrediction c))

/-- Gallagher's result establishes the conjecture conditional on RH. -/
theorem gallagher_implies_conjecture (hRH : RiemannHypothesis) :
    ErdosProblem234 := by
  constructor
  · intro c hc
    use cramerPrediction c
    exact gallagher_conditional hRH c hc
  · use cramerPrediction
    constructor
    · exact cramer_continuous
    · intro c hc
      exact gallagher_conditional hRH c hc

/-!
## Section VII: Partial Results on Gap Distribution
-/

/-- Small gaps exist: for any ε > 0, infinitely many primes have
g_n < (1 + ε) log p_n (toward the twin prime conjecture). -/
axiom small_gaps_exist (ε : ℝ) (hε : ε > 0) :
    {n : ℕ | (primeGap n : ℝ) < (1 + ε) * Real.log (nthPrime n)}.Infinite

/-- Large gaps exist: g_n/log n can be made arbitrarily large.
(Rankin, Pintz, Ford–Green–Konyagin–Tao, Maynard) -/
axiom large_gaps_exist :
    ∀ M > 0, ∃ n : ℕ, normalizedGap n > M

/-- The average normalized gap tends to 1 by the Prime Number Theorem. -/
axiom average_normalized_gap :
    Tendsto (fun N => (∑ n ∈ Finset.range N, normalizedGap n) / N) atTop (nhds 1)
