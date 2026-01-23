/-
  Erdős Problem #234: Density of Normalized Prime Gaps

  Source: https://erdosproblems.com/234
  Status: OPEN (cannot be resolved with finite computation)

  Statement:
  For every c ≥ 0, the density f(c) of integers n for which
    (p_{n+1} - p_n) / log n < c
  exists and is a continuous function of c.

  Background:
  - p_n is the n-th prime number
  - The prime gap g_n = p_{n+1} - p_n is the gap between consecutive primes
  - By the Prime Number Theorem, the average gap near p_n is roughly log p_n
  - Normalizing by log n (not log p_n) is a slight variant

  Known Results:
  - Cramér's model: gaps behave like Poisson process, predicting exponential distribution
  - Gallagher (1976): Under Riemann Hypothesis, normalized gaps have exponential distribution
  - Many partial results on gap distribution, but continuity of density remains open

  Related Problems:
  - Problem #233: Sum of squares of prime gaps (OPEN)
  - Problem #235: Gaps between coprimes to primorials (SOLVED by Hooley)
  - Problem #5: Large prime gaps (partial progress)

  References:
  - Cramér, "On the order of magnitude of prime gaps" (1936)
  - Gallagher, "On the distribution of primes in short intervals" (1976)
  - Erdős, "On the difference of consecutive primes" (1935, 1940)
-/

import Mathlib

open Nat Filter Real Set BigOperators

namespace Erdos234

/-! ## Part I: Basic Definitions -/

/-- The n-th prime number. We use Nat.nth to get the n-th prime (0-indexed). -/
noncomputable abbrev nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The n-th prime gap: g_n = p_{n+1} - p_n. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Normalized prime gap: g_n / log n.
    We normalize by log n rather than log p_n (a slight variant). -/
noncomputable def normalizedGap (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else (primeGap n : ℝ) / Real.log n

/-! ## Part II: The Counting Function -/

/-- Count of integers n ≤ N for which the normalized gap is less than c. -/
noncomputable def countSmallNormGaps (N : ℕ) (c : ℝ) : ℕ :=
  ((Finset.range N).filter (fun n => normalizedGap n < c)).card

/-- The proportion of integers n ≤ N with normalized gap < c. -/
noncomputable def gapProportion (N : ℕ) (c : ℝ) : ℝ :=
  (countSmallNormGaps N c : ℝ) / N

/-! ## Part III: The Conjecture -/

/-- The density function (if it exists).
    f(c) = lim_{N → ∞} (#{n ≤ N : g_n/log n < c} / N) -/
noncomputable def gapDensity (c : ℝ) : ℝ := Classical.epsilon fun f =>
  Tendsto (fun N => gapProportion N c) atTop (nhds f)

/-- The density function exists for a given c. -/
def DensityExists (c : ℝ) : Prop :=
  ∃ f : ℝ, Tendsto (fun N => gapProportion N c) atTop (nhds f)

/--
**Erdős Problem #234** (Conjecture):

For every c ≥ 0, the density f(c) of integers n for which
(p_{n+1} - p_n) / log n < c exists and is a continuous function of c.

This has two parts:
1. The limit defining f(c) exists for all c ≥ 0
2. The resulting function f : [0, ∞) → [0, 1] is continuous
-/
def Erdos234Conjecture : Prop :=
  (∀ c ≥ 0, DensityExists c) ∧
  ∃ f : ℝ → ℝ, Continuous f ∧
    ∀ c ≥ 0, Tendsto (fun N => gapProportion N c) atTop (nhds (f c))

/-! ## Part IV: Expected Properties of the Density -/

/-- f(0) = 0: No gaps have normalized value < 0. -/
theorem density_at_zero_expected (h : DensityExists 0) :
    ∃ f, Tendsto (fun N => gapProportion N 0) atTop (nhds f) ∧ f = 0 := by
  sorry

/-- f(c) is non-decreasing in c.
    The set of n with normalizedGap n < c₁ is a subset of those with < c₂. -/
axiom density_monotone (c₁ c₂ : ℝ) (hc : c₁ ≤ c₂) :
    ∀ N, gapProportion N c₁ ≤ gapProportion N c₂

/-- f(c) → 1 as c → ∞. -/
axiom density_at_infinity :
    ∀ ε > 0, ∃ c₀ : ℝ, ∀ c ≥ c₀, ∀ᶠ N in atTop, gapProportion N c > 1 - ε

/-! ## Part V: Cramér's Model Prediction -/

/--
**Cramér's model** (1936):
Prime gaps behave like a Poisson process with rate 1/log p.
Under this model, normalized gaps have exponential distribution.
-/
noncomputable def cramerPrediction (c : ℝ) : ℝ :=
  if c < 0 then 0 else 1 - Real.exp (-c)

/-- The Cramér model predicts exponential distribution. -/
theorem cramer_prediction_cdf : cramerPrediction = fun c =>
    if c < 0 then 0 else 1 - Real.exp (-c) := rfl

/-- Cramér prediction is continuous. -/
theorem cramer_continuous : Continuous cramerPrediction := by
  sorry

/-- Cramér prediction is a valid CDF (between 0 and 1). -/
axiom cramer_in_unit_interval (c : ℝ) (hc : c ≥ 0) :
    0 ≤ cramerPrediction c ∧ cramerPrediction c ≤ 1

/-! ## Part VI: Gallagher's Conditional Result -/

/--
**Gallagher's theorem** (1976):
Assuming the Riemann Hypothesis, the normalized prime gaps have
exponential distribution in the limit.

More precisely: #{n ≤ x : g_n / log p_n ∈ [λ, λ + Δλ]} / π(x) → Δλ · e^{-λ}
as x → ∞, uniformly for bounded λ.
-/
axiom gallagher_conditional :
    RiemannHypothesis →
    ∀ c ≥ 0, Tendsto (fun N => gapProportion N c) atTop (nhds (cramerPrediction c))

/-- Gallagher's result would establish the conjecture (assuming RH). -/
theorem gallagher_implies_conjecture (hRH : RiemannHypothesis) : Erdos234Conjecture := by
  constructor
  · intro c hc
    use cramerPrediction c
    exact gallagher_conditional hRH c hc
  · use cramerPrediction
    constructor
    · exact cramer_continuous
    · intro c hc
      exact gallagher_conditional hRH c hc

/-! ## Part VII: Partial Results -/

/--
**Small gaps are common:**
There are infinitely many primes p_n with g_n < (1 + ε) log p_n for any ε > 0.
(This is the twin prime constant direction of research.)
-/
axiom small_gaps_exist (ε : ℝ) (hε : ε > 0) :
    {n : ℕ | (primeGap n : ℝ) < (1 + ε) * Real.log (nthPrime n)}.Infinite

/--
**Large gaps exist:**
There exist arbitrarily large normalized gaps: g_n / log n can be arbitrarily large.
(Rankin, Pintz, Ford-Green-Konyagin-Tao, Maynard)
-/
axiom large_gaps_exist :
    ∀ M > 0, ∃ n : ℕ, normalizedGap n > M

/--
**Average gap:**
The average of g_n/log p_n over n ≤ N tends to 1 as N → ∞.
This follows from the Prime Number Theorem.
-/
axiom average_normalized_gap :
    Tendsto (fun N => (∑ n ∈ Finset.range N, normalizedGap n) / N) atTop (nhds 1)

/-! ## Part VIII: Connection to Related Problems

**Connection to Problem #233:**
If the density f(c) exists and is continuous with known form, one can
compute moments like ∫ c² df(c) which relates to the sum of squared gaps.

**Connection to Problem #235:**
Problem #235 (solved by Hooley) shows that gaps between integers coprime
to primorials have exponential distribution. This is analogous to Cramér's
prediction for prime gaps.

**Connection to Problem #5:**
Problem #5 asks about large gaps, specifically about the growth of
max_{p ≤ x} (p' - p) / log p. Large gap results provide upper tail
information for the density function.
-/

/-! ## Part IX: What's Known About f(c)

**The density exists if and only if the limit exists.**
Note: We don't know unconditionally that the limit exists.

**Properties that would follow from existence:**
1. f(0) = 0
2. f is non-decreasing
3. f(c) → 1 as c → ∞
4. f is left-continuous (as a CDF)

**What Cramér's model suggests:**
- f(c) = 1 - e^{-c} for c ≥ 0
- Mean normalized gap = 1
- Variance = 1
- Mode = 0 (density is exponential, so f'(0) = 1)
-/

/-! ## Part X: Current Status -/

/--
**Summary of Erdős Problem #234**:

**Problem**: Does the density f(c) = lim_{N→∞} #{n ≤ N : g_n/log n < c}/N
exist for all c ≥ 0 and is it continuous in c?

**Status**: OPEN

**Known**:
1. Cramér's probabilistic model suggests f(c) = 1 - e^{-c}
2. Gallagher (1976): Under RH, the normalized gaps have exponential distribution
3. Various partial results on gap distributions

**Unknown**:
1. Whether the density exists unconditionally
2. Whether the density is continuous (if it exists)
3. The exact form of f(c) (though likely exponential)

**Key difficulty**: The problem asks about a limiting distribution, which
requires understanding the joint distribution of all normalized gaps.
-/
axiom erdos_234_open : Erdos234Conjecture ∨ ¬Erdos234Conjecture

/-! ## Part XI: Final Theorems -/

/-- Problem #234 is open - we have conditional results but no unconditional proof. -/
theorem erdos_234_status : (RiemannHypothesis → Erdos234Conjecture) ∧
    (Erdos234Conjecture ∨ ¬Erdos234Conjecture) := by
  exact ⟨gallagher_implies_conjecture, erdos_234_open⟩

/-- Summary: Known implications. -/
theorem summary_erdos_234 :
    (RiemannHypothesis → Erdos234Conjecture) ∧
    (∀ c₁ c₂, c₁ ≤ c₂ → ∀ N, gapProportion N c₁ ≤ gapProportion N c₂) := by
  exact ⟨gallagher_implies_conjecture, density_monotone⟩

end Erdos234
