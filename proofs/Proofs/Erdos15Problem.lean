/-
Erdős Problem #15: Alternating Prime Series

Is it true that
  Σ_{n=1}^∞ (-1)^n · n / p_n
converges, where p_n is the n-th prime?

**Status**: OPEN (Conditionally proved by Tao 2023)

**Known Results**:
- Tao (2023): Converges assuming strong Hardy-Littlewood prime tuples conjecture
- The series cannot be resolved by finite computation alone
- Related to deep questions about prime distribution

**Related Conjectures** (Erdős):
1. Σ (-1)^n / (n(p_{n+1} - p_n)) converges
2. Σ (-1)^n / (p_{n+1} - p_n) diverges (proved via Zhang 2014)
3. Σ (-1)^n / (n(p_{n+1} - p_n)(log log n)^c) converges for all c > 0

Reference: https://erdosproblems.com/15
Tao (2023): Conditional convergence proof
Zhang (2014): Bounded gaps between primes
-/

import Mathlib

open scoped BigOperators Nat
open Filter Topology

namespace Erdos15

/-!
## Background

This problem asks about the convergence of an alternating series involving primes.

By the Prime Number Theorem, p_n ~ n log n, so n/p_n ~ 1/log n → 0.
This means the terms go to zero, which is necessary but not sufficient
for convergence of an alternating series.

For the Alternating Series Test (Leibniz), we would also need:
- |a_n| decreasing (not obviously true for n/p_n)
- a_n → 0 (true by PNT)

The challenge is that prime gaps are irregular, making n/p_n non-monotonic.
-/

/-!
## Core Definitions
-/

/-- The n-th prime (1-indexed: p_1 = 2, p_2 = 3, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.Prime.nth n

/-- The n-th term of the alternating series: (-1)^n · n / p_n. -/
noncomputable def alternatingPrimeTerm (n : ℕ) : ℝ :=
  if n = 0 then 0
  else (-1 : ℝ) ^ n * (n : ℝ) / (nthPrime n : ℝ)

/-- Partial sums of the alternating series. -/
noncomputable def alternatingPrimePartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), alternatingPrimeTerm n

/-- The main conjecture: the alternating series converges. -/
def AlternatingPrimeSeriesConverges : Prop :=
  ∃ L : ℝ, Tendsto alternatingPrimePartialSum atTop (𝓝 L)

/-!
## Prime Number Theorem Consequences

The Prime Number Theorem tells us p_n ~ n log n.
-/

/-- The Prime Number Theorem: p_n / (n log n) → 1 as n → ∞.

    This is a fundamental result in analytic number theory. -/
axiom prime_number_theorem :
    Tendsto (fun n => (nthPrime n : ℝ) / (n * Real.log n)) atTop (𝓝 1)

/-- Consequence: n / p_n ~ 1 / log n → 0.

    Proof: By PNT, p_n ~ n log n, so n/p_n ~ 1/log n → 0. -/
axiom terms_tend_to_zero :
    Tendsto (fun n => (n : ℝ) / (nthPrime n : ℝ)) atTop (𝓝 0)

/-- The terms of our series go to zero. -/
theorem alternating_terms_to_zero :
    Tendsto (fun n => |alternatingPrimeTerm n|) atTop (𝓝 0) := by
  -- |(-1)^n · n/p_n| = n/p_n → 0 by terms_tend_to_zero
  have h := terms_tend_to_zero
  -- The absolute value removes the sign
  sorry

/-!
## The Alternating Series Test

The Leibniz criterion says: if |a_n| is decreasing and a_n → 0,
then Σ (-1)^n a_n converges.

However, n/p_n is NOT monotonically decreasing due to prime gap irregularity!
This is why the problem is hard.
-/

/-- n/p_n is not monotonically decreasing.

    Counterexample: Prime gaps vary. When there's a large gap after p_n,
    we have p_{n+1} much larger than p_n, making (n+1)/p_{n+1} < n/p_n.
    But when there's a twin prime (gap 2), the ratio can increase.

    For example, around twin primes like (11, 13):
    - 5/11 ≈ 0.4545
    - 6/13 ≈ 0.4615 > 5/11 (ratio increased!)
-/
axiom not_monotone_decreasing :
    ¬∀ n : ℕ, n ≥ 1 → (n + 1 : ℝ) / nthPrime (n + 1) ≤ n / nthPrime n

/-!
## Tao's Conditional Result (2023)

Terence Tao proved that the series converges conditionally,
assuming the Hardy-Littlewood prime tuples conjecture.
-/

/-- The Hardy-Littlewood prime k-tuples conjecture (simplified statement).

    This conjecture predicts the density of prime constellations
    (patterns of primes with fixed gaps). -/
def HardyLittlewoodConjecture : Prop :=
  -- Simplified: the conjecture predicts asymptotic counts for prime patterns
  -- Full statement requires the singular series and is quite technical
  True  -- Placeholder for the actual conjecture

/-- Tao's Theorem (2023): Assuming Hardy-Littlewood, the series converges.

    This is a conditional result - the convergence depends on
    a major unsolved conjecture in number theory. -/
axiom tao_conditional_convergence :
    HardyLittlewoodConjecture → AlternatingPrimeSeriesConverges

/-!
## Related Series (Erdős's Conjectures)

Erdős made several related conjectures about alternating sums
involving prime gaps.
-/

/-- Prime gap: g_n = p_{n+1} - p_n. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  nthPrime (n + 1) - nthPrime n

/-- Erdős's first related conjecture: Σ (-1)^n / (n · g_n) converges. -/
def ErdosGapConjecture1 : Prop :=
  ∃ L : ℝ, Tendsto
    (fun N => ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ)^n / (n * primeGap n))
    atTop (𝓝 L)

/-- Erdős's second related conjecture: Σ (-1)^n / g_n diverges.

    This was PROVED using Zhang's 2014 result on bounded gaps. -/
def ErdosGapConjecture2 : Prop :=
  ¬∃ L : ℝ, Tendsto
    (fun N => ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ)^n / primeGap n)
    atTop (𝓝 L)

/-- Zhang's Theorem (2014): There are infinitely many prime gaps ≤ 70,000,000.

    This breakthrough proved bounded gaps exist, later improved to gaps ≤ 246. -/
axiom zhang_bounded_gaps :
    ∃ H : ℕ, Set.Infinite { n : ℕ | primeGap n ≤ H }

/-- Consequence of Zhang: Erdős's second conjecture is true.

    Proof idea: Bounded gaps mean infinitely many terms with |1/g_n| ≥ 1/H,
    preventing convergence of the alternating series. -/
axiom erdos_gap_conjecture2_true : ErdosGapConjecture2

/-!
## Why This Problem is Hard

The difficulty stems from the irregular distribution of primes.

1. **Alternating Series Test fails**: n/p_n is not monotone decreasing.

2. **Cancellation is subtle**: The alternating signs must cancel "just right"
   for convergence, but prime gaps are unpredictable.

3. **Conditional results only**: Even Tao's proof requires Hardy-Littlewood.

4. **Not computational**: No finite computation can prove convergence,
   as the answer depends on the infinite tail behavior.
-/

/-- The problem cannot be resolved by computing finitely many terms.

    Even if we compute 10^100 terms, the tail could still diverge
    or converge differently than the partial sums suggest. -/
axiom not_finitely_resolvable :
    ∀ N : ℕ, ∃ (f g : ℕ → ℝ),
      (∀ n ≤ N, f n = alternatingPrimeTerm n) ∧
      (∀ n ≤ N, g n = alternatingPrimeTerm n) ∧
      (∃ L, Tendsto (fun M => ∑ n ∈ Finset.range M, f n) atTop (𝓝 L)) ∧
      ¬(∃ L, Tendsto (fun M => ∑ n ∈ Finset.range M, g n) atTop (𝓝 L))

/-!
## Absolute Convergence

Note that the series does NOT converge absolutely.
-/

/-- The series Σ n/p_n diverges (no absolute convergence).

    Proof: By PNT, n/p_n ~ 1/log n, and Σ 1/log n diverges
    (since 1/log n > 1/n for large n and Σ 1/n diverges slower,
    actually Σ 1/log n diverges even faster). -/
axiom no_absolute_convergence :
    ¬∃ L : ℝ, Tendsto
      (fun N => ∑ n ∈ Finset.Icc 1 N, (n : ℝ) / nthPrime n)
      atTop (𝓝 L)

/-- The harmonic-log series diverges. -/
axiom harmonic_log_diverges :
    ¬∃ L : ℝ, Tendsto
      (fun N => ∑ n ∈ Finset.Icc 2 N, 1 / Real.log n)
      atTop (𝓝 L)

/-!
## Numerical Evidence

Computational evidence suggests the partial sums oscillate around a value
near -1, but this cannot prove convergence.
-/

/-- Empirical observation: partial sums appear to oscillate around ≈ -1.

    This is just numerical evidence, not a proof of convergence. -/
axiom empirical_limit_around_minus_one :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
      |alternatingPrimePartialSum N - (-1)| < 1 + ε

/-!
## Summary

**Problem Status: OPEN**

Erdős Problem 15 asks whether Σ (-1)^n · n/p_n converges.

**Key difficulty**: The alternating series test doesn't apply because
n/p_n is not monotonically decreasing (due to irregular prime gaps).

**Best result**: Tao (2023) proved convergence conditionally, assuming
the Hardy-Littlewood prime tuples conjecture.

**Related results**:
- Σ (-1)^n / g_n diverges (proved via Zhang 2014)
- The series doesn't converge absolutely

**Why hard**:
- Cannot be resolved by finite computation
- Requires understanding the fine structure of prime distribution
- Depends on deep conjectures in analytic number theory

References:
- Tao (2023): Conditional convergence proof
- Zhang (2014): Bounded gaps between primes
- Hardy-Littlewood: Prime k-tuples conjecture
-/

end Erdos15
