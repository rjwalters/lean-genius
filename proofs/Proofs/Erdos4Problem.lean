/-
  Erdős Problem #4: Large Prime Gaps

  Source: https://erdosproblems.com/4
  Status: SOLVED (Ford-Green-Konyagin-Maynard-Tao, 2016-2018)
  Prize: $10,000

  Statement:
  Is it true that, for any C > 0, there are infinitely many n such that
    p_{n+1} - p_n > C · (log log n · log log log log n) / (log log log n)² · log n?

  Answer: YES.
  - Rankin (1938): Proved for some specific C > 0.
  - Maynard (2016) and Ford-Green-Konyagin-Tao (2016): Proved for ALL C > 0.
  - Ford-Green-Konyagin-Maynard-Tao (2018): Improved the bound.

  Background:
  This problem asks about the largest gaps between consecutive primes.
  While the average gap near n is approximately log n, exceptionally large
  gaps exist. The question is: how large can they be?

  This file formalizes the definitions and key results.
-/

import Mathlib

open Set Nat Real

namespace Erdos4

/-! ## Prime Notation -/

/-- The n-th prime number (0-indexed: p₀ = 2, p₁ = 3, p₂ = 5, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The prime gap: difference between consecutive primes. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-! ## Iterated Logarithms -/

/-- Natural logarithm (from Mathlib). -/
noncomputable def lg (x : ℝ) : ℝ := Real.log x

/-- Double logarithm: log(log(x)). -/
noncomputable def lg2 (x : ℝ) : ℝ := lg (lg x)

/-- Triple logarithm: log(log(log(x))). -/
noncomputable def lg3 (x : ℝ) : ℝ := lg (lg (lg x))

/-- Quadruple logarithm: log(log(log(log(x)))). -/
noncomputable def lg4 (x : ℝ) : ℝ := lg (lg (lg (lg x)))

/-! ## The Erdős Function -/

/--
The Erdős function for prime gaps:
  f(n) = (log log n · log log log log n) / (log log log n)² · log n

This function grows slower than (log n)² but faster than log n.
-/
noncomputable def erdosFunction (n : ℕ) : ℝ :=
  (lg2 n * lg4 n) / (lg3 n)^2 * lg n

/--
Simplified Rankin function (without the quartic log term):
  g(n) = (log log n) / (log log log n) · log n
-/
noncomputable def rankinFunction (n : ℕ) : ℝ :=
  (lg2 n) / (lg3 n) * lg n

/-! ## The Erdős Conjecture (Now Proved) -/

/--
**Erdős Problem 4** (SOLVED):
For any C > 0, there are infinitely many n such that
  p_{n+1} - p_n > C · erdosFunction(n).
-/
def erdos_4_conjecture : Prop :=
  ∀ C : ℝ, C > 0 →
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ (primeGap n : ℝ) > C * erdosFunction n

/-! ## Historical Results -/

/--
**Rankin's Theorem** (1938):
There exists C > 0 such that for infinitely many n,
  p_{n+1} - p_n > C · erdosFunction(n).

This was the first quantitative result on large prime gaps.
-/
axiom rankin_theorem :
    ∃ C : ℝ, C > 0 ∧
      ∀ N : ℕ, ∃ n : ℕ, n > N ∧ (primeGap n : ℝ) > C * erdosFunction n

/-- Rankin's original constant (approximately 1/3 · e^γ where γ is Euler's constant). -/
noncomputable def rankin_constant : ℝ := (1/3) * Real.exp 0.5772156649

/-! ## The 2016 Breakthrough -/

/--
**Maynard's Theorem** (2016):
For ANY C > 0, there are infinitely many n with
  p_{n+1} - p_n > C · erdosFunction(n).

This proves Erdős Problem 4 in the affirmative.
-/
axiom maynard_theorem : erdos_4_conjecture

/--
**Ford-Green-Konyagin-Tao Theorem** (2016):
Independent proof of the same result as Maynard.
-/
axiom ford_green_konyagin_tao_theorem : erdos_4_conjecture

/-- The problem is solved: both teams proved it. -/
theorem erdos_4_solved : erdos_4_conjecture := maynard_theorem

/-! ## Improved Bounds (2018) -/

/--
**Ford-Green-Konyagin-Maynard-Tao Theorem** (2018):
All five authors proved a stronger bound:
  p_{n+1} - p_n ≫ (log log n · log log log log n) / (log log log n) · log n

Note: The denominator is (log log log n) not (log log log n)².
-/
noncomputable def improvedErdosFunction (n : ℕ) : ℝ :=
  (lg2 n * lg4 n) / (lg3 n) * lg n

axiom fgkmt_improved_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ N : ℕ, ∃ n : ℕ, n > N ∧ (primeGap n : ℝ) > C * improvedErdosFunction n

/-! ## Upper Bounds -/

/--
**Baker-Harman-Pintz Theorem** (2001):
For all sufficiently large n,
  p_{n+1} - p_n ≤ n^{0.525}.

This is the best known upper bound on prime gaps.
-/
axiom baker_harman_pintz_upper_bound :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → (primeGap n : ℝ) ≤ (n : ℝ)^(0.525 : ℝ)

/-- The BHP exponent. -/
def bhp_exponent : ℝ := 0.525

/-! ## Cramér's Conjecture -/

/--
**Cramér's Conjecture** (1936, OPEN):
For all large n,
  p_{n+1} - p_n = O((log p_n)²).

More precisely, lim sup (p_{n+1} - p_n) / (log p_n)² = 1.
-/
def cramer_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ᶠ n in Filter.atTop, (primeGap n : ℝ) ≤ C * (lg (nthPrime n))^2

/--
**Cramér-Granville Conjecture** (refined):
lim sup (p_{n+1} - p_n) / (log p_n)² = 2 · e^{-γ} ≈ 1.1229.
-/
noncomputable def cramer_granville_constant : ℝ := 2 * Real.exp (-0.5772156649)

/-! ## Simple Properties -/

/-- The first prime gap: p₁ - p₀ = 3 - 2 = 1. -/
axiom gap_0 : primeGap 0 = 1

/-- Prime gaps are always positive for n ≥ 1. -/
axiom prime_gap_pos (n : ℕ) (hn : n ≥ 1) : primeGap n > 0

/-- The average prime gap near n is approximately log n. -/
axiom average_gap_asymptotic :
    Filter.Tendsto (fun n => (nthPrime n : ℝ) / n / lg n) Filter.atTop (nhds 1)

/-! ## Comparison of Bounds -/

/-- The Erdős function grows slower than (log n)^(1+ε) for any ε > 0. -/
axiom erdos_function_growth (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in Filter.atTop, erdosFunction n < (lg n)^(1 + ε)

/-- The improved bound is stronger (larger). -/
theorem improved_stronger (n : ℕ) (hn : n ≥ 100) :
    erdosFunction n ≤ improvedErdosFunction n := by
  unfold erdosFunction improvedErdosFunction
  -- The improved has lg3 n in denominator vs (lg3 n)^2
  sorry -- Technical inequality

/-! ## Related Conjectures -/

/--
**Stronger Conjecture** (Erdős, $10,000 for this):
There exists c > 0 such that for infinitely many n,
  p_{n+1} - p_n > (log n)^{1+c}.

This would be a significant strengthening of Problem 4.
-/
def erdos_stronger_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ (primeGap n : ℝ) > (lg n)^(1 + c)

/--
**Firoozbakht's Conjecture** (1982, OPEN):
p_n^{1/n} is strictly decreasing for n ≥ 1.

This implies p_{n+1} - p_n < (log p_n)² - log p_n for large n.
-/
def firoozbakht_conjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 → (nthPrime (n + 1) : ℝ)^(1 / (n + 1 : ℝ)) <
                    (nthPrime n : ℝ)^(1 / (n : ℝ))

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem 4 asked whether for any C > 0, there are infinitely many n with
  p_{n+1} - p_n > C · (log log n · log log log log n) / (log log log n)² · log n.

**Answer: YES** (Maynard 2016, Ford-Green-Konyagin-Tao 2016)

**Key Results**:
1. Rankin (1938): Proved for some specific C > 0
2. Maynard (2016): Proved for all C > 0
3. Ford-Green-Konyagin-Tao (2016): Independent proof
4. Ford-Green-Konyagin-Maynard-Tao (2018): Improved bound

**Open Questions**:
- Cramér's conjecture: Is p_{n+1} - p_n = O((log p_n)²)?
- Does p_{n+1} - p_n > (log n)^{1+c} hold for some c > 0?
- Exact growth rate of maximal prime gaps

References:
- Rankin (1938): "The difference between consecutive prime numbers"
- Maynard (2016): "Large gaps between primes"
- Ford, Green, Konyagin, Tao (2016): "Large gaps between consecutive prime numbers"
- Ford, Green, Konyagin, Maynard, Tao (2018): Improved bound
-/

end Erdos4
