/-
  Erdős Problem #673: Sum of Consecutive Divisor Ratios

  Source: https://erdosproblems.com/673
  Status: SOLVED

  Statement:
  Let 1 = d₁ < d₂ < ... < d_τ(n) = n be the divisors of n. Define
  G(n) = Σᵢ dᵢ/dᵢ₊₁ (sum over consecutive divisor ratios).

  Questions:
  1. Does G(n) → ∞ for almost all n? (YES - trivial)
  2. Asymptotic formula for Σ_{n≤X} G(n)?

  Known Results:
  - Tao: τ(n/m)/m ≤ G(n) ≤ τ(n) for any m | n
  - For even n: τ(n)/4 ≤ G(n) ≤ τ(n)
  - Erdős-Tenenbaum: G(n)/τ(n) has a continuous distribution function

  Tags: number-theory, divisors, analytic-number-theory
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic

namespace Erdos673

open Nat Finset Real Filter

/- ## Part I: Divisor Definitions -/

/-- The divisors of n as a sorted list. -/
noncomputable def sortedDivisors (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-- The number of divisors τ(n). -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- The i-th divisor of n (0-indexed from the sorted list). -/
noncomputable def divisorAt (n : ℕ) (i : ℕ) : ℕ :=
  (sortedDivisors n).getD i 0

/-- First divisor is 1 (for n ≥ 1). -/
theorem first_divisor_eq_one (n : ℕ) (hn : n ≥ 1) :
    divisorAt n 0 = 1 := by
  sorry

/-- Last divisor is n (for n ≥ 1). -/
theorem last_divisor_eq_n (n : ℕ) (hn : n ≥ 1) :
    divisorAt n (tau n - 1) = n := by
  sorry

/- ## Part II: The Function G(n) -/

/-- G(n) = sum of consecutive divisor ratios dᵢ/dᵢ₊₁. -/
noncomputable def G (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (tau n - 1),
    (divisorAt n i : ℝ) / (divisorAt n (i + 1) : ℝ)

/-- G(1) = 0 (no consecutive pairs). -/
theorem G_one : G 1 = 0 := by
  sorry

/-- G(p) = 1/p for prime p. -/
theorem G_prime (p : ℕ) (hp : p.Prime) : G p = 1 / p := by
  sorry

/-- G(p²) = 1/p + 1/p = 2/p for prime p. -/
theorem G_prime_sq (p : ℕ) (hp : p.Prime) : G (p ^ 2) = 2 / p := by
  sorry

/- ## Part III: Bounds on G(n) -/

/-- Upper bound: G(n) ≤ τ(n) - 1. -/
theorem G_upper_bound (n : ℕ) (hn : n ≥ 1) :
    G n ≤ tau n - 1 := by
  sorry

/-- Tao's upper bound: G(n) ≤ τ(n). -/
theorem tao_upper_bound (n : ℕ) (hn : n ≥ 1) :
    G n ≤ tau n := by
  sorry

/-- Tao's lower bound for m | n: G(n) ≥ τ(n/m)/m. -/
theorem tao_lower_bound (n m : ℕ) (hn : n ≥ 1) (hm : m ∣ n) (hm1 : m ≥ 1) :
    G n ≥ (tau (n / m) : ℝ) / m := by
  sorry

/-- For even n: G(n) ≥ τ(n)/4. -/
theorem G_even_lower_bound (n : ℕ) (hn : n ≥ 2) (heven : Even n) :
    G n ≥ (tau n : ℝ) / 4 := by
  sorry

/- ## Part IV: Asymptotic Behavior -/

/-- The average of G: (1/X) Σ_{n≤X} G(n) → ∞. -/
theorem average_G_tends_to_infinity :
    Tendsto (fun X : ℕ => (1 / X : ℝ) * ∑ n ∈ Finset.range X, G (n + 1))
      atTop atTop := by
  sorry

/-- G(n) → ∞ for almost all n (density 1). -/
def AlmostAllGToInfinity : Prop :=
  ∀ M : ℝ, Tendsto (fun X : ℕ =>
    ((Finset.range X).filter (fun n => G (n + 1) ≥ M)).card / X : ℕ → ℝ)
    atTop (𝓝 1)

/-- The first question is trivially true. -/
theorem first_question_trivial : AlmostAllGToInfinity := by
  sorry

/- ## Part V: Distribution of G(n)/τ(n) -/

/-- The ratio G(n)/τ(n). -/
noncomputable def GRatio (n : ℕ) : ℝ :=
  if tau n = 0 then 0 else G n / tau n

/-- GRatio is bounded: 0 ≤ G(n)/τ(n) ≤ 1 for n ≥ 1. -/
theorem GRatio_bounded (n : ℕ) (hn : n ≥ 1) :
    0 ≤ GRatio n ∧ GRatio n ≤ 1 := by
  sorry

/-- Erdős-Tenenbaum: G(n)/τ(n) has a continuous distribution function. -/
def HasContinuousDistribution : Prop :=
  ∃ F : ℝ → ℝ, Continuous F ∧
    (∀ t : ℝ, 0 ≤ F t ∧ F t ≤ 1) ∧
    (Tendsto F atBot (𝓝 0)) ∧
    (Tendsto F atTop (𝓝 1)) ∧
    ∀ t : ℝ, Tendsto (fun X : ℕ =>
      ((Finset.range X).filter (fun n => GRatio (n + 1) ≤ t)).card / X : ℕ → ℝ)
      atTop (𝓝 (F t))

/-- Erdős-Tenenbaum theorem on the distribution. -/
theorem erdos_tenenbaum_distribution : HasContinuousDistribution := by
  sorry

/- ## Part VI: Specific Values -/

/-- G(6) = 1/2 + 1/3 + 2/6 = 1/2 + 1/3 + 1/3 = 7/6.
    Divisors of 6: 1, 2, 3, 6. Ratios: 1/2, 2/3, 3/6. -/
theorem G_6 : G 6 = 1/2 + 2/3 + 1/2 := by
  sorry

/-- G(12) for divisors 1, 2, 3, 4, 6, 12. -/
theorem G_12 : G 12 = 1/2 + 2/3 + 3/4 + 4/6 + 6/12 := by
  sorry

/-- For highly composite numbers, G(n) is relatively large. -/
theorem highly_composite_G_large (n : ℕ) (hn : n ≥ 1)
    (hhc : ∀ m < n, tau m < tau n) :
    G n ≥ (tau n : ℝ) / 4 := by
  sorry

/- ## Part VII: Multiplicative Properties -/

/-- G is not multiplicative. -/
theorem G_not_multiplicative :
    ∃ a b : ℕ, Nat.Coprime a b ∧ a ≥ 2 ∧ b ≥ 2 ∧ G (a * b) ≠ G a * G b := by
  sorry

/-- For coprime m, n: relationship between G(mn), G(m), G(n). -/
theorem G_coprime_relation (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1)
    (hcop : Nat.Coprime m n) :
    G (m * n) ≥ G m + G n := by
  sorry

/- ## Part VIII: Asymptotic Formula -/

/-- The sum Σ_{n≤X} G(n) has order X log X. -/
theorem sum_G_asymptotic :
    ∃ c : ℝ, c > 0 ∧
      Tendsto (fun X : ℕ => (∑ n ∈ Finset.range X, G (n + 1)) / (X * Real.log X))
        atTop (𝓝 c) := by
  sorry

/-- More precise: Σ_{n≤X} G(n) ~ c X log X for some c. -/
def AsymptoticFormula : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∀ᶠ X in atTop,
    |((∑ n ∈ Finset.range X, G (n + 1)) : ℝ) - c * X * Real.log X| ≤ ε * X * Real.log X

/- ## Part IX: Connection to τ(n) -/

/-- The divisor function τ(n). -/
theorem tau_sum_asymptotic :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.range X, (tau (n + 1) : ℝ)) / (X * Real.log X))
      atTop (𝓝 1) := by
  sorry

/-- G(n) and τ(n) have similar average behavior. -/
theorem G_tau_similar_average :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ᶠ X in atTop,
        c₁ * (∑ n ∈ Finset.range X, (tau (n + 1) : ℝ)) ≤
        ∑ n ∈ Finset.range X, G (n + 1) ∧
        ∑ n ∈ Finset.range X, G (n + 1) ≤
        c₂ * (∑ n ∈ Finset.range X, (tau (n + 1) : ℝ)) := by
  sorry

end Erdos673

/-
  ## Summary

  This file formalizes Erdős Problem #673 on consecutive divisor ratios.

  **Status**: SOLVED

  **Definition**: G(n) = Σ dᵢ/dᵢ₊₁ where d₁ < d₂ < ... < d_τ(n) are divisors of n.

  **Questions**:
  1. Does G(n) → ∞ for almost all n? YES (trivial)
  2. Asymptotic formula for Σ_{n≤X} G(n)? Order X log X

  **Key Results**:
  - Tao: τ(n/m)/m ≤ G(n) ≤ τ(n) for any m | n
  - For even n: τ(n)/4 ≤ G(n) ≤ τ(n)
  - Erdős-Tenenbaum: G(n)/τ(n) has continuous distribution function

  **What we formalize**:
  1. Sorted divisors and divisorAt
  2. The function G(n) as sum of consecutive ratios
  3. Upper and lower bounds (Tao)
  4. Asymptotic behavior (average → ∞)
  5. Distribution of G(n)/τ(n) (Erdős-Tenenbaum)
  6. Specific values G(6), G(12)
  7. Non-multiplicativity
  8. Asymptotic formula ~ c X log X

  **Key sorries**:
  - `tao_lower_bound`, `tao_upper_bound`: Tao's bounds
  - `erdos_tenenbaum_distribution`: Distribution function result
  - `sum_G_asymptotic`: Asymptotic formula
-/
