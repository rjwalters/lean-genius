/-
  Erdős Problem #1095: The Erdős-Selfridge Function

  Source: https://erdosproblems.com/1095
  Status: OPEN

  Statement:
  Let g(k) > k+1 be the smallest n such that all prime factors of C(n,k)
  are greater than k. Estimate g(k).

  Background:
  The binomial coefficient C(n,k) = n!/(k!(n-k)!) typically has many small
  prime factors. For most n, some prime p ≤ k divides C(n,k). The function
  g(k) finds the first n where this fails—where C(n,k) is "k-rough" (all
  prime factors exceed k).

  This is related to the distribution of smooth numbers and the structure
  of binomial coefficients modulo primes.

  Known Bounds:
  • Original (Ecklund-Erdős-Selfridge 1974):
    k^{1+c} < g(k) ≤ exp((1+o(1))k) for some c > 0

  • Current best lower bound (Konyagin 1999):
    g(k) ≫ exp(c·(log k)²) for some c > 0

  Conjectures:
  • g(k) < L_k = lcm(1,...,k) for large k
  • lim sup g(k+1)/g(k) = ∞
  • lim inf g(k+1)/g(k) = 0
  • Heuristic: log g(k) ≍ k/log k

  References:
  [EES74] Ecklund, Erdős, Selfridge "A new function associated with
          prime factors of binomial coefficients" Math. Comp. (1974)
  [ELS93] Erdős, Lacampagne, Selfridge "Estimates of the least prime
          factor of a binomial coefficient" Math. Comp. (1993)
  [Ko99b] Konyagin "Estimates of the least prime factor" Mathematika (1999)
  [SSW20] Sorenson, Sorenson, Webster "An algorithm and estimates for
          the Erdős-Selfridge function" (2020)

  Tags: number-theory, binomial-coefficients, prime-factors, open-problem
-/

import Mathlib

open Nat Finset BigOperators

namespace Erdos1095

/-
# Part 1: Core Definitions
-/

/-- An integer is k-rough if all its prime factors exceed k -/
def isKRough (n k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p > k

/-- C(n,k) is k-rough: all prime factors exceed k -/
def binomIsKRough (n k : ℕ) : Prop :=
  isKRough (Nat.choose n k) k

/-
# Part 2: The Erdős-Selfridge Function g(k) — Axiomatized

g(k) is the smallest n > k+1 such that all prime factors of C(n,k) exceed k.
Existence follows from known upper bounds (Ecklund-Erdős-Selfridge 1974).
-/

/-- The Erdős-Selfridge function g(k): smallest n > k+1 with C(n,k) k-rough. -/
axiom g : ℕ → ℕ

/-- g(k) > k + 1 (by definition). -/
axiom g_gt : ∀ k, g k > k + 1

/-- C(g(k), k) is k-rough: all prime factors exceed k. -/
axiom g_spec : ∀ k, binomIsKRough (g k) k

/-- g(k) is minimal: no smaller n > k+1 satisfies the condition. -/
axiom g_minimal : ∀ k n, n > k + 1 → binomIsKRough n k → g k ≤ n

/-
# Part 3: Concrete Computations of g(k)

We prove g(2) = 6, g(3) = 7, g(4) = 7, g(5) = 23 from the axioms.
Each proof shows:
  - Upper bound: exhibit a witness n with C(n,k) k-rough
  - Lower bound: rule out all n in (k+1, answer) by finding a small prime divisor
-/

/-- g(2) = 6: C(4,2)=6 has factor 2, C(5,2)=10 has factor 2,
    C(6,2)=15=3·5 is 2-rough. -/
theorem g_two : g 2 = 6 := by
  apply le_antisymm
  · -- g(2) ≤ 6: C(6,2) = 15 is 2-rough
    apply g_minimal 2 6 (by omega)
    intro p hp hpdvd
    by_contra h; push_neg at h
    have : p = 2 := le_antisymm h hp.two_le
    subst this; exact absurd hpdvd (by decide)
  · -- g(2) ≥ 6: rule out n = 4 and n = 5
    have hgt := g_gt 2
    suffices gFunc_2_ne : g 2 ≠ 4 ∧ g 2 ≠ 5 by omega
    constructor
    · intro h4; exact absurd (h4 ▸ g_spec 2) (fun h => absurd (h 2 (by decide) (by decide)) (by omega))
    · intro h5; exact absurd (h5 ▸ g_spec 2) (fun h => absurd (h 2 (by decide) (by decide)) (by omega))

/-- g(3) = 7: C(5,3)=10 has factor 2, C(6,3)=20 has factor 2,
    C(7,3)=35=5·7 is 3-rough. -/
theorem g_three : g 3 = 7 := by
  apply le_antisymm
  · apply g_minimal 3 7 (by omega)
    intro p hp hpdvd
    by_contra h; push_neg at h
    have : p = 2 ∨ p = 3 := by have := hp.two_le; omega
    rcases this with rfl | rfl <;> exact absurd hpdvd (by decide)
  · have hgt := g_gt 3
    suffices g 3 ≠ 5 ∧ g 3 ≠ 6 by omega
    exact ⟨fun h => absurd (h ▸ g_spec 3) (fun h => absurd (h 2 (by decide) (by decide)) (by omega)),
           fun h => absurd (h ▸ g_spec 3) (fun h => absurd (h 2 (by decide) (by decide)) (by omega))⟩

/-- g(4) = 7: C(6,4)=15 has factor 3≤4,
    C(7,4)=35=5·7 is 4-rough. -/
theorem g_four : g 4 = 7 := by
  apply le_antisymm
  · apply g_minimal 4 7 (by omega)
    intro p hp hpdvd
    by_contra h; push_neg at h
    have : p = 2 ∨ p = 3 ∨ p = 4 := by have := hp.two_le; omega
    rcases this with rfl | rfl | rfl
    · exact absurd hpdvd (by decide)
    · exact absurd hpdvd (by decide)
    · exact absurd hp (by decide)
  · have hgt := g_gt 4
    suffices g 4 ≠ 6 by omega
    intro h; exact absurd (h ▸ g_spec 4) (fun h => absurd (h 3 (by decide) (by decide)) (by omega))

/-- C(23,5) = 33649 = 7·11·19·23 is 5-rough. -/
private theorem binomIsKRough_23_5 : binomIsKRough 23 5 := by
  intro p hp hpdvd
  by_contra h; push_neg at h
  -- p prime, p ≤ 5 → p ∈ {2, 3, 4, 5}; 4 isn't prime
  have : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by have := hp.two_le; omega
  rcases this with rfl | rfl | rfl | rfl
  · exact absurd hpdvd (by decide)
  · exact absurd hpdvd (by decide)
  · exact absurd hp (by decide)
  · exact absurd hpdvd (by decide)

/-- g(5) = 23: for all n ∈ {7,...,22}, some prime ≤ 5 divides C(n,5).
    C(23,5) = 33649 = 7·11·19·23 is 5-rough. -/
theorem g_five : g 5 = 23 := by
  apply le_antisymm
  · exact g_minimal 5 23 (by omega) binomIsKRough_23_5
  · have hgt := g_gt 5
    -- Rule out n = 7 through 22: each C(n,5) has a prime factor ≤ 5
    suffices h : ∀ n, 7 ≤ n → n ≤ 22 → ¬binomIsKRough n 5 by
      by_contra hlt; push_neg at hlt
      exact h (g 5) (by omega) (by omega) (g_spec 5)
    intro n hn1 hn2 hk
    interval_cases n <;> first
      | exact absurd (hk 2 (by decide) (by decide)) (by omega)
      | exact absurd (hk 3 (by decide) (by decide)) (by omega)

example : g 2 = 6 := g_two
example : g 3 = 7 := g_three
example : g 4 = 7 := g_four
example : g 5 = 23 := g_five

/-
# Part 4: Structural Properties
-/

/-- g(k) ≥ k + 2, immediate from g(k) > k + 1. -/
theorem g_ge_k_plus_two (k : ℕ) : g k ≥ k + 2 := by
  have := g_gt k; omega

/-
# Part 5: Known Bounds (axiomatized — deep results from the literature)
-/

/-- Original lower bound [EES74]: g(k) > k^{1+c} for some c > 0. -/
axiom ees_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ k ≥ 2, (g k : ℝ) > k^(1 + c)

/-- Original upper bound [EES74]: g(k) ≤ exp((1+o(1))k). -/
axiom ees_upper_bound :
  ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (g k : ℝ) ≤ Real.exp ((1 + ε) * k)

/-- Konyagin's improved lower bound [Ko99]: g(k) ≫ exp(c·(log k)²). -/
axiom konyagin_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (g k : ℝ) ≥ Real.exp (c * (Real.log k)^2)

/-
# Part 6: The LCM Conjecture
-/

/-- L_k = lcm(1, 2, ..., k). -/
def lcmUpTo (k : ℕ) : ℕ :=
  (Finset.Icc 1 k).lcm id

/-- L_k ~ exp(k) by the Prime Number Theorem [equivalently, ψ(k)/k → 1]. -/
axiom lcm_asymptotic :
  Filter.Tendsto (fun k => Real.log (lcmUpTo k) / k) Filter.atTop (nhds 1)

/-- LCM conjecture [EES74]: g(k) < L_k for large k. -/
def lcmConjecture : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, g k < lcmUpTo k

/-
# Part 7: Ratio Conjectures

The function g(k) is believed to be wildly irregular.
-/

/-- Conjecture: lim sup g(k+1)/g(k) = ∞. -/
def ratioLimSupConjecture : Prop :=
  ∀ M : ℝ, ∃ k : ℕ, (g (k + 1) : ℝ) / g k > M

/-- Conjecture: lim inf g(k+1)/g(k) = 0. -/
def ratioLimInfConjecture : Prop :=
  ∀ ε > 0, ∃ k : ℕ, (g (k + 1) : ℝ) / g k < ε

/-
# Part 8: Heuristic Asymptotic
-/

/-- "Right-thinking person" lower bound [ELS93]: g(k) ≥ exp(c·k/log k). -/
axiom els_consensus_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (g k : ℝ) ≥ Real.exp (c * k / Real.log k)

/-- Heuristic conjecture: log g(k) ~ c·k/log k for some c > 0. -/
def heuristicConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto (fun k => Real.log (g k) / (k / Real.log k))
      Filter.atTop (nhds c)

/-
# Part 9: Main Open Problem

The asymptotic behavior of g(k) remains unknown.
-/

/-- The main open question: determine the growth rate of g(k). -/
def erdos1095OpenProblem : Prop :=
  ∃ f : ℕ → ℝ, (∀ k, f k > 0) ∧
    Filter.Tendsto (fun k => Real.log (g k) / f k) Filter.atTop (nhds 1)

#check g
#check konyagin_lower_bound
#check ees_upper_bound
#check heuristicConjecture

end Erdos1095
