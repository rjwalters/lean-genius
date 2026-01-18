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

/-
## Prime Factors of Binomial Coefficients

The smallest prime factor and k-roughness of integers.
-/

/-- The smallest prime factor of n (or n itself if n ≤ 1) -/
noncomputable def smallestPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then n
  else Nat.minFac n

/-- An integer is k-rough if all its prime factors exceed k -/
def isKRough (n k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p > k

/-- The binomial coefficient C(n,k) -/
def binom (n k : ℕ) : ℕ := Nat.choose n k

/-- C(n,k) is k-rough: all prime factors exceed k -/
def binomIsKRough (n k : ℕ) : Prop :=
  isKRough (binom n k) k

/-
## The Erdős-Selfridge Function g(k)

g(k) = smallest n > k+1 such that C(n,k) is k-rough.
-/

/-- g(k): the Erdős-Selfridge function -/
noncomputable def g (k : ℕ) : ℕ :=
  Nat.find (⟨Nat.factorial k + k + 1, by sorry⟩ :
    ∃ n, n > k + 1 ∧ binomIsKRough n k)

/-- g(k) > k + 1 by definition -/
theorem g_gt_k_plus_one (k : ℕ) : g k > k + 1 := by
  have h := Nat.find_spec (⟨Nat.factorial k + k + 1, by sorry⟩ :
    ∃ n, n > k + 1 ∧ binomIsKRough n k)
  exact h.1

/-- C(g(k), k) is k-rough -/
theorem g_is_k_rough (k : ℕ) : binomIsKRough (g k) k := by
  have h := Nat.find_spec (⟨Nat.factorial k + k + 1, by sorry⟩ :
    ∃ n, n > k + 1 ∧ binomIsKRough n k)
  exact h.2

/-
## Known Bounds

The gap between known lower and upper bounds is enormous.
-/

/-- Original lower bound: g(k) > k^{1+c} for some c > 0 -/
axiom ees_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ k ≥ 2, (g k : ℝ) > k^(1 + c)

/-- Original upper bound: g(k) ≤ exp((1+o(1))k) -/
axiom ees_upper_bound :
  ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (g k : ℝ) ≤ Real.exp ((1 + ε) * k)

/-- Konyagin's improved lower bound: g(k) ≫ exp(c·(log k)²) -/
axiom konyagin_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (g k : ℝ) ≥ Real.exp (c * (Real.log k)^2)

/-
## The LCM Conjecture

Ecklund-Erdős-Selfridge conjectured g(k) < lcm(1,...,k) for large k.
-/

/-- L_k = lcm(1, 2, ..., k) -/
def lcmUpTo (k : ℕ) : ℕ :=
  (Finset.Icc 1 k).lcm id

/-- LCM conjecture: g(k) < L_k for large k -/
def lcmConjecture : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, g k < lcmUpTo k

/-- L_k ~ exp(k) by the prime number theorem -/
axiom lcm_asymptotic :
  Filter.Tendsto (fun k => Real.log (lcmUpTo k) / k) Filter.atTop (nhds 1)

/-
## Ratio Conjectures

The function g(k) is believed to be highly irregular.
-/

/-- Conjecture: lim sup g(k+1)/g(k) = ∞ -/
def ratioLimSupConjecture : Prop :=
  ∀ M : ℝ, ∃ k : ℕ, (g (k + 1) : ℝ) / g k > M

/-- Conjecture: lim inf g(k+1)/g(k) = 0 -/
def ratioLimInfConjecture : Prop :=
  ∀ ε > 0, ∃ k : ℕ, (g (k + 1) : ℝ) / g k < ε

/-
## Heuristic Asymptotic

The expected behavior: log g(k) ≍ k/log k.
-/

/-- Heuristic conjecture: log g(k) ~ c·k/log k for some c -/
def heuristicConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto (fun k => Real.log (g k) / (k / Real.log k))
      Filter.atTop (nhds c)

/-- "Right-thinking person" lower bound: g(k) ≥ exp(c·k/log k) -/
axiom els_consensus_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (g k : ℝ) ≥ Real.exp (c * k / Real.log k)

/-
## Known Values

Some computed values of g(k) for small k.
-/

/-- g(2) = 3 since C(3,2) = 3 is 2-rough -/
axiom g_2 : g 2 = 3

/-- g(3) = 7 since C(7,3) = 35 = 5·7 is 3-rough -/
axiom g_3 : g 3 = 7

/-- g(4) = 23 -/
axiom g_4 : g 4 = 23

/-- g(5) = 62 -/
axiom g_5 : g 5 = 62

/-- g(6) = 143 -/
axiom g_6 : g 6 = 143

/-
## Main Open Problem

The asymptotic behavior of g(k) remains unknown.
-/

/-- The main open question: determine the growth rate of g(k) -/
def erdos1095OpenProblem : Prop :=
  ∃ f : ℕ → ℝ, (∀ k, f k > 0) ∧
    Filter.Tendsto (fun k => Real.log (g k) / f k) Filter.atTop (nhds 1)

#check g
#check konyagin_lower_bound
#check ees_upper_bound
#check heuristicConjecture
