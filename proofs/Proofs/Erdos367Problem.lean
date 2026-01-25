/-
Erdős Problem #367: Products of 2-Full Parts

For a positive integer n, the 2-full part B₂(n) is n/n', where n' is the product
of primes that divide n exactly once (i.e., squarefree part of n).
Equivalently, B₂(n) = ∏_{p² | n} p^{v_p(n)} where v_p(n) is the p-adic valuation.

Problem: For every fixed k ≥ 1, is it true that
  ∏_{n ≤ m < n+k} B₂(m) ≪ n^{2+o(1)} ?

Or perhaps even ≪_k n²?

Known results:
- For k ≤ 2, the bound ≪ n² holds trivially.
- For k ≥ 3, the bound ≪ n² fails (van Doorn).
- There exists an infinite sequence where ∏_{n ≤ m < n+3} B₂(m) ≫ n²·log n.

This is Problem #367 from erdosproblems.com.

Reference: https://erdosproblems.com/367

Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Erdős Problem 367: Products of 2-Full Parts

*Reference:* [erdosproblems.com/367](https://www.erdosproblems.com/367)
-/

open Nat Finset
open Filter

namespace Erdos367

/-- The squarefree part of n: product of primes dividing n exactly once -/
noncomputable def squarefreePart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p = 1), p

/-- The 2-full part B₂(n) = n / squarefreePart(n) -/
noncomputable def twoFullPart (n : ℕ) : ℕ :=
  if h : squarefreePart n ∣ n ∧ squarefreePart n ≠ 0
  then n / squarefreePart n
  else n

/-- Alternative: B₂(n) = ∏_{p² | n} p^{v_p(n)} -/
noncomputable def twoFullPartAlt (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p ≥ 2),
    p ^ (n.factorization p)

/-- Product of 2-full parts over a range [n, n+k) -/
noncomputable def productTwoFullParts (n k : ℕ) : ℕ :=
  ∏ m ∈ Finset.Ico n (n + k), twoFullPart m

/-!
## Main Problem

Erdős Problem #367: Study the growth of ∏_{n ≤ m < n+k} B₂(m).
-/

/-- The bound ∏_{n ≤ m < n+k} B₂(m) ≪ n^{2+ε} for all ε > 0 -/
def weakBound (k : ℕ) : Prop :=
  ∀ ε > 0, ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 1, (productTwoFullParts n k : ℝ) ≤ C * (n : ℝ)^(2 + ε)

/-- The strong bound ∏_{n ≤ m < n+k} B₂(m) ≪_k n² -/
def strongBound (k : ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 1, (productTwoFullParts n k : ℝ) ≤ C * (n : ℝ)^2

/-- Erdős Problem #367: Does weakBound(k) hold for all k? -/
@[category research open, AMS 11]
theorem erdos_367 (k : ℕ) : answer(sorry) ↔ weakBound k := by
  sorry

/-!
## Known Results
-/

/-- Trivial case: For k ≤ 2, strongBound holds -/
@[category research, AMS 11]
theorem trivial_case_k_le_2 : strongBound 1 ∧ strongBound 2 := by
  sorry

/-- The strong bound fails for k = 3 -/
@[category research, AMS 11]
theorem strong_bound_fails_k_3 : ¬ strongBound 3 := by
  sorry

/-- van Doorn: There exist infinitely many n with
    ∏_{n ≤ m < n+3} B₂(m) ≫ n² · log n -/
@[category research, AMS 11]
theorem van_doorn_lower_bound :
    ∃ c > 0, ∀ N : ℕ, ∃ n ≥ N,
      (productTwoFullParts n 3 : ℝ) ≥ c * (n : ℝ)^2 * Real.log n := by
  sorry

/-!
## Properties of the 2-Full Part
-/

/-- B₂(n) = 1 iff n is squarefree -/
lemma twoFullPart_eq_one_iff (n : ℕ) (hn : n ≥ 1) :
    twoFullPart n = 1 ↔ Squarefree n := by
  sorry

/-- B₂(p) = 1 for primes p -/
lemma twoFullPart_prime (p : ℕ) (hp : p.Prime) : twoFullPart p = 1 := by
  sorry

/-- B₂(p²) = p² for primes p -/
lemma twoFullPart_prime_sq (p : ℕ) (hp : p.Prime) : twoFullPart (p^2) = p^2 := by
  sorry

/-- B₂ is multiplicative on coprime arguments -/
lemma twoFullPart_mul_coprime (m n : ℕ) (h : Nat.Coprime m n) :
    twoFullPart (m * n) = twoFullPart m * twoFullPart n := by
  sorry

/-- B₂(n) ≤ n always -/
lemma twoFullPart_le (n : ℕ) : twoFullPart n ≤ n := by
  sorry

/-- B₂(n) divides n -/
lemma twoFullPart_dvd (n : ℕ) : twoFullPart n ∣ n := by
  sorry

/-!
## Examples
-/

/-- B₂(1) = 1 -/
example : twoFullPart 1 = 1 := by sorry

/-- B₂(4) = 4 since 4 = 2² -/
example : twoFullPart 4 = 4 := by sorry

/-- B₂(6) = 1 since 6 = 2·3 is squarefree -/
example : twoFullPart 6 = 1 := by sorry

/-- B₂(12) = 4 since 12 = 2²·3, squarefree part is 3 -/
example : twoFullPart 12 = 4 := by sorry

/-- B₂(72) = 36 since 72 = 2³·3², squarefree part is 2 -/
example : twoFullPart 72 = 36 := by sorry

/-!
## Generalization to r-Full Parts
-/

/-- The r-full part: product of p^{v_p(n)} for primes with v_p(n) ≥ r -/
noncomputable def rFullPart (r n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p ≥ r),
    p ^ (n.factorization p)

/-- The 2-full part is a special case of r-full with r = 2 -/
lemma twoFullPart_eq_rFullPart (n : ℕ) : twoFullPartAlt n = rFullPart 2 n := rfl

/-- Generalized problem for r ≥ 3 -/
@[category research open, AMS 11]
theorem erdos_367_generalized (r : ℕ) (hr : r ≥ 3) (k : ℕ) :
    answer(sorry) ↔
    ∀ ε > 0, ∃ C : ℝ, C > 0 ∧
      ∀ n ≥ 1, (∏ m ∈ Finset.Ico n (n + k), rFullPart r m : ℝ) ≤ C * (n : ℝ)^(r + ε) := by
  sorry

/-!
## Analysis of Consecutive Integers
-/

/-- Key insight: consecutive integers often share high prime powers -/
-- If p² | n, then p² | n + p² - (n mod p²) for nearby integers
-- This can create large products of 2-full parts

/-- The product is large when consecutive integers share large 2-full parts -/
lemma product_large_when_shared (n k : ℕ) :
    ∃ m₁ m₂ : ℕ, m₁ ∈ Finset.Ico n (n + k) ∧ m₂ ∈ Finset.Ico n (n + k) ∧
      m₁ ≠ m₂ → twoFullPart m₁ * twoFullPart m₂ ≤ productTwoFullParts n k := by
  sorry

/-!
## Heuristics and Expectations
-/

/-- Heuristic: B₂(n) ≈ 1 on average (most numbers are nearly squarefree) -/
-- The "typical" value of B₂(n) is small, but occasional large values
-- from highly composite numbers contribute to the product.

/-- Expected order: E[B₂(n)] is bounded -/
-- On average, B₂(n) is O(1), but the maximum over k consecutive
-- integers can be much larger.

end Erdos367

-- Placeholder for main result
theorem erdos_367_placeholder : True := trivial
