/-
Erdős Problem #792: Sum-Free Subsets

A set B ⊆ ℤ is sum-free if there are no solutions to a + b = c with a, b, c ∈ B.
(We may or may not require a ≠ b depending on the convention.)

Let f(n) be the maximum value such that any subset A ⊆ ℤ with |A| = n contains
a sum-free subset B ⊆ A with |B| ≥ f(n).

Problem: Estimate f(n).

Known bounds:
- Lower: f(n) ≥ n/3 (Erdős)
- Lower: f(n) ≥ (n+1)/3 (Alon-Kleitman)
- Lower: f(n) ≥ (n+2)/3 (Bourgain)
- Lower: f(n) ≥ n/3 + c·log log n (Bedert, 2025)
- Upper: f(n) ≤ n/3 + o(n) (Eberhard-Green-Manners)

This is Problem #792 from erdosproblems.com.
Also Problem 1 on Ben Green's open problems list.

Reference: https://erdosproblems.com/792

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
# Erdős Problem 792: Sum-Free Subsets

*Reference:* [erdosproblems.com/792](https://www.erdosproblems.com/792)
-/

open Nat Finset Set
open Filter

namespace Erdos792

/-- A set B is sum-free if there are no a, b, c ∈ B with a + b = c -/
def SumFree (B : Set ℤ) : Prop :=
  ∀ a b c : ℤ, a ∈ B → b ∈ B → c ∈ B → a + b ≠ c

/-- For finsets: sum-free predicate -/
def SumFreeFinset (B : Finset ℤ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a + b ≠ c

/-- A sum-free subset of A -/
def IsSumFreeSubset (B A : Finset ℤ) : Prop :=
  B ⊆ A ∧ SumFreeFinset B

/-- The maximum size of a sum-free subset of A -/
noncomputable def maxSumFreeSize (A : Finset ℤ) : ℕ :=
  sSup {n | ∃ B : Finset ℤ, IsSumFreeSubset B A ∧ B.card = n}

/-- f(n): the minimum, over all n-element sets A, of maxSumFreeSize(A) -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∀ A : Finset ℤ, A.card = n → maxSumFreeSize A ≥ m}

/-!
## Main Problem

Erdős Problem #792: Estimate f(n).

The main question is the exact asymptotics of f(n).
Current knowledge: n/3 ≤ f(n) ≤ n/3 + o(n).
-/

/-- Erdős Problem #792: Determine the asymptotics of f(n) -/
@[category research open, AMS 11]
theorem erdos_792 : answer(sorry) ↔
    ∃ g : ℕ → ℝ, (∀ᶠ n in atTop, g n / n → 0) ∧
      ∀ᶠ n in atTop, (f n : ℝ) = n / 3 + g n := by
  sorry

/-!
## Lower Bounds

Several progressively stronger lower bounds have been proven.
-/

/-- Erdős's original bound: f(n) ≥ n/3 -/
@[category research, AMS 11]
theorem erdos_lower_bound : ∀ n ≥ 1, (f n : ℝ) ≥ n / 3 := by
  sorry

/-- Alon-Kleitman: f(n) ≥ (n+1)/3 -/
@[category research, AMS 11]
theorem alon_kleitman_bound : ∀ n ≥ 1, f n ≥ (n + 1) / 3 := by
  sorry

/-- Bourgain: f(n) ≥ (n+2)/3 -/
@[category research, AMS 11]
theorem bourgain_bound : ∀ n ≥ 1, f n ≥ (n + 2) / 3 := by
  sorry

/-- Bedert (2025): f(n) ≥ n/3 + c·log log n for some c > 0 -/
@[category research, AMS 11]
theorem bedert_bound : ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n in atTop, (f n : ℝ) ≥ n / 3 + c * Real.log (Real.log n) := by
  sorry

/-!
## Upper Bounds

Eberhard, Green, and Manners established the upper bound.
-/

/-- Eberhard-Green-Manners: f(n) ≤ n/3 + o(n) -/
@[category research, AMS 11]
theorem egm_upper_bound : ∀ ε > 0, ∀ᶠ n in atTop,
    (f n : ℝ) ≤ n / 3 + ε * n := by
  sorry

/-- Corollary: lim_{n→∞} f(n)/n = 1/3 -/
@[category research, AMS 11]
theorem f_limit : Filter.Tendsto (fun n => (f n : ℝ) / n) atTop (nhds (1/3)) := by
  sorry

/-!
## Examples and Special Cases
-/

/-- Example: The set {1, 2, 3} has maximal sum-free subset {1} or {3} of size 1 -/
-- Note: 1 + 2 = 3, so we cannot include both 1, 2 and 3
example : maxSumFreeSize {1, 2, 3} ≥ 1 := by
  sorry

/-- Example: The interval [n, 2n-1] is sum-free -/
-- If a, b ∈ [n, 2n-1], then a + b ≥ 2n > 2n-1, so a + b ∉ [n, 2n-1]
lemma interval_sum_free (n : ℕ) (hn : n ≥ 1) :
    SumFreeFinset (Finset.Icc n (2*n - 1)) := by
  sorry

/-- The "middle third" construction: take elements in (n/3, 2n/3] -/
-- This gives a sum-free set of size ≈ n/3
lemma middle_third_sum_free (A : Finset ℤ) :
    ∃ B : Finset ℤ, IsSumFreeSubset B A ∧ B.card ≥ A.card / 3 := by
  sorry

/-!
## Structural Results
-/

/-- Every set A ⊆ ℤ of size n has a sum-free subset of size ≥ ⌈n/3⌉ -/
lemma sum_free_subset_exists (A : Finset ℤ) :
    ∃ B : Finset ℤ, IsSumFreeSubset B A ∧ B.card ≥ (A.card + 2) / 3 := by
  sorry

/-- The extremal sets achieving f(n) are related to arithmetic structures -/
-- Sets achieving the minimum often have rich additive structure

/-!
## Connection to Additive Combinatorics

The sum-free subset problem is a cornerstone of additive combinatorics.
-/

/-- A set is sum-free iff it contains no 3-term arithmetic progression -/
-- This is because a + c = 2b means (a, b, c) is an AP with a ≠ c
-- But sum-free is actually stricter: no a + b = c at all

/-- Relationship to Schur numbers and Ramsey theory -/
-- Schur's theorem: for any r-coloring of [1, n], some color class contains a, b, c
-- with a + b = c. This is related but different from sum-free subsets.

/-!
## Open Questions
-/

/-- The main open question: What is the second-order term in f(n)? -/
-- We know f(n) = n/3 + g(n) where g(n) = o(n)
-- Bedert: g(n) ≥ c·log log n
-- But what is the true growth rate of g(n)?

/-- Is f(n) = n/3 + Θ(log log n)? -/
@[category research open, AMS 11]
theorem erdos_792_second_order : answer(sorry) ↔
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ᶠ n in atTop,
        c₁ * Real.log (Real.log n) ≤ (f n : ℝ) - n/3 ∧
        (f n : ℝ) - n/3 ≤ c₂ * Real.log (Real.log n) := by
  sorry

end Erdos792

-- Placeholder for main result
theorem erdos_792_placeholder : True := trivial
