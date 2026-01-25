/-
Erdős Problem #950: Sum of Reciprocal Prime Gaps

Define f(n) = ∑_{p<n} 1/(n-p) where the sum is over all primes p < n.

This measures how "close" n is to primes by weighting nearby primes more heavily.

Three questions:
1. Is lim inf f(n) = 1?
2. Is lim sup f(n) = ∞?
3. Is f(n) = o(log log n) for all n?

Known results (de Bruijn, Erdős, Turán):
- ∑_{n<x} f(n) ~ ∑_{n<x} f(n)² ~ x

This is Problem #950 from erdosproblems.com.

Reference: https://erdosproblems.com/950

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
# Erdős Problem 950: Sum of Reciprocal Prime Gaps

*Reference:* [erdosproblems.com/950](https://www.erdosproblems.com/950)
-/

open Nat Finset
open Filter Real
open scoped Topology

namespace Erdos950

/-- The set of primes less than n -/
def primesLessThan (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter Nat.Prime

/-- f(n) = ∑_{p<n} 1/(n-p) where p ranges over primes -/
noncomputable def f (n : ℕ) : ℝ :=
  ∑ p ∈ primesLessThan n, (1 : ℝ) / (n - p : ℕ)

/-- Alternative using ℝ throughout -/
noncomputable def fReal (n : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range ⌊n⌋₊).filter Nat.Prime, 1 / (n - p)

/-!
## Main Questions

Erdős Problem #950 asks three specific questions about the behavior of f(n).
-/

/-- Question 1: Is lim inf f(n) = 1? -/
@[category research open, AMS 11]
theorem erdos_950_q1 : answer(sorry) ↔
    Filter.liminf (fun n => f n) atTop = 1 := by
  sorry

/-- Question 2: Is lim sup f(n) = ∞? -/
@[category research open, AMS 11]
theorem erdos_950_q2 : answer(sorry) ↔
    Filter.limsup (fun n => f n) atTop = ⊤ := by
  sorry

/-- Question 3: Is f(n) = o(log log n) for all n? -/
@[category research open, AMS 11]
theorem erdos_950_q3 : answer(sorry) ↔
    ∀ᶠ n in atTop, f n < log (log n) := by
  sorry

/-- Stronger form of Q3: f(n) = o(log log n) -/
def fLittleO : Prop :=
  Tendsto (fun n => f n / log (log n)) atTop (nhds 0)

@[category research open, AMS 11]
theorem erdos_950_q3_strong : answer(sorry) ↔ fLittleO := by
  sorry

/-!
## Known Results
-/

/-- de Bruijn-Erdős-Turán: ∑_{n<x} f(n) ~ x -/
@[category research solved, AMS 11]
theorem de_bruijn_erdos_turan_sum :
    Tendsto (fun x => (∑ n ∈ Finset.range x, f n) / x) atTop (nhds 1) := by
  sorry

/-- de Bruijn-Erdős-Turán: ∑_{n<x} f(n)² ~ x -/
@[category research solved, AMS 11]
theorem de_bruijn_erdos_turan_sum_sq :
    Tendsto (fun x => (∑ n ∈ Finset.range x, (f n)^2) / x) atTop (nhds 1) := by
  sorry

/-- Consequence: f(n) averages to 1 -/
lemma f_average_one : Tendsto (fun x => (∑ n ∈ Finset.range x, f n) / x) atTop (nhds 1) :=
  de_bruijn_erdos_turan_sum

/-!
## Basic Properties
-/

/-- f(n) ≥ 0 always -/
lemma f_nonneg (n : ℕ) : f n ≥ 0 := by
  unfold f
  apply Finset.sum_nonneg
  intro p hp
  simp only [one_div, inv_nonneg]
  exact Nat.cast_nonneg _

/-- f(2) = 0 since there are no primes < 2 -/
lemma f_two : f 2 = 0 := by
  simp [f, primesLessThan]

/-- f(3) = 1 since 2 is the only prime < 3, and 1/(3-2) = 1 -/
lemma f_three : f 3 = 1 := by
  simp [f, primesLessThan]
  sorry

/-- f(4) = 1/2 + 1 = 3/2 since primes < 4 are 2, 3 -/
lemma f_four : f 4 = 3/2 := by
  simp [f, primesLessThan]
  sorry

/-- For prime p, the term 1/(n-p) contributes to f(n) -/
lemma prime_contributes (n p : ℕ) (hp : p.Prime) (hpn : p < n) :
    (1 : ℝ) / (n - p : ℕ) ∈ Set.range (fun q => (1 : ℝ) / (n - q)) := by
  exact ⟨p, rfl⟩

/-!
## Heuristic Analysis
-/

/-- If n is just after a prime p, then 1/(n-p) is large -/
-- For n = p + 1, the term 1/(n-p) = 1
-- This suggests f(n) could be large when n follows a prime closely

/-- If n is far from all primes, f(n) is small -/
-- Large gaps between primes lead to small f(n) values
-- This suggests lim inf f(n) could be less than 1

/-- Average analysis: ∑_{p<n} 1/(n-p) ≈ ∫_2^n 1/(n-t) · (1/log t) dt -/
-- By PNT, primes have density ~ 1/log t near t
-- The integral ~ log(n-2)/log(n) ~ 1 for large n
-- This explains why the average is 1

/-!
## Related Weaker Conjecture
-/

/-- Erdős's weaker conjecture: For every ε > 0, large x has some y < x with
    π(x) < π(y) + ε·π(x-y) -/
def weakerConjecture : Prop :=
  ∀ ε > 0, ∀ᶠ x in atTop, ∃ y : ℕ, y < x ∧
    primeCountingFunction x < primeCountingFunction y + ε * primeCountingFunction (x - y)
  where
    primeCountingFunction (n : ℕ) : ℝ := (primesLessThan (n + 1)).card

/-- If the weaker bound π(x) < π(y) + O((x-y)/log x) holds, then f(n) ≪ log log log n -/
@[category research, AMS 11]
theorem weaker_implies_bound : weakerConjecture →
    ∃ C > 0, ∀ᶠ n in atTop, f n ≤ C * log (log (log n)) := by
  sorry

/-!
## Connection to Prime Distribution
-/

/-- Prime gap at the m-th prime -/
noncomputable def primeGap (m : ℕ) : ℕ :=
  m.nth Nat.Prime + 1 - m.nth Nat.Prime

/-- f(n) is related to the reciprocals of distances to primes -/
-- Large f(n) occurs when n has many primes nearby
-- Small f(n) occurs in regions sparse in primes

/-- Having many primes in [n-k, n) increases f(n) -/
lemma dense_primes_increase_f (n k : ℕ) (hk : k > 0) :
    (primesLessThan n ∩ Finset.Ico (n - k) n).card > 0 →
    f n ≥ 1 / k := by
  sorry

end Erdos950

-- Placeholder for main result
theorem erdos_950_placeholder : True := trivial
