/-
Erdős Problem #404: Prime Power Divisibility of Factorial Sums

For which integers a ≥ 1 and primes p is there a finite upper bound on those k such that
there exist a = a₁ < a₂ < ··· < aₙ with p^k | (a₁! + a₂! + ··· + aₙ!)?

Let f(a, p) denote the greatest such k if it exists. How does f(a, p) behave?

Secondary question: Is there a prime p and an infinite sequence a₁ < a₂ < ···
such that if p^{mₖ} is the highest power of p dividing ∑_{i≤k} aᵢ!, then mₖ → ∞?

Known results:
- Lin: f(2, 2) ≤ 254

This is Problem #404 from erdosproblems.com.

Reference: https://erdosproblems.com/404

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

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem 404: Prime Power Divisibility of Factorial Sums

*Reference:* [erdosproblems.com/404](https://www.erdosproblems.com/404)
-/

open Nat Finset
open Filter

namespace Erdos404

/-- A strictly increasing sequence starting at a -/
structure StrictIncSeq (a : ℕ) where
  length : ℕ
  seq : Fin length → ℕ
  starts_at_a : length > 0 → seq ⟨0, by omega⟩ = a
  strictly_increasing : ∀ i j : Fin length, i < j → seq i < seq j

/-- The sum of factorials over a sequence -/
noncomputable def factorialSum (s : StrictIncSeq a) : ℕ :=
  ∑ i : Fin s.length, (s.seq i).factorial

/-- p^k divides the factorial sum -/
def dividesByPrimePower (a k : ℕ) (p : ℕ) : Prop :=
  ∃ s : StrictIncSeq a, p^k ∣ factorialSum s

/-- The set of k such that some sequence starting at a has p^k | sum of factorials -/
def divisiblePowers (a : ℕ) (p : ℕ) : Set ℕ :=
  {k | dividesByPrimePower a k p}

/-- f(a, p) = sup {k | p^k divides some factorial sum starting at a} -/
noncomputable def f (a : ℕ) (p : ℕ) : ℕ∞ :=
  sSup (divisiblePowers a p : Set ℕ)

/-!
## Main Questions

Erdős Problem #404 asks about the finiteness and behavior of f(a, p).
-/

/-- Question 1: For which (a, p) is f(a, p) finite? -/
@[category research open, AMS 11]
theorem erdos_404_q1 (a : ℕ) (p : ℕ) (hp : p.Prime) :
    answer(sorry) ↔ f a p < ⊤ := by
  sorry

/-- Question 2: How does f(a, p) behave as a function of a and p? -/
-- This is a qualitative question about the structure of f

/-- Secondary question: Does there exist p and sequence with mₖ → ∞? -/
def secondaryQuestion : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ seq : ℕ → ℕ, StrictMono seq ∧
    Tendsto (fun k => padicValNat p (∑ i ∈ Finset.range (k+1), (seq i).factorial)) atTop atTop

@[category research open, AMS 11]
theorem erdos_404_secondary : answer(sorry) ↔ secondaryQuestion := by
  sorry

/-!
## Known Results
-/

/-- Lin's bound: f(2, 2) ≤ 254 -/
@[category research solved, AMS 11]
theorem lin_bound : f 2 2 ≤ 254 := by
  sorry

/-- This means: for any strictly increasing sequence starting at 2,
    2^255 does not divide the sum of factorials -/
lemma lin_bound_meaning : ∀ s : StrictIncSeq 2, ¬(2^255 ∣ factorialSum s) := by
  sorry

/-!
## p-adic Analysis of Factorials
-/

/-- Legendre's formula: v_p(n!) = ∑_{i≥1} ⌊n/p^i⌋ -/
noncomputable def legendreSum (n p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.log p n + 1), n / p^(i+1)

lemma legendre_formula (n p : ℕ) (hp : p.Prime) (hn : n ≥ 1) :
    padicValNat p n.factorial = legendreSum n p := by
  sorry

/-- For large n, v_p(n!) ≈ n/(p-1) -/
lemma padic_val_factorial_asymp (p : ℕ) (hp : p.Prime) :
    Tendsto (fun n => (padicValNat p n.factorial : ℝ) / n) atTop (nhds (1/(p-1))) := by
  sorry

/-!
## Structure of Factorial Sums
-/

/-- If a₁ < a₂, then a₂! dominates and a₁! + a₂! ≡ a₁! (mod a₂!) -/
lemma factorial_sum_mod (a₁ a₂ : ℕ) (h : a₁ < a₂) :
    a₁.factorial + a₂.factorial ≡ a₁.factorial [MOD a₂.factorial] := by
  sorry

/-- The p-adic valuation of a sum depends on cancellation -/
-- If all terms have the same p-adic valuation, the sum might have higher or equal valuation
-- Cancellation can increase the valuation

/-- Key observation: a₁! + a₂! = a₁!(1 + (a₂!/a₁!)) -/
lemma factorial_sum_factored (a₁ a₂ : ℕ) (h : a₁ ≤ a₂) :
    a₁.factorial + a₂.factorial = a₁.factorial * (1 + a₂.factorial / a₁.factorial) := by
  sorry

/-!
## Examples
-/

/-- Example: 2! + 3! = 2 + 6 = 8 = 2³, so f(2, 2) ≥ 3 -/
example : 2^3 ∣ Nat.factorial 2 + Nat.factorial 3 := by
  native_decide

/-- Example: 1! + 2! = 1 + 2 = 3, so 3 | 1! + 2! -/
example : 3 ∣ Nat.factorial 1 + Nat.factorial 2 := by
  native_decide

/-- For p > a, we have v_p(a!) = 0, so v_p(a₁! + ··· + aₙ!) = v_p(sum of small numbers) -/
-- This makes the problem easier for large primes

/-!
## Heuristics
-/

/-- Heuristic: For fixed a, as p → ∞, f(a, p) should decrease -/
-- Larger primes divide fewer numbers, making high powers harder to achieve

/-- Heuristic: For fixed p, as a → ∞, f(a, p) might increase -/
-- Larger starting points give access to larger factorials with more p factors

/-- The problem cannot be resolved by finite computation -/
-- Even if f(a, p) < ∞, verifying this requires infinite search

/-!
## Special Cases
-/

/-- For a = 1: studying 1! + larger factorials -/
-- 1! = 1, so we're asking about 1 + (larger factorials)

/-- For p = 2: the most studied case -/
-- Lin's bound gives f(2, 2) ≤ 254
-- The structure of 2-adic valuations is well-understood

/-- When does equality f(a, p) = k hold? -/
-- This means p^k divides some sum, but p^{k+1} never does

end Erdos404

-- Placeholder for main result
theorem erdos_404_placeholder : True := trivial
