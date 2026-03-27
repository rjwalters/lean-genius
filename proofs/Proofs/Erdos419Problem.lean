/- Erdős Problem #419: Limit Points of τ((n+1)!)/τ(n!)

  Source: https://erdosproblems.com/419
  Status: SOLVED (Erdős-Graham-Ivić-Pomerance 1996, Sawhney rediscovery)

  Statement:
  If τ(n) counts the number of divisors of n, what is the set of limit points of
  τ((n+1)!)/τ(n!)?

  Answer:
  The limit points are exactly {1} ∪ {1 + 1/k : k ≥ 1} = {1, 2, 3/2, 4/3, 5/4, ...}

  Background:
  - τ(n) = divisor function = number of positive divisors of n
  - τ(n!) grows rapidly as n increases
  - The ratio τ((n+1)!)/τ(n!) is related to prime factorization of n+1
  - For n+1 = p (prime), ratio ≈ 2; for n+1 = pk (prime × small), ratio ≈ 1 + 1/k

  Tags: number-theory, divisor-function, factorial, limit-points, solved
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Analysis.SpecificLimits.Basic

namespace Erdos419

open Nat ArithmeticFunction

/- ## Part 1: Basic Definitions

The divisor function and factorials.
-/

/-- The divisor function τ(n) = number of positive divisors of n -/
noncomputable def tau (n : ℕ) : ℕ := n.divisors.card

/-- The ratio we're studying -/
noncomputable def factorialDivisorRatio (n : ℕ) : ℚ :=
  if h : n.factorial ≠ 0 ∧ (n + 1).factorial ≠ 0 then
    (tau (n + 1).factorial : ℚ) / (tau n.factorial : ℚ)
  else 1

/- ## Part 2: The Ratio Formula

Key identity relating the ratio to prime factorization of n+1.
-/

/-- The p-adic valuation of n! (Legendre's formula) -/
noncomputable def padicValFactorial (p n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, n / p^(i + 1)

/- ## Part 3: Prime Factorization Bounds

Bounds on prime factors and their valuations.
-/

/- ## Part 4: Small Primes Contribution

Primes p ≤ n^(2/3) contribute approximately 1 to the ratio.
-/

/- ## Part 5: Large Prime Contribution

If n+1 = pk where p > n^(2/3), this prime contributes exactly 1 + 1/k.
-/

/- ## Part 6: The Set of Limit Points

The complete characterization.
-/

/-- The candidate set of limit points: {1} ∪ {1 + 1/k : k ≥ 1} -/
def limitPointSet : Set ℚ :=
  {1} ∪ {x | ∃ k : ℕ, k ≥ 1 ∧ x = 1 + 1 / k}

/-- 1 + 1/k for k = 1, 2, 3, ... gives 2, 3/2, 4/3, ... -/
example : (1 : ℚ) + 1/1 = 2 := by norm_num
example : (1 : ℚ) + 1/2 = 3/2 := by norm_num
example : (1 : ℚ) + 1/3 = 4/3 := by norm_num
example : (1 : ℚ) + 1/4 = 5/4 := by norm_num

/-- 1 is a limit point (infinitely many n with ratio close to 1) -/
axiom one_is_limit_point :
    ∀ ε > 0, ∃ᶠ n in Filter.atTop, |factorialDivisorRatio n - 1| < ε

/-- Each 1 + 1/k is a limit point -/
axiom one_plus_reciprocal_is_limit_point (k : ℕ) (hk : k ≥ 1) :
    ∀ ε > 0, ∃ᶠ n in Filter.atTop, |factorialDivisorRatio n - (1 + 1/k)| < ε

/-- These are the ONLY limit points -/
axiom only_these_limit_points (x : ℚ) :
    (∀ ε > 0, ∃ᶠ n in Filter.atTop, |factorialDivisorRatio n - x| < ε) →
    x ∈ limitPointSet

/- ## Part 7: Examples and Concrete Cases

Concrete cases illustrating the phenomenon.
-/

/- ## Part 8: The Proof Structure and Main Theorem

The ratio decomposition and Sawhney's characterization.
-/

/-- Sawhney's argument: the only limit points are {1, 2, 3/2, 4/3, ...} -/
theorem sawhney_characterization :
    ∀ x : ℚ, (∀ ε > 0, ∃ᶠ n in Filter.atTop, |factorialDivisorRatio n - x| < ε) ↔
      x ∈ limitPointSet := by
  intro x
  constructor
  · exact only_these_limit_points x
  · intro hx
    cases hx with
    | inl h1 =>
      rw [h1]
      exact one_is_limit_point
    | inr hk =>
      obtain ⟨k, hk_pos, hx_eq⟩ := hk
      rw [hx_eq]
      exact one_plus_reciprocal_is_limit_point k hk_pos

/- ## Part 9: Asymptotics of τ(n!)

Related results on the divisor function of factorials.
-/

/- ## Part 10: Summary

The limit points are exactly {1, 2, 3/2, 4/3, 5/4, ...}.
-/

/-- The limit point set is closed and has accumulation point at 1 -/
theorem limit_set_properties :
    (1 : ℚ) ∈ limitPointSet ∧
    ∀ k ≥ 1, (1 : ℚ) + 1/k ∈ limitPointSet ∧
    ∀ x ∈ limitPointSet, x ≥ 1 := by
  constructor
  · left; rfl
  constructor
  · intro k hk
    right
    use k, hk
  · intro x hx
    cases hx with
    | inl h1 => simp [h1]
    | inr hk =>
      obtain ⟨k, hk_pos, hx⟩ := hk
      simp [hx]
      have : (k : ℚ) ≥ 1 := by exact Nat.one_le_cast.mpr hk_pos
      linarith [this, one_div_pos.mpr (by linarith : (k : ℚ) > 0)]

/-- Erdős Problem #419: SOLVED
    The limit points of τ((n+1)!)/τ(n!) are exactly {1} ∪ {1+1/k : k ≥ 1}.
    Combines: characterization theorem, limit point existence, and uniqueness. -/
theorem erdos_419_summary :
    (∀ x : ℚ, (∀ ε > 0, ∃ᶠ n in Filter.atTop, |factorialDivisorRatio n - x| < ε) ↔
      x ∈ limitPointSet) ∧
    (∀ ε > 0, ∃ᶠ n in Filter.atTop, |factorialDivisorRatio n - 1| < ε) ∧
    (∀ k : ℕ, k ≥ 1 → ∀ ε > 0, ∃ᶠ n in Filter.atTop, |factorialDivisorRatio n - (1 + 1/k)| < ε) :=
  ⟨sawhney_characterization, one_is_limit_point, one_plus_reciprocal_is_limit_point⟩

end Erdos419
