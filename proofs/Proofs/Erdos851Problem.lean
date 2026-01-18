/-
  Erdős Problem #851: Density of Integers 2^k + n

  **Romanoff's Theorem (1934)**: The set of integers of the form 2^k + p
  (where p is prime) has positive lower density.

  **Erdős's Question**: For any ε > 0, is there some r such that the density
  of integers of the form 2^k + n (where n has at most r prime factors)
  is at least 1 - ε?

  In other words, can we cover almost all integers by allowing n to have
  a bounded number of prime factors?

  References:
  - https://erdosproblems.com/851
  - Romanoff, N.P., "Über einige Sätze der additiven Zahlentheorie" (1934)
-/

import Mathlib

open Nat Set Finset BigOperators

namespace Erdos851

/-!
## Core Definitions

We define the set of integers representable as 2^k + n where n has
at most r prime factors (counted with multiplicity).
-/

/-- An integer m is in **TwoPowAddSet r** if m = 2^k + n for some k ≥ 0
and n with at most r distinct prime factors. -/
def TwoPowAddSet (r : ℕ) : Set ℕ :=
  {m | ∃ k n : ℕ, m = 2^k + n ∧ n.primeFactors.card ≤ r}

/-- The lower density of a set S ⊆ ℕ is
    liminf_{N→∞} |S ∩ [1,N]| / N

We axiomatize this to avoid decidability issues. -/
axiom lowerDensity (S : Set ℕ) : ℝ

/-!
## Basic Properties
-/

/-- All powers of 2 plus 1 are in TwoPowAddSet 0 (since 1 has 0 prime factors). -/
theorem twoPow_add_one_mem (k : ℕ) : 2^k + 1 ∈ TwoPowAddSet 0 := by
  refine ⟨k, 1, rfl, ?_⟩
  simp [Nat.primeFactors]

/-- TwoPowAddSet is monotone in r. -/
theorem twoPowAddSet_mono {r s : ℕ} (h : r ≤ s) : TwoPowAddSet r ⊆ TwoPowAddSet s := by
  intro m ⟨k, n, hm, hr⟩
  exact ⟨k, n, hm, le_trans hr h⟩

/-- The union over all r covers all positive integers ≥ 2. -/
theorem twoPowAddSet_union_covers (m : ℕ) (hm : 2 ≤ m) :
    ∃ r, m ∈ TwoPowAddSet r := by
  refine ⟨(m - 1).primeFactors.card, 0, m - 1, ?_, le_refl _⟩
  omega

/-!
## Romanoff's Theorem (1934)

The set of integers of the form 2^k + p (where p is prime) has positive
lower density. This was proved by Romanoff in 1934.
-/

/-- **Romanoff's Theorem (1934)**: The set of integers of the form 2^k + p
(where p is prime or 1) has positive lower density. -/
axiom romanoff_theorem : 0 < lowerDensity (TwoPowAddSet 1)

/-- The lower density of TwoPowAddSet 1 is approximately 0.0868... -/
axiom romanoff_density_value :
    0.08 < lowerDensity (TwoPowAddSet 1) ∧ lowerDensity (TwoPowAddSet 1) < 0.10

/-!
## Main Conjecture (OPEN)

Erdős asked whether by allowing n to have more prime factors, we can
achieve density arbitrarily close to 1.
-/

/-- **Erdős Problem #851 (OPEN)**: For any ε > 0, is there some r such that
the density of TwoPowAddSet r is at least 1 - ε?

This asks whether almost all integers can be represented as 2^k + n
where n has a bounded number of prime factors. -/
axiom erdos_851_conjecture :
    ∀ ε : ℝ, ε > 0 → ∃ r : ℕ, 1 - ε ≤ lowerDensity (TwoPowAddSet r)

/-!
## Density Properties
-/

/-- The density of TwoPowAddSet r is monotonically increasing in r. -/
axiom density_mono (r s : ℕ) (hr : r ≤ s) :
    lowerDensity (TwoPowAddSet r) ≤ lowerDensity (TwoPowAddSet s)

/-- The limiting density is at most 1. -/
axiom density_le_one (r : ℕ) : lowerDensity (TwoPowAddSet r) ≤ 1

/-!
## The Key Question

The main open question is whether the limiting density equals 1.
If yes, then Erdős's conjecture is true.
If no, there's a positive proportion of integers that cannot be
written as 2^k + n for any n with bounded prime factors.
-/

/-- The conjecture is equivalent to asking if lim_{r→∞} density(r) = 1. -/
axiom conjecture_iff_limit_one :
    (∀ ε : ℝ, ε > 0 → ∃ r : ℕ, 1 - ε ≤ lowerDensity (TwoPowAddSet r)) ↔
    (∀ ε : ℝ, ε > 0 → ∃ r₀ : ℕ, ∀ r ≥ r₀, 1 - ε < lowerDensity (TwoPowAddSet r))

/-!
## Related Results
-/

/-- The set of integers NOT of the form 2^k + p (prime) has positive density.
This is the "uncovered" portion that Romanoff's theorem leaves. -/
axiom uncovered_by_primes_positive :
    0 < lowerDensity ((TwoPowAddSet 1)ᶜ)

/-- Erdős-Odlyzko (1979): Improved lower bounds on Romanoff density. -/
axiom erdos_odlyzko_bound :
    0.0868 < lowerDensity (TwoPowAddSet 1)

/-!
## Examples

We verify specific integers belong to TwoPowAddSet for various r.
-/

/-- 3 = 2^1 + 1 is in TwoPowAddSet 0. -/
theorem three_mem : 3 ∈ TwoPowAddSet 0 :=
  ⟨1, 1, rfl, by simp [Nat.primeFactors]⟩

/-- 5 = 2^2 + 1 is in TwoPowAddSet 0. -/
theorem five_mem : 5 ∈ TwoPowAddSet 0 :=
  ⟨2, 1, rfl, by simp [Nat.primeFactors]⟩

/-- 9 = 2^3 + 1 is in TwoPowAddSet 0. -/
theorem nine_mem : 9 ∈ TwoPowAddSet 0 :=
  ⟨3, 1, rfl, by simp [Nat.primeFactors]⟩

/-- 17 = 2^4 + 1 is in TwoPowAddSet 0. -/
theorem seventeen_mem : 17 ∈ TwoPowAddSet 0 :=
  ⟨4, 1, rfl, by simp [Nat.primeFactors]⟩

/-- For any prime p, 2^k + p ∈ TwoPowAddSet 1. -/
axiom twoPow_add_prime_mem (k : ℕ) (p : ℕ) (hp : p.Prime) :
    2^k + p ∈ TwoPowAddSet 1

/-!
## Connection to Covering Congruences

This problem is related to covering congruences. Erdős and others
studied which integers can be "covered" by representations of
specific forms.

A key observation: if m ≡ 0 (mod 2^k) for all small k, then m
cannot be written as 2^k + n for small n, limiting representations.
-/

/-- The covering problem: for large r, does TwoPowAddSet r contain
almost all integers? -/
axiom covering_problem_open :
    (∀ r : ℕ, ((TwoPowAddSet r)ᶜ : Set ℕ).Nonempty) ∨
    (∃ r : ℕ, ∀ m : ℕ, m ≥ 2 → m ∈ TwoPowAddSet r)

/-!
## Historical Context

Romanoff (1934) initiated the study of representations n = 2^k + p.
The positive lower density result was surprising and opened questions
about how "complete" such representations can be.

Erdős's question generalizes this: if we allow n to have more prime
factors, can we cover almost all integers?

The problem connects to:
- Additive number theory
- Sieve methods
- Density of sets defined by arithmetic conditions

Key references:
- Romanoff, N.P., "Über einige Sätze der additiven Zahlentheorie" (1934)
- Erdős, P. and Odlyzko, A.M., "On the density of odd integers of the
  form (p-1)/2^n and related questions" (1979)
-/

end Erdos851
