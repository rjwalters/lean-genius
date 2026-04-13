/-
  Aristotle targets for Erdős Problem #1100
  Routine supporting lemmas for automated proof search.
  See Erdos1100Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT question1_almost_all_growth, question2_upper_bound (open problems)
  - NOT g_exponential_growth sorries (depend on erdos_simonovits_bounds axiom, asymptotic)
  - Routine arithmetic: tau, omega computations; divisibility facts
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1100Aristotle

open Finset Nat Real

/-- τ(n): Number of divisors of n. -/
def tau (n : ℕ) : ℕ := (Finset.filter (· ∣ n) (Finset.range (n + 1))).card

/-- ω(n): Number of distinct prime divisors. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

-- Routine: τ(1) = 1.
-- Only 1 divides 1, so the filter {d ∈ [0,1] | d ∣ 1} = {1} has cardinality 1.
theorem tau_one : tau 1 = 1 := by native_decide

-- Routine: ω(1) = 0.
-- 1 has no prime factors, so primeFactors 1 = ∅.
theorem omega_one : omega 1 = 0 := by native_decide

-- Routine: τ(p) = 2 for prime p.
-- The only divisors of p are 1 and p.
theorem tau_prime (p : ℕ) (hp : p.Prime) : tau p = 2 := by
  sorry

-- Routine: ω(p) = 1 for prime p.
-- A prime has exactly one distinct prime factor (itself).
-- Mathlib: Nat.Prime.primeFactors_eq says primeFactors p = {p}.
theorem omega_prime (p : ℕ) (hp : p.Prime) : omega p = 1 := by
  sorry

-- Routine: For n > 0, τ(n) ≥ 1.
-- n has at least the divisor 1 (since 1 ∣ n for all n > 0).
theorem tau_pos (n : ℕ) (hn : n > 0) : tau n ≥ 1 := by
  sorry

-- Routine: 1 divides every natural number.
-- This is Nat.one_dvd.
theorem one_dvd_all (n : ℕ) : 1 ∣ n := one_dvd n

-- Routine: For n > 0, n divides n.
-- n is always in the set of divisors of n.
theorem self_dvd (n : ℕ) (hn : n > 0) : n ∣ n := dvd_refl n

-- Routine: τ(n) ≤ n for n ≥ 1.
-- All divisors d of n satisfy 1 ≤ d ≤ n, so they lie in Finset.range(n+1).
-- The filter has at most n+1 elements, but divisors > n don't exist for n > 0.
theorem tau_le_self (n : ℕ) (hn : n ≥ 1) : tau n ≤ n := by
  sorry

-- Routine: 2^n > 0 for all n.
-- Needed for density calculations.
theorem two_pow_pos (n : ℕ) : 2 ^ n > 0 := Nat.pos_pow_of_pos n (by norm_num)

-- Routine: Real.sqrt 2 > 1.
-- √2 ≈ 1.414, which is > 1.
theorem sqrt_two_gt_one : Real.sqrt 2 > 1 := by
  sorry

-- Routine: For c > 0, c^k > 0 for all k.
-- Positive powers of a positive real are positive.
theorem pow_pos_of_pos (c : ℝ) (hc : c > 0) (k : ℕ) : c ^ k > 0 := by
  exact pow_pos hc k

end Erdos1100Aristotle
