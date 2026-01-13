/-
Erdős Problem #48: Infinitely many (n,m) with φ(n) = σ(m)

Are there infinitely many integers n, m such that φ(n) = σ(m)?
(where φ is Euler's totient and σ is sum of divisors)

**Answer**: YES - proved by Ford, Luca, and Pomerance (2010)

The key insight is that for any prime p, if we can find n,m with
φ(n) = σ(m) = p - 1, then we get the pair (p, m). Since there are
infinitely many primes p where p-1 is in the range of σ, we get
infinitely many pairs.

Reference: https://www.erdosproblems.com/48
-/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors

open Nat

namespace Erdos48

/-- Sum of divisors function σ(n) -/
def sumDivisors (n : ℕ) : ℕ := (n.divisors).sum id

/-- The set of pairs (n,m) where φ(n) = σ(m) -/
def totientSigmaPairs : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | p.1.totient = sumDivisors p.2}

/--
Erdős Problem #48: There are infinitely many pairs (n,m) with φ(n) = σ(m).

This was proved by Ford, Luca, and Pomerance in 2010. The proof uses
deep results about the distribution of values of arithmetic functions.

We state this as an axiom since the full proof requires analytic number
theory techniques beyond current Mathlib formalization.
-/
axiom erdos_48 : totientSigmaPairs.Infinite

/-- σ(1) = 1 -/
theorem sumDivisors_one : sumDivisors 1 = 1 := by
  simp [sumDivisors, Nat.divisors_one]

/-- σ(3) = 1 + 3 = 4 -/
theorem sumDivisors_three : sumDivisors 3 = 4 := by native_decide

/-- φ(5) = 4 -/
theorem totient_five : (5 : ℕ).totient = 4 := by native_decide

/-- The pair (5, 3) satisfies φ(5) = σ(3) = 4 -/
theorem pair_5_3_in_set : (5, 3) ∈ totientSigmaPairs := by
  simp only [totientSigmaPairs, Set.mem_setOf_eq]
  native_decide

end Erdos48

