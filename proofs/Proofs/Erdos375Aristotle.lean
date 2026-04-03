/-
  Aristotle targets for Erdős Problem #375 (Grimm's Conjecture)
  Routine supporting lemmas for automated proof search.
  See Erdos375Problem.lean for the main formalization.

  These are concrete examples and routine number-theoretic facts
  that support the partial results in the main file.

  Criteria for inclusion:
  - NOT Grimm's conjecture itself (an open problem)
  - Concrete compositeness facts decidable from definitions
  - Routine prime divisibility facts
  - Supporting lemmas for the k=1 case
-/
import Mathlib

namespace Erdos375Aristotle

open Nat

/-
## Definitions

Local copies from the main file to keep the companion self-contained.
-/

/-- A composite number is > 1 and not prime. -/
def isComposite (n : ℕ) : Prop := n > 1 ∧ ¬ n.Prime

/-- A consecutive composite block: n+1, ..., n+k are all composite. -/
def isCompositeBlock (n k : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ k → isComposite (n + i)

/-
## Concrete Compositeness Facts

These are all decidable and routine for Aristotle.
-/

-- 24 = 2³ × 3 is composite
theorem composite_24 : isComposite 24 := by
  sorry

-- 25 = 5² is composite
theorem composite_25 : isComposite 25 := by
  sorry

-- 26 = 2 × 13 is composite
theorem composite_26 : isComposite 26 := by
  sorry

-- 90 = 2 × 3² × 5 is composite
theorem composite_90 : isComposite 90 := by sorry

-- 91 = 7 × 13 is composite
theorem composite_91 : isComposite 91 := by sorry

-- 92 = 2² × 23 is composite
theorem composite_92 : isComposite 92 := by sorry

-- 93 = 3 × 31 is composite
theorem composite_93 : isComposite 93 := by sorry

-- 94 = 2 × 47 is composite
theorem composite_94 : isComposite 94 := by sorry

-- 95 = 5 × 19 is composite
theorem composite_95 : isComposite 95 := by sorry

/-
## Consecutive Composite Block Examples
-/

-- 24, 25, 26 are all composite (n = 23, k = 3)
theorem block_23_3 : isCompositeBlock 23 3 := by
  sorry

-- 90, 91, 92, 93, 94, 95 are all composite (n = 89, k = 6)
theorem block_89_6 : isCompositeBlock 89 6 := by
  sorry

/-
## Prime Divisibility Facts

These support the concrete Grimm examples.
-/

-- 2 divides 24
theorem two_dvd_24 : 2 ∣ 24 := by sorry

-- 5 divides 25
theorem five_dvd_25 : 5 ∣ 25 := by sorry

-- 13 divides 26
theorem thirteen_dvd_26 : 13 ∣ 26 := by sorry

-- The primes 2, 5, 13 are pairwise distinct
theorem primes_2_5_13_distinct : (2 : ℕ) ≠ 5 ∧ (2 : ℕ) ≠ 13 ∧ (5 : ℕ) ≠ 13 := by
  sorry

/-
## k = 1 Support: Prime Divisors of Composites
-/

-- Any composite number has a prime divisor
theorem composite_has_prime_dvd (n : ℕ) (hn : n > 1) (hnotprime : ¬n.Prime) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n := by
  sorry

-- Consecutive integers are coprime: gcd(n, n+1) = 1
theorem consecutive_coprime (n : ℕ) : Nat.Coprime n (n + 1) := by
  sorry

-- Coprime numbers have no common prime divisors
theorem coprime_disjoint_primes (a b : ℕ) (h : Nat.Coprime a b)
    (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) : False := by
  sorry

end Erdos375Aristotle
