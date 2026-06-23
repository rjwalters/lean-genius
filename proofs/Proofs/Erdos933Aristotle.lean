/-
  Aristotle targets for Erdős Problem #933
  Routine supporting lemmas for automated proof search.
  See Erdos933Problem.lean for the main formalization.

  Criteria for inclusion:
  - power2_consecutive, power3_consecutive: factorization of n*(n+1) decomposes by
    Nat.factorization_mul, routine application
  - steinerbergerN_ne_zero, steinerberger_factorization_2: basic properties of
    the sequence 2^(3^r), follows from pow_ne_zero and Nat.factorization_pow
  - factorization_succ_ne_zero: n+1 ≠ 0 for all n, trivial
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos933Aristotle

open Nat

/-- The Steinerberger construction sequence: n = 2^{3^r}. -/
def steinerbergerN (r : ℕ) : ℕ := 2 ^ (3 ^ r)

-- Routine: steinerbergerN r ≠ 0 for all r.
-- 2^(3^r) is always positive.
theorem steinerbergerN_ne_zero (r : ℕ) : steinerbergerN r ≠ 0 := by
  sorry

-- Routine: n + 1 ≠ 0 for all n : ℕ.
-- Successor of a natural number is never zero.
theorem succ_ne_zero' (n : ℕ) : n + 1 ≠ 0 := by
  sorry

-- Routine: factorization of n*(n+1) at prime 2 equals sum of factorizations.
-- Follows from Nat.factorization_mul applied to n and n+1 (both nonzero for n ≥ 1),
-- and the case n = 0 is trivial by simp.
theorem power2_consecutive (n : ℕ) :
    (n * (n + 1)).factorization 2 =
      n.factorization 2 + (n + 1).factorization 2 := by
  sorry

-- Routine: factorization of n*(n+1) at prime 3 equals sum of factorizations.
-- Same argument as power2_consecutive with prime 3.
theorem power3_consecutive (n : ℕ) :
    (n * (n + 1)).factorization 3 =
      n.factorization 3 + (n + 1).factorization 3 := by
  sorry

-- Routine: factorization of a*b at any prime p equals sum, when a ≠ 0 and b ≠ 0.
-- Direct application of Nat.factorization_mul.
theorem factorization_mul_apply (a b p : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization p = a.factorization p + b.factorization p := by
  sorry

-- Routine: For r ≥ 1, 3^r ≥ 1.
-- Power of 3 is at least 1.
theorem three_pow_pos (r : ℕ) (hr : r ≥ 1) : 3 ^ r ≥ 1 := by
  sorry

-- Routine: steinerbergerN r = 2^(3^r), so its factorization at 2 is 3^r.
-- Since 2 is prime and 2^k has factorization k at prime 2.
theorem steinerberger_factorization_2 (r : ℕ) :
    (steinerbergerN r).factorization 2 = 3 ^ r := by
  sorry

-- Routine: 0 * (0 + 1) = 0, so factorization at any prime is 0.
-- Base case used in power2_consecutive and power3_consecutive.
theorem factorization_zero_mul_succ (p : ℕ) :
    (0 * (0 + 1)).factorization p = 0 := by
  sorry

end Erdos933Aristotle
