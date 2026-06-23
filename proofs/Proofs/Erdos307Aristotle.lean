/-
  Aristotle targets for Erdős Problem #307: Prime Reciprocal Products
  Supporting lemmas for automated proof search.
  See Erdos307Problem.lean for the main formalization.

  This file provides routine supporting lemmas for two sorry-ed theorems:
  - prime_sets_disjoint: if P, Q are prime sets with product 1, P ∩ Q = ∅
  - prime_set_size_lower_bound: if P, Q are prime sets with product 1, |P ∪ Q| ≥ 60

  Included targets (7):
  1. reciprocalProduct_comm: commutativity of the product of reciprocal sums
  2. prime_inv_pos: 1/p > 0 for any prime p (in ℚ)
  3. prime_inv_le_half: 1/p ≤ 1/2 for any prime p (since p ≥ 2)
  4. reciprocalSum_nonneg: sum of reciprocals of a set of positive naturals is ≥ 0
  5. reciprocalSum_pos_of_prime_nonempty: sum > 0 for nonempty prime sets
  6. reciprocalProduct_factors_pos: if product = 1, both factors are > 0
  7. sum_first_58_primes_lt_two: Σ_{p ≤ 271} 1/p < 2 (concrete bound needed for size lower bound)

  Excluded (too deep for Aristotle):
  - prime_sets_disjoint: requires prime factorization uniqueness argument
  - prime_set_size_lower_bound: depends on prime_sets_disjoint (sorry)
-/
import Proofs.Erdos307Problem
import Mathlib

namespace Erdos307Aristotle

open Erdos307 BigOperators Finset

-- 1. Commutativity of the product of reciprocal sums.
-- Strategy: unfold reciprocalProduct and apply mul_comm.
theorem reciprocalProduct_comm (P Q : Finset ℕ) :
    reciprocalProduct P Q = reciprocalProduct Q P := by
  sorry

-- 2. For any prime p, its reciprocal 1/p is positive in ℚ.
-- Strategy: apply inv_pos.mpr, then Nat.cast_pos.mpr, then Nat.Prime.pos.
theorem prime_inv_pos (p : ℕ) (hp : Nat.Prime p) : (0 : ℚ) < (p : ℚ)⁻¹ := by
  sorry

-- 3. For any prime p (so p ≥ 2), we have 1/p ≤ 1/2 in ℚ.
-- Strategy: prime gives p ≥ 2, then use inv_le_inv_of_le or one_div_le_one_div_iff.
theorem prime_inv_le_half (p : ℕ) (hp : Nat.Prime p) : (p : ℚ)⁻¹ ≤ 1 / 2 := by
  sorry

-- 4. The reciprocal sum of a set of positive naturals is nonneg.
-- Strategy: apply Finset.sum_nonneg; intro n hn; exact le_of_lt (inv_pos.mpr (Nat.cast_pos.mpr (hn_pos n hn))).
theorem reciprocalSum_nonneg (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    0 ≤ reciprocalSum S := by
  sorry

-- 5. The reciprocal sum of a nonempty set of primes is strictly positive.
-- Strategy: apply Finset.sum_pos using prime_inv_pos; use Nonempty.
theorem reciprocalSum_pos_of_prime_nonempty (S : Finset ℕ)
    (hS : IsSetOfPrimes S) (hne : S.Nonempty) : 0 < reciprocalSum S := by
  sorry

-- 6. If the product of two reciprocal sums equals 1, then both factors are positive.
-- The product = 1 > 0, and both factors are nonneg (sums of positive terms for prime sets),
-- so positivity follows.
-- Strategy: from hPQ : reciprocalProduct P Q = 1, have product > 0, so both > 0.
theorem reciprocalProduct_factors_pos (P Q : Finset ℕ)
    (hP : IsSetOfPrimes P) (hQ : IsSetOfPrimes Q)
    (hPQ : reciprocalProduct P Q = 1)
    (hPne : P.Nonempty) (hQne : Q.Nonempty) :
    0 < reciprocalSum P ∧ 0 < reciprocalSum Q := by
  sorry

-- 7. The sum of reciprocals of all primes up to 271 (the 58th prime) is strictly less than 2.
-- This is the key concrete bound: we need ≥ 59 distinct primes for the sum to reach 2.
-- Strategy: native_decide or norm_num (exact rational arithmetic computation).
-- This bound supports prime_set_size_lower_bound: any 58-element prime set has sum < 2,
-- so if sum(P ∪ Q) ≥ 2, then |P ∪ Q| ≥ 59.
theorem sum_first_58_primes_lt_two :
    (∑ p in (Finset.range 272).filter Nat.Prime, (p : ℚ)⁻¹) < 2 := by
  sorry

end Erdos307Aristotle
