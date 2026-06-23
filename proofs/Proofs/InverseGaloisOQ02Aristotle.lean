/-
  Aristotle targets for Inverse Galois OQ-02 (M₂₃)
  Routine supporting lemmas for automated proof search.
  See InverseGaloisOQ02.lean for the main formalization.

  Criteria for inclusion:
  - Generic Cauchy/Sylow applications: if p prime, p ∣ |G|, then G has element of order p
  - Divisibility facts for 10200960 = 2^7 · 3^2 · 5 · 7 · 11 · 23
  - Arithmetic facts: 2^7 = 128, primality checks
  - Excluded: M23_not_commutative, M23_commutator_eq_top, M23_not_solvable (complex group theory)
  - Excluded: M23_realizable_over_Q (open problem)
  - No axioms (M23 is not redeclared here; companion uses generic group lemmas)
  - No definition sorries
-/
import Mathlib

namespace InverseGaloisOQ02Aristotle

open Finset

-- Routine: 2^7 = 128.
theorem two_pow_seven : (2 : ℕ) ^ 7 = 128 := by
  sorry

-- Routine: 23 is prime.
theorem prime_23 : Nat.Prime 23 := by
  sorry

-- Routine: 2 is prime.
theorem prime_2 : Nat.Prime 2 := by
  sorry

-- Routine: 23 divides 10200960.
-- 10200960 = 2^7 · 3^2 · 5 · 7 · 11 · 23.
theorem dvd_23_10200960 : 23 ∣ 10200960 := by
  sorry

-- Routine: 2^7 divides 10200960.
-- 10200960 = 2^7 · 3^2 · 5 · 7 · 11 · 23.
theorem dvd_pow_2_7_10200960 : 2 ^ 7 ∣ 10200960 := by
  sorry

-- Routine: 2^8 does not divide 10200960.
-- The 2-adic valuation of 10200960 is exactly 7.
theorem not_dvd_pow_2_8_10200960 : ¬(2 ^ 8 ∣ (10200960 : ℕ)) := by
  sorry

-- Routine: For any finite group G, if p prime and p ∣ |G|, then G has element of order p.
-- This is Cauchy's theorem for finite groups.
theorem cauchy_element_of_order {G : Type*} [Group G] [Fintype G]
    {p : ℕ} (hp : Nat.Prime p) (hdvd : p ∣ Fintype.card G) :
    ∃ g : G, orderOf g = p := by
  sorry

-- Routine: factorization of 10200960 into prime factors.
-- 10200960 = 2^7 · 3^2 · 5 · 7 · 11 · 23.
theorem factorization_10200960 :
    (10200960 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23 := by
  sorry

-- Routine: the 2-adic valuation of 10200960 is 7.
-- Needed to determine the Sylow 2-subgroup order.
theorem factorization_2_10200960 :
    (10200960 : ℕ).factorization 2 = 7 := by
  sorry

-- Routine: 2^7 = 128 as a general fact about Nat.
theorem pow_2_7_eq_128 : (2 : ℕ) ^ 7 = 128 := by
  sorry

end InverseGaloisOQ02Aristotle
