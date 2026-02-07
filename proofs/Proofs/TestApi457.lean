import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset

-- Test: product of positive terms is positive
#check Finset.prod_pos

-- Test: Nat.find properties
#check @Nat.find_spec
#check @Nat.find_min'

-- Test: Icc properties
#check Finset.mem_Icc

-- Test: divisibility in products
#check Finset.dvd_prod_of_mem

-- Test: Nat.exists_infinite_primes
#check Nat.exists_infinite_primes

-- Test: omega for modular arithmetic
example (n p : ℕ) (hp : p > 0) (h : n % p = 0) : p ∣ (n + p) := by
  rw [Nat.dvd_iff_mod_eq_zero]; omega

-- Test: dvd transitivity with product membership
example (s : Finset ℕ) (a b : ℕ) (ha : a ∈ s) (hab : b ∣ a) :
    b ∣ ∏ x ∈ s, x := by
  exact dvd_trans hab (Finset.dvd_prod_of_mem _ ha)
