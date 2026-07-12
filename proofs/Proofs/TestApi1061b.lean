-- Test API availability for erdos-1061 multiplicativity approach
import Mathlib
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic

open Nat BigOperators Finset ArithmeticFunction

-- Test that isMultiplicative_sigma is available
#check ArithmeticFunction.IsMultiplicative
#check isMultiplicative_sigma

-- Test sigma_apply
#check ArithmeticFunction.sigma

-- Test that we can state and use multiplicativity
example : ArithmeticFunction.IsMultiplicative (σ 1) := isMultiplicative_sigma

-- Test Nat.Coprime API
#check Nat.Coprime
#check Nat.Prime.coprime_iff_not_dvd

-- Test divisors of prime
#check Nat.divisors_prime_eq

-- Test multiplicative application
example (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : Nat.Coprime m n) :
    (σ 1) (m * n) = (σ 1) m * (σ 1) n :=
  ArithmeticFunction.IsMultiplicative.map_mul_of_coprime isMultiplicative_sigma hmn
