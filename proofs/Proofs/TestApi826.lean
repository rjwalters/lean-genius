import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open scoped ArithmeticFunction
open Nat

-- Check: σ 0 for specific values
example : σ 0 1 = 1 := by native_decide
example : σ 0 2 = 2 := by native_decide
example : σ 0 6 = 4 := by native_decide
example : σ 0 12 = 6 := by native_decide

-- Check sigma_apply exists
#check ArithmeticFunction.sigma_apply
#check Nat.divisors
#check Nat.primeFactors

-- Simple individual checks
example : σ 0 (0 + 1) ≤ 2 * 1 := by native_decide
example : σ 0 (0 + 2) ≤ 2 * 2 := by native_decide
example : σ 0 (0 + 6) ≤ 2 * 6 := by native_decide
