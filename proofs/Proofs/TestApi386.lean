import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

-- Test: Nat.choose values
example : Nat.choose 21 2 = 210 := by native_decide
example : Nat.choose 7 3 = 35 := by native_decide
example : Nat.choose 10 4 = 210 := by native_decide
example : Nat.choose 14 4 = 1001 := by native_decide
example : Nat.choose 15 6 = 5005 := by native_decide

-- Test: products match
example : 2 * 3 * 5 * 7 = 210 := by native_decide
example : 5 * 7 = 35 := by native_decide
example : 7 * 11 * 13 = 1001 := by native_decide
example : 5 * 7 * 11 * 13 = 5005 := by native_decide

-- Test: Combined - choose equals product of consecutive primes
example : Nat.choose 21 2 = 2 * 3 * 5 * 7 := by native_decide
example : Nat.choose 7 3 = 5 * 7 := by native_decide
example : Nat.choose 10 4 = 2 * 3 * 5 * 7 := by native_decide
example : Nat.choose 14 4 = 7 * 11 * 13 := by native_decide
example : Nat.choose 15 6 = 5 * 7 * 11 * 13 := by native_decide
