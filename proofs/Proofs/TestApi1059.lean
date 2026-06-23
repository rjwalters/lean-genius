import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

-- Test: Nat.Composite decidability
example : (100 : ℕ).Composite := by decide

-- Test: unfold factorial
example : Nat.factorial 4 = 24 := by native_decide
example : Nat.factorial 5 = 120 := by native_decide

-- Test: Set.Finite for finite enumeration
example : ∀ d ∈ ({1, 2, 6, 24} : Finset ℕ), (101 - d : ℕ).Composite := by decide
