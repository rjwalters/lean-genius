import Mathlib

-- Test: compositeness decidability (Nat.Composite was removed upstream in v4.31;
-- express "n is composite" faithfully as ¬ Nat.Prime n ∧ 2 ≤ n)
example : ¬ Nat.Prime 100 ∧ 2 ≤ (100 : ℕ) := by decide

-- Test: unfold factorial
example : Nat.factorial 4 = 24 := by native_decide
example : Nat.factorial 5 = 120 := by native_decide

-- Test: Set.Finite for finite enumeration
example : ∀ d ∈ ({1, 2, 6, 24} : Finset ℕ), ¬ Nat.Prime (101 - d) ∧ 2 ≤ (101 - d : ℕ) := by decide
