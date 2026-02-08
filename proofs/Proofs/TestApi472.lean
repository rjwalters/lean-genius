import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Parity

-- Test basic decidability for small prime checks
example : (3 : ℕ).Prime := by decide
example : (5 : ℕ).Prime := by decide

-- Test list membership
example : (3 : ℕ) ∈ [3, 5] := by decide
example : ∀ p ∈ [3, 5], (p : ℕ).Prime := by decide

-- Test Even/Odd
#check Nat.Even
#check Nat.even_add
#check Nat.Odd
#check Nat.Prime.eq_two_or_odd

-- Test natural number subtraction behavior
-- q + q - 1 where q ≥ 2: is 2q - 1 odd?
example : ¬ Even (3 + 3 - 1) := by decide
example : ¬ Even (5 + 5 - 1) := by decide

-- Test decidability for small Finset/List computations
#check List.ofFn
#check Nat.minFac
