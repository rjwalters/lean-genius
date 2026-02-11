import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

-- Test what's available for absorption identity
#check @Nat.succ_mul_choose_eq
-- Nat.succ_mul_choose_eq : (n + 1) * Nat.choose (n + 1) (k + 1) = Nat.choose n k * (k + 1) + ...
-- No wait, let me just check the type

-- Also check add_one_mul_choose_eq
#check @Nat.add_one_mul_choose_eq

-- Test: the identity (a+b) | a * C(a+b, a)
-- Approach via succ_mul_choose_eq:
-- succ_mul_choose_eq says (n+1) * C(n+1, k+1) = ... but let me build
-- The absorption identity: (n+1) * C(n, k) = (k+1) * C(n+1, k+1)

example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (a + b) * (a + b - 1).choose (a - 1) = a * (a + b).choose a := by
  -- Use Nat.succ_mul_choose_eq or add_one_mul_choose_eq
  have h1 : a + b = (a + b - 1) + 1 := by omega
  have h2 : a = (a - 1) + 1 := by omega
  rw [h1, h2]
  -- Now we have ((a+b-1)+1) * C(a+b-1, a-1) = ((a-1)+1) * C((a+b-1)+1, (a-1)+1)
  -- This should match Nat.add_one_mul_choose_eq
  rw [Nat.add_one_mul_choose_eq]
