/-
  Aristotle targets for Erdos674Problem
  Routine supporting lemmas for automated proof search.
  See Erdos674Problem.lean for the main formalization.
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Tactic

namespace Erdos674.Aristotle

open Nat

/-
  Ko's explicit values:
  koX = 2^12 * 3^6
  koY = 2^8 * 3^8
  koZ = 2^11 * 3^7
-/

def koX : ℕ := 2 ^ 12 * 3 ^ 6
def koY : ℕ := 2 ^ 8 * 3 ^ 8
def koZ : ℕ := 2 ^ 11 * 3 ^ 7

/-- koX > 0. -/
theorem koX_pos : koX > 0 := by sorry

/-- koY > 0. -/
theorem koY_pos : koY > 0 := by sorry

/-- koZ > 0. -/
theorem koZ_pos : koZ > 0 := by sorry

/-- Ko's family satisfies 4xy = z². -/
theorem ko_family_ratio : 4 * koX * koY = koZ ^ 2 := by sorry

/-- gcd(koX, koY) > 1 (they share factor 2 and 3). -/
theorem ko_gcd_gt_one : Nat.gcd koX koY > 1 := by sorry

/-- 2 divides koX. -/
theorem two_dvd_koX : 2 ∣ koX := by sorry

/-- 2 divides koY. -/
theorem two_dvd_koY : 2 ∣ koY := by sorry

/-- 2 divides koZ. -/
theorem two_dvd_koZ : 2 ∣ koZ := by sorry

/-- 3 divides koX. -/
theorem three_dvd_koX : 3 ∣ koX := by sorry

/-- 3 divides koY. -/
theorem three_dvd_koY : 3 ∣ koY := by sorry

/-- 3 divides koZ. -/
theorem three_dvd_koZ : 3 ∣ koZ := by sorry

/-- If gcd(x,y) > 1, then gcd(x,y) ≠ 1. -/
theorem gcd_gt_one_ne_one (x y : ℕ) (h : Nat.gcd x y > 1) : Nat.gcd x y ≠ 1 := by sorry

/-- x^x * y^y is symmetric under swapping x and y when applied pairwise. -/
theorem exp_self_mul_comm (x y : ℕ) : x ^ x * y ^ y = y ^ y * x ^ x := by sorry

/-- For any n ≥ 2, 2^(n+1) ≥ 4. -/
theorem pow_succ_ge_four (n : ℕ) (hn : n ≥ 2) : 2 ^ (n + 1) ≥ 4 := by sorry

/-- For any n ≥ 2, 2^n - 1 ≥ 3. -/
theorem pow_sub_one_ge_three (n : ℕ) (hn : n ≥ 2) : 2 ^ n - 1 ≥ 3 := by sorry

/-- For a, b > 1: (a*b)^(a*b) divides (a^a * b^b)^(a*b) is not generally true,
    but a^(a*b) * b^(a*b) = (a*b)^(a*b) simplifies. This helper. -/
theorem mul_pow_self (a b : ℕ) : (a * b) ^ (a * b) = a ^ (a * b) * b ^ (a * b) := by sorry

/-- Nat division helper: if 4 * a * b = c^2 and c > 0, then a * b > 0. -/
theorem pos_of_sq_eq (a b c : ℕ) (hc : c > 0) (h : 4 * a * b = c ^ 2) : a * b > 0 := by sorry

end Erdos674.Aristotle
