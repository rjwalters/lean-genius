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
theorem koX_pos : koX > 0 := by unfold koX; positivity

/-- koY > 0. -/
theorem koY_pos : koY > 0 := by unfold koY; positivity

/-- koZ > 0. -/
theorem koZ_pos : koZ > 0 := by unfold koZ; positivity

/-- Ko's family satisfies 4xy = z². -/
theorem ko_family_ratio : 4 * koX * koY = koZ ^ 2 := by unfold koX koY koZ; norm_num

/-- gcd(koX, koY) > 1 (they share factor 2 and 3). -/
theorem ko_gcd_gt_one : Nat.gcd koX koY > 1 := by unfold koX koY; native_decide

/-- 2 divides koX. -/
theorem two_dvd_koX : 2 ∣ koX := by unfold koX; exact ⟨2 ^ 11 * 3 ^ 6, by ring⟩

/-- 2 divides koY. -/
theorem two_dvd_koY : 2 ∣ koY := by unfold koY; exact ⟨2 ^ 7 * 3 ^ 8, by ring⟩

/-- 2 divides koZ. -/
theorem two_dvd_koZ : 2 ∣ koZ := by unfold koZ; exact ⟨2 ^ 10 * 3 ^ 7, by ring⟩

/-- 3 divides koX. -/
theorem three_dvd_koX : 3 ∣ koX := by unfold koX; exact ⟨2 ^ 12 * 3 ^ 5, by ring⟩

/-- 3 divides koY. -/
theorem three_dvd_koY : 3 ∣ koY := by unfold koY; exact ⟨2 ^ 8 * 3 ^ 7, by ring⟩

/-- 3 divides koZ. -/
theorem three_dvd_koZ : 3 ∣ koZ := by unfold koZ; exact ⟨2 ^ 11 * 3 ^ 6, by ring⟩

/-- If gcd(x,y) > 1, then gcd(x,y) ≠ 1. -/
theorem gcd_gt_one_ne_one (x y : ℕ) (h : Nat.gcd x y > 1) : Nat.gcd x y ≠ 1 := by omega

/-- x^x * y^y is symmetric under swapping x and y when applied pairwise. -/
theorem exp_self_mul_comm (x y : ℕ) : x ^ x * y ^ y = y ^ y * x ^ x := mul_comm _ _

/-- For any n ≥ 2, 2^(n+1) ≥ 4. -/
theorem pow_succ_ge_four (n : ℕ) (hn : n ≥ 2) : 2 ^ (n + 1) ≥ 4 := by
  calc 2 ^ (n + 1) ≥ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 8 := by norm_num
    _ ≥ 4 := by omega

/-- For any n ≥ 2, 2^n - 1 ≥ 3. -/
theorem pow_sub_one_ge_three (n : ℕ) (hn : n ≥ 2) : 2 ^ n - 1 ≥ 3 := by
  have h : 2 ^ n ≥ 4 := by
    calc 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hn
      _ = 4 := by norm_num
  omega

/-- (a*b)^(a*b) = a^(a*b) * b^(a*b) by Nat.mul_pow. -/
theorem mul_pow_self (a b : ℕ) : (a * b) ^ (a * b) = a ^ (a * b) * b ^ (a * b) :=
  Nat.mul_pow a b (a * b)

/-- Nat division helper: if 4 * a * b = c^2 and c > 0, then a * b > 0. -/
theorem pos_of_sq_eq (a b c : ℕ) (hc : c > 0) (h : 4 * a * b = c ^ 2) : a * b > 0 := by
  by_contra hab
  push_neg at hab
  interval_cases (a * b)
  simp at h; omega

end Erdos674.Aristotle
