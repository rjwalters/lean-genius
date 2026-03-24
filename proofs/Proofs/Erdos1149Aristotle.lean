/-
  Aristotle targets for Erdős Problem #1149
  Routine supporting lemmas for automated proof search.
  See Erdos1149Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (Bergelson-Richter theorem)
  - Known result likely in Mathlib (coprimality, divisor counting, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

open Finset BigOperators

namespace Erdos1149Aristotle

/-- The number of multiples of d in {1, ..., N} is ⌊N/d⌋.
    Standard number theory counting result. -/
theorem card_multiples (d N : ℕ) (hd : 0 < d) :
    (Finset.filter (fun a => d ∣ a) (Finset.Icc 1 N)).card = N / d := by
  sorry

/-- gcd(n, 1) = 1 for all n. -/
theorem gcd_one_right (n : ℕ) : Nat.gcd n 1 = 1 := by
  sorry

/-- gcd(1, n) = 1 for all n. -/
theorem gcd_one_left (n : ℕ) : Nat.gcd 1 n = 1 := by
  sorry

/-- Coprimality is symmetric: gcd(a,b) = 1 ↔ gcd(b,a) = 1. -/
theorem coprime_comm (a b : ℕ) : Nat.Coprime a b ↔ Nat.Coprime b a := by
  sorry

/-- For a prime p, gcd(a, b) divisible by p iff p | a and p | b. -/
theorem prime_dvd_gcd_iff (p a b : ℕ) (hp : Nat.Prime p) :
    p ∣ Nat.gcd a b ↔ p ∣ a ∧ p ∣ b := by
  sorry

/-- n and n are coprime iff n = 1. -/
theorem coprime_self_iff (n : ℕ) : Nat.Coprime n n ↔ n = 1 := by
  sorry

/-- If gcd(a,b) = 1 and c | a, then gcd(c,b) = 1. -/
theorem coprime_of_dvd_left (a b c : ℕ) (hab : Nat.Coprime a b) (hca : c ∣ a) :
    Nat.Coprime c b := by
  sorry

/-- 6/π² is positive. -/
theorem six_div_pi_sq_pos : (0 : ℝ) < 6 / Real.pi ^ 2 := by
  sorry

/-- 6/π² is less than 1. -/
theorem six_div_pi_sq_lt_one : 6 / Real.pi ^ 2 < (1 : ℝ) := by
  sorry

/-- π > 3 (used in bounding 6/π²). -/
theorem pi_gt_three : (3 : ℝ) < Real.pi := by
  sorry

/-- 6/π² = (π²/6)⁻¹ (reciprocal of Basel problem value). -/
theorem six_div_pi_sq_eq_inv : 6 / Real.pi ^ 2 = (Real.pi ^ 2 / 6)⁻¹ := by
  sorry

/-- Möbius function at 1 is 1. -/
theorem moebius_one : ArithmeticFunction.moebius 1 = 1 := by
  sorry

/-- Möbius function at a prime is -1. -/
theorem moebius_prime (p : ℕ) (hp : Nat.Prime p) :
    ArithmeticFunction.moebius p = -1 := by
  sorry

/-- |μ(n)| ≤ 1 for all n. -/
theorem abs_moebius_le_one (n : ℕ) :
    |ArithmeticFunction.moebius n| ≤ 1 := by
  sorry

end Erdos1149Aristotle
