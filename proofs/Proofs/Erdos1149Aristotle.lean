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
  -- Bijection: multiples of d in [1,N] ↔ [1, N/d] via a ↦ a/d
  rw [show N / d = (Finset.Icc 1 (N / d)).card from by simp [Finset.card_Icc]]
  apply Finset.card_nbij (fun a => a / d)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    simp only [Finset.mem_Icc]
    obtain ⟨⟨ha1, haN⟩, hd_dvd⟩ := ha
    constructor
    · exact Nat.one_le_div_of_dvd (by omega) hd_dvd
    · exact Nat.div_le_div_right haN
  · intro a₁ ha₁ a₂ ha₂ h
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
    obtain ⟨_, hd₁⟩ := ha₁; obtain ⟨_, hd₂⟩ := ha₂
    exact Nat.eq_of_dvd_of_div_eq_div hd hd₁ hd₂ h
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    exact ⟨d * k, by simp [Finset.mem_filter, Finset.mem_Icc, Nat.mul_div_cancel_left _ hd]; omega,
           Nat.mul_div_cancel_left k hd⟩

/-- gcd(n, 1) = 1 for all n. -/
theorem gcd_one_right (n : ℕ) : Nat.gcd n 1 = 1 :=
  Nat.gcd_one_right n

/-- gcd(1, n) = 1 for all n. -/
theorem gcd_one_left (n : ℕ) : Nat.gcd 1 n = 1 :=
  Nat.gcd_one_left n

/-- Coprimality is symmetric: gcd(a,b) = 1 ↔ gcd(b,a) = 1. -/
theorem coprime_comm (a b : ℕ) : Nat.Coprime a b ↔ Nat.Coprime b a :=
  Nat.Coprime.comm

/-- For a prime p, gcd(a, b) divisible by p iff p | a and p | b. -/
theorem prime_dvd_gcd_iff (p a b : ℕ) (hp : Nat.Prime p) :
    p ∣ Nat.gcd a b ↔ p ∣ a ∧ p ∣ b := by
  constructor
  · exact fun h => ⟨dvd_trans h (Nat.gcd_dvd_left a b), dvd_trans h (Nat.gcd_dvd_right a b)⟩
  · exact fun ⟨ha, hb⟩ => Nat.dvd_gcd ha hb

/-- n and n are coprime iff n = 1. -/
theorem coprime_self_iff (n : ℕ) : Nat.Coprime n n ↔ n = 1 := by
  simp [Nat.Coprime, Nat.gcd_self]

/-- If gcd(a,b) = 1 and c | a, then gcd(c,b) = 1. -/
theorem coprime_of_dvd_left (a b c : ℕ) (hab : Nat.Coprime a b) (hca : c ∣ a) :
    Nat.Coprime c b :=
  Nat.Coprime.coprime_dvd_left hca hab

/-- 6/π² is positive. -/
theorem six_div_pi_sq_pos : (0 : ℝ) < 6 / Real.pi ^ 2 := by
  positivity

/-- 6/π² is less than 1. -/
-- π > 3 so π² > 9 > 6, hence 6/π² < 1
theorem six_div_pi_sq_lt_one : 6 / Real.pi ^ 2 < (1 : ℝ) := by
  rw [div_lt_one (by positivity)]
  calc (6 : ℝ) < 9 := by norm_num
    _ = 3 ^ 2 := by norm_num
    _ < Real.pi ^ 2 := by
        apply sq_lt_sq'
        · linarith [Real.pi_pos]
        · exact Real.pi_gt_three

/-- π > 3 (used in bounding 6/π²). -/
theorem pi_gt_three : (3 : ℝ) < Real.pi :=
  Real.pi_gt_three

/-- 6/π² = (π²/6)⁻¹ (reciprocal of Basel problem value). -/
theorem six_div_pi_sq_eq_inv : 6 / Real.pi ^ 2 = (Real.pi ^ 2 / 6)⁻¹ := by
  rw [inv_div]; ring

/-- Möbius function at 1 is 1. -/
theorem moebius_one : ArithmeticFunction.moebius 1 = 1 := by
  simp [ArithmeticFunction.moebius_apply_one]

/-- Möbius function at a prime is -1. -/
theorem moebius_prime (p : ℕ) (hp : Nat.Prime p) :
    ArithmeticFunction.moebius p = -1 :=
  ArithmeticFunction.moebius_apply_prime hp

/-- |μ(n)| ≤ 1 for all n. -/
theorem abs_moebius_le_one (n : ℕ) :
    |ArithmeticFunction.moebius n| ≤ 1 := by
  sorry -- Needs case analysis on squarefree/non-squarefree

end Erdos1149Aristotle
