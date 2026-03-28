/-
  Erdős Problem #405: Factorial Plus Power Equals Prime Power

  Source: https://erdosproblems.com/405
  Status: SOLVED

  Statement:
  Let p be an odd prime. Is it true that the equation
    (p-1)! + a^{p-1} = p^k
  has only finitely many solutions?

  Answer: YES. Yu-Liu (1996) found ALL solutions:
  - 2! + 1² = 3
  - 2! + 5² = 3³
  - 4! + 1⁴ = 5²

  Known Results:
  - Erdős-Graham: Conjectured finiteness; noted (p-1)! + a^{p-1} is rarely a power
  - Brindza-Erdős (1991): Proved finiteness
  - Yu-Liu (1996): Complete resolution — only 3 solutions exist

  Tags: number-theory, diophantine-equations, factorials
-/

import Mathlib

namespace Erdos405

open Nat

/-
## Part 1: Basic Definitions

The Diophantine equation (p-1)! + a^{p-1} = p^k.
-/

/-- A solution to the equation (p-1)! + a^{p-1} = p^k -/
structure Solution where
  p : ℕ
  a : ℕ
  k : ℕ
  p_prime : Nat.Prime p
  p_odd : p ≥ 3
  equation : (p - 1).factorial + a ^ (p - 1) = p ^ k

/-- The set of all solutions -/
def AllSolutions : Set Solution :=
  { s : Solution | True }

/-- Check if (p, a, k) is a solution -/
def IsSolution (p a k : ℕ) : Prop :=
  Nat.Prime p ∧ p ≥ 3 ∧ (p - 1).factorial + a ^ (p - 1) = p ^ k

/-
## Part 2: The Three Known Solutions

Yu-Liu (1996) proved these are the ONLY solutions.
-/

/-- Solution 1: p = 3, a = 1, k = 1 (since 2! + 1² = 2 + 1 = 3 = 3¹) -/
theorem solution_1 : IsSolution 3 1 1 := by
  constructor
  · exact Nat.prime_three
  constructor
  · norm_num
  · -- 2! + 1^2 = 2 + 1 = 3 = 3^1
    norm_num

/-- Solution 2: p = 3, a = 5, k = 3 (since 2! + 5² = 2 + 25 = 27 = 3³) -/
theorem solution_2 : IsSolution 3 5 3 := by
  constructor
  · exact Nat.prime_three
  constructor
  · norm_num
  · -- 2! + 5^2 = 2 + 25 = 27 = 3^3
    norm_num

/-- Solution 3: p = 5, a = 1, k = 2 (since 4! + 1⁴ = 24 + 1 = 25 = 5²) -/
theorem solution_3 : IsSolution 5 1 2 := by
  constructor
  · exact Nat.prime_five
  constructor
  · norm_num
  · -- 4! + 1^4 = 24 + 1 = 25 = 5^2
    norm_num

/-- The complete list of solutions -/
def CompleteSolutionList : List (ℕ × ℕ × ℕ) :=
  [(3, 1, 1), (3, 5, 3), (5, 1, 2)]

/-
## Part 3: The Finiteness Results
-/

/-- Brindza-Erdős (1991): The set of solutions is finite -/
axiom brindza_erdos_1991 :
  { (p, a, k) : ℕ × ℕ × ℕ | IsSolution p a k }.Finite

/-- Yu-Liu (1996): Complete characterization -/
axiom yu_liu_1996 :
  ∀ p a k : ℕ, IsSolution p a k ↔
    (p = 3 ∧ a = 1 ∧ k = 1) ∨
    (p = 3 ∧ a = 5 ∧ k = 3) ∨
    (p = 5 ∧ a = 1 ∧ k = 2)

/-
## Part 4: Wilson's Theorem Connection

(p-1)! ≡ -1 (mod p) for prime p.
-/

/-- Wilson's theorem: (p-1)! ≡ p-1 ≡ -1 (mod p).
    Proved via Mathlib's ZMod.wilsons_lemma. -/
theorem wilson_theorem (p : ℕ) (hp : Nat.Prime p) :
    (p - 1).factorial % p = p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := ZMod.wilsons_lemma p
  -- h : ((p-1)! : ZMod p) = -1
  have hval := congr_arg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_neg_one'] at hval
  exact hval

/-- Fermat's little theorem: a^(p-1) ≡ 1 (mod p) when p ∤ a.
    Proved via Mathlib's ZMod.pow_card_sub_one_eq_one. -/
theorem fermat_little (p a : ℕ) (hp : Nat.Prime p) (ha : ¬p ∣ a) :
    a ^ (p - 1) % p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha_zmod : (a : ZMod p) ≠ 0 := by
    intro h; apply ha
    rwa [ZMod.natCast_eq_zero_iff] at h
  have hcard : p - 1 = Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card p]
  have key : ((a : ZMod p)) ^ (p - 1) = 1 := by
    rw [hcard]; exact ZMod.pow_card_sub_one_eq_one ha_zmod
  have h1 : ((a ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast; exact key
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp.one_lt] at h1

/-- Combined: (p-1)! + a^{p-1} ≡ -1 + 1 = 0 (mod p) if p ∤ a.
    Proved from Wilson's theorem and Fermat's little theorem. -/
theorem sum_divisible_by_p (p a : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (ha : ¬p ∣ a) :
    p ∣ (p - 1).factorial + a ^ (p - 1) := by
  have hw := wilson_theorem p hp
  have hf := fermat_little p a hp ha
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod, hw, hf]
  omega

/-
## Part 5: The Exceptional Case p ∣ a
-/

/-- If p ∣ a, then a^{p-1} ≡ 0 (mod p^{p-1}).
    Since p | a, we have a = p·m, so a^{p-1} = p^{p-1}·m^{p-1}. -/
theorem divisible_implies_large_power (p a : ℕ) (hp : Nat.Prime p) (ha : p ∣ a) :
    p ^ (p - 1) ∣ a ^ (p - 1) := by
  obtain ⟨m, rfl⟩ := ha
  rw [mul_pow]
  exact dvd_mul_right _ _

/-- When p ∣ a, the equation becomes (p-1)! ≡ p^k (mod p^{p-1}),
    which severely constrains k since v_p((p-1)!) = 0 for prime p. -/
axiom divisible_case_analysis (p a k : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3)
    (ha : p ∣ a) (heq : (p - 1).factorial + a ^ (p - 1) = p ^ k) :
    k ≤ p - 1

/-
## Part 6: p-adic Analysis

The p-adic valuation constrains solutions.
-/

/-- p-adic valuation of n! -/
noncomputable def factorialPadicVal (p n : ℕ) : ℕ :=
  (Finset.range n).sum fun i => n / p ^ (i + 1)

/-- Legendre's formula for v_p(n!).
    Proved from Mathlib's padicValNat_factorial by reindexing. -/
theorem legendre_formula (p n : ℕ) (hp : Nat.Prime p) :
    padicValNat p n.factorial = factorialPadicVal p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [factorialPadicVal]
  · have hlog : Nat.log p n < n + 1 := by
      rw [Nat.log_lt hp.one_lt hn]
      calc n < 2 ^ n := Nat.lt_two_pow n
        _ ≤ p ^ n := Nat.pow_le_pow_left hp.two_le n
        _ ≤ p ^ (n + 1) := Nat.pow_le_pow_right hp.pos (Nat.le_succ n)
    rw [padicValNat_factorial hlog, Finset.sum_Ico_eq_sum_range]
    unfold factorialPadicVal
    exact Finset.sum_congr (by omega) fun k _ => by rw [add_comm]

/-- For (p-1)!, the p-adic valuation is 0.
    Since (p-1)! is the product of {1,...,p-1}, none divisible by p. -/
theorem factorial_padic_zero (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    padicValNat p (p - 1).factorial = 0 := by
  rw [padicValNat.eq_zero_iff]
  right; right
  intro ⟨k, hk⟩
  -- p ∣ (p-1)! means some factor in 1..p-1 is divisible by p.
  -- But (p-1)! = ∏_{i=1}^{p-1} i, and for prime p, p ∤ i for 1 ≤ i ≤ p-1.
  have h_ne_zero : (p - 1).factorial ≠ 0 := Nat.factorial_pos _ |>.ne'
  have h_dvd : p ∣ (p - 1).factorial := ⟨k, hk⟩
  have h_not_dvd : ¬ p ∣ (p - 1).factorial := by
    rw [hp.dvd_factorial]
    omega
  exact h_not_dvd h_dvd

/-
## Part 7: Why Only These Solutions?

Analysis of why p ∈ {3, 5} are special.
-/

/-- For p = 3: 2! = 2, so need 2 + a² = 3^k -/
theorem p_equals_3_analysis :
    ∀ a k : ℕ, IsSolution 3 a k →
      (a = 1 ∧ k = 1) ∨ (a = 5 ∧ k = 3) := by
  intro a k h
  have := yu_liu_1996 3 a k
  rw [h] at this
  simp at this
  rcases this with ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ | ⟨hp, _, _⟩
  · left; exact ⟨ha, hk⟩
  · right; exact ⟨ha, hk⟩
  · norm_num at hp

/-- For p = 5: 4! = 24, so need 24 + a⁴ = 5^k -/
theorem p_equals_5_analysis :
    ∀ a k : ℕ, IsSolution 5 a k → a = 1 ∧ k = 2 := by
  intro a k h
  have := yu_liu_1996 5 a k
  rw [h] at this
  simp at this
  rcases this with ⟨hp, _, _⟩ | ⟨hp, _, _⟩ | ⟨_, ha, hk⟩
  · norm_num at hp
  · norm_num at hp
  · exact ⟨ha, hk⟩

/-
## Part 8: General Perfect Power Question

Erdős-Graham: Is (p-1)! + a^{p-1} rarely a perfect power?
-/

/-- (p-1)! + a^{p-1} equals a perfect power -/
def IsPerfectPower (n : ℕ) : Prop :=
  ∃ b k : ℕ, k ≥ 2 ∧ n = b ^ k

/-- Example: 6! + 2⁶ = 720 + 64 = 784 = 28² -/
theorem example_perfect_power :
    6.factorial + 2 ^ 6 = 28 ^ 2 := by
  norm_num

/-
## Part 9: Main Problem Statement
-/

/-- Erdős Problem #405: Complete statement -/
theorem erdos_405_statement :
    -- The equation has only finitely many solutions
    { (p, a, k) : ℕ × ℕ × ℕ | IsSolution p a k }.Finite ∧
    -- There are exactly 3 solutions
    (∀ p a k : ℕ, IsSolution p a k ↔
      (p = 3 ∧ a = 1 ∧ k = 1) ∨ (p = 3 ∧ a = 5 ∧ k = 3) ∨ (p = 5 ∧ a = 1 ∧ k = 2)) := by
  constructor
  · exact brindza_erdos_1991
  · exact yu_liu_1996

/-
## Part 10: Summary
-/

/-- Summary of Erdős Problem #405 -/
theorem erdos_405_summary :
    -- Three solutions exist
    IsSolution 3 1 1 ∧ IsSolution 3 5 3 ∧ IsSolution 5 1 2 ∧
    -- These are the only solutions
    (∀ p a k : ℕ, IsSolution p a k →
      (p = 3 ∧ a = 1 ∧ k = 1) ∨ (p = 3 ∧ a = 5 ∧ k = 3) ∨ (p = 5 ∧ a = 1 ∧ k = 2)) := by
  constructor
  · exact solution_1
  constructor
  · exact solution_2
  constructor
  · exact solution_3
  · intro p a k h
    exact (yu_liu_1996 p a k).mp h

/-- **Erdős Problem #405: SOLVED**
The equation (p-1)! + a^{p-1} = p^k has exactly 3 solutions:
(3,1,1), (3,5,3), (5,1,2). -/
theorem erdos_405 :
    { (p, a, k) : ℕ × ℕ × ℕ | IsSolution p a k }.Finite ∧
    (∀ p a k : ℕ, IsSolution p a k ↔
      (p = 3 ∧ a = 1 ∧ k = 1) ∨ (p = 3 ∧ a = 5 ∧ k = 3) ∨ (p = 5 ∧ a = 1 ∧ k = 2)) :=
  ⟨brindza_erdos_1991, yu_liu_1996⟩

end Erdos405
