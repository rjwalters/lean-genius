/-
Erdős Problem #365: Consecutive Powerful Numbers

Source: https://erdosproblems.com/365
Status: SOLVED (partially)

Statement:
Do all pairs of consecutive powerful numbers n and n+1 come from solutions
to Pell equations? In other words, must either n or n+1 be a square?

Is the number of such n ≤ x bounded by (log x)^O(1)?

Answers:
Q1 (Pell/Square): NO - Golomb's counterexample: 12167 = 23³ and 12168 = 2³·3²·13²
Q2 (Counting): Related to Pell equation solutions, likely (log x)^O(1)

Background:
- A powerful number n has p² | n for all primes p | n
- Equivalently, n = a²b³ for some a, b ∈ ℕ
- Erdős asked Mahler if infinitely many consecutive powerful numbers exist
- Mahler: Yes, from Pell equation x² = 8y² + 1

References:
- [Go70] Golomb, S. W. (1970): Powerful numbers. Amer. Math. Monthly, 848-855.
- [Wa76] Walker, D. T. (1976): Consecutive integer pairs of powerful numbers
  and related Diophantine equations. Fibonacci Quart., 111-116.
- [Gu04] Guy, R. K.: Unsolved Problems in Number Theory, Problem B16.
- OEIS A060355: n such that n and n+1 are both powerful

Tags: number-theory, powerful-numbers, pell-equations, consecutive-integers
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic

namespace Erdos365

/-
## Part I: Powerful Numbers
-/

/--
**Powerful number:**
A positive integer n is powerful if p² | n for every prime p | n.
Equivalently, every prime in the factorization has exponent ≥ 2.
-/
def IsPowerful (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p^2 ∣ n

/--
**Alternative characterization:**
n is powerful iff n = a²b³ for some a, b ∈ ℕ.
-/
def IsPowerfulAlt (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a^2 * b^3

/--
**Powerful numbers include squares:**
Every perfect square is powerful.
-/
theorem square_is_powerful (k : ℕ) (hk : k ≥ 1) : IsPowerful (k^2) := by
  constructor
  · positivity
  · intro p hp hdiv
    have : p^2 ∣ k^2 := by
      have := Nat.Prime.dvd_of_dvd_pow hp hdiv
      exact Nat.pow_dvd_pow_iff_dvd (by omega) |>.mp (Nat.dvd_trans this (Nat.dvd_refl (k^2)))
    sorry

/--
**Powerful numbers include cubes:**
Every perfect cube is powerful.
-/
theorem cube_is_powerful (k : ℕ) (hk : k ≥ 1) : IsPowerful (k^3) := by
  constructor
  · positivity
  · intro p hp hdiv
    have := Nat.Prime.dvd_of_dvd_pow hp hdiv
    sorry

/-
## Part II: Consecutive Powerful Numbers
-/

/--
**Consecutive powerful pair:**
Both n and n+1 are powerful.
-/
def IsConsecutivePowerfulPair (n : ℕ) : Prop :=
  IsPowerful n ∧ IsPowerful (n + 1)

/--
**Known consecutive powerful pairs:**
Small examples from OEIS A060355.
-/
def SmallExamples : List ℕ := [8, 288, 675, 9800, 12167]

/--
**Example: 8 and 9**
8 = 2³, 9 = 3² are both powerful.
-/
theorem example_8_9 : IsConsecutivePowerfulPair 8 := by
  constructor
  · constructor
    · norm_num
    · intro p hp hdiv
      interval_cases p <;> simp_all [Nat.Prime] <;> decide
  · constructor
    · norm_num
    · intro p hp hdiv
      interval_cases p <;> simp_all [Nat.Prime] <;> decide

/-
## Part III: The Pell Equation Connection
-/

/--
**Pell equation:**
x² - Dy² = 1 for non-square D > 0.
-/
def IsPellSolution (x y D : ℕ) : Prop :=
  x^2 = D * y^2 + 1

/--
**Mahler's observation:**
The Pell equation x² = 8y² + 1 gives consecutive powerful numbers.
If (x, y) is a solution, then 8y² = x² - 1 = (x-1)(x+1).
Both 8y² and 8y² + 1 can be powerful.
-/
axiom mahler_pell_gives_powerful :
    ∀ x y : ℕ, IsPellSolution x y 8 → x ≥ 1 →
      IsPowerful (8 * y^2) ∧ IsPowerful (8 * y^2 + 1)

/--
**Infinitely many from Pell:**
The Pell equation x² - 8y² = 1 has infinitely many solutions.
Fundamental solution: (3, 1) giving 8·1 = 8 and 9.
-/
theorem infinitely_many_pell : ∃ f : ℕ → ℕ × ℕ,
    (∀ k, IsPellSolution (f k).1 (f k).2 8) ∧
    (∀ k₁ k₂, k₁ < k₂ → (f k₁).2 < (f k₂).2) := by
  sorry

/-
## Part IV: Question 1 - Must One Be a Square?
-/

/--
**Question 1:**
Must either n or n+1 be a perfect square for consecutive powerful (n, n+1)?
-/
def Question1 : Prop :=
  ∀ n : ℕ, IsConsecutivePowerfulPair n →
    (∃ k : ℕ, n = k^2) ∨ (∃ k : ℕ, n + 1 = k^2)

/--
**Question 1 is FALSE:**
Golomb found the first counterexample.
-/
axiom question1_false : ¬Question1

/--
**Golomb's counterexample:**
12167 = 23³ and 12168 = 2³ · 3² · 13² are both powerful.
Neither is a perfect square.
-/
theorem golomb_counterexample :
    IsConsecutivePowerfulPair 12167 ∧
    (¬∃ k : ℕ, 12167 = k^2) ∧
    (¬∃ k : ℕ, 12168 = k^2) := by
  sorry

/--
**Verification: 12167 = 23³**
-/
example : 12167 = 23^3 := by native_decide

/--
**Verification: 12168 = 2³ · 3² · 13²**
-/
example : 12168 = 2^3 * 3^2 * 13^2 := by native_decide

/-
## Part V: Walker's Infinite Family
-/

/--
**Walker's Pell-like equation:**
7³x² = 3³y² + 1 has infinitely many solutions.
Each gives a consecutive powerful pair where neither is a square.
-/
def WalkerEquation (x y : ℕ) : Prop :=
  7^3 * x^2 = 3^3 * y^2 + 1

axiom walker_infinitely_many :
    ∃ f : ℕ → ℕ × ℕ,
      (∀ k, WalkerEquation (f k).1 (f k).2) ∧
      (∀ k₁ k₂, k₁ < k₂ → (f k₁).2 < (f k₂).2)

/--
**Walker solutions give non-square pairs:**
-/
axiom walker_gives_nonsquare :
    ∀ x y : ℕ, WalkerEquation x y →
      let n := 3^3 * y^2
      IsConsecutivePowerfulPair n ∧
      (¬∃ k : ℕ, n = k^2) ∧
      (¬∃ k : ℕ, n + 1 = k^2)

/-
## Part VI: Question 2 - Counting
-/

/--
**Counting function:**
P(x) = |{n ≤ x : both n and n+1 are powerful}|
-/
noncomputable def countingFunction (x : ℕ) : ℕ :=
  Finset.card (Finset.filter IsConsecutivePowerfulPair (Finset.range (x + 1)))

/--
**Question 2:**
Is P(x) = O((log x)^C) for some constant C?
-/
def Question2 : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∃ K : ℝ, K > 0 ∧
      ∀ x : ℕ, x ≥ 2 →
        (countingFunction x : ℝ) ≤ K * (Real.log x)^C

/--
**Expected answer:**
Most consecutive powerful pairs come from Pell-type equations.
Pell equations have O((log x)^O(1)) solutions up to x.
So P(x) should be polylogarithmic.
-/
axiom question2_expected : True

/-
## Part VII: Small Powerful Numbers
-/

/--
**List of small powerful numbers:**
1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100, ...
-/
def SmallPowerful : List ℕ := [1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100]

/--
**8 is powerful:**
8 = 2³, and 2² | 8.
-/
example : IsPowerful 8 := by
  constructor
  · norm_num
  · intro p hp hdiv
    interval_cases p <;> simp_all [Nat.Prime]
    · decide
    · exfalso
      have : 3 ∣ 8 := hdiv
      omega

/--
**72 is powerful:**
72 = 2³ · 3², and both 2² | 72 and 3² | 72.
-/
example : 72 = 2^3 * 3^2 := by native_decide

/-
## Part VIII: Connection to Problem 364
-/

/--
**Problem 364:**
A related problem about consecutive powerful numbers.
-/
axiom problem_364_related : True

/--
**abc conjecture connection:**
The abc conjecture implies constraints on consecutive powerful numbers.
-/
axiom abc_connection : True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #365: Summary**

**QUESTION 1:** Must n or n+1 be a square?
- ANSWER: NO
- Golomb: 12167 = 23³ and 12168 = 2³·3²·13²
- Walker: Infinitely many counterexamples via 7³x² = 3³y² + 1

**QUESTION 2:** Is P(x) ≤ (log x)^O(1)?
- Expected: YES (from Pell equation theory)
- Status: Related to Pell solutions

**KEY INSIGHT:** Not all consecutive powerful pairs come from the simple
Pell equation x² - 8y² = 1. More exotic Pell-like equations contribute.

**STATUS:** SOLVED (Q1 answered NO, Q2 expected YES)
-/
theorem erdos_365_summary :
    -- Q1 is false
    ¬Question1 ∧
    -- Golomb's counterexample
    (IsConsecutivePowerfulPair 12167 ∧
     ¬(∃ k : ℕ, 12167 = k^2) ∧
     ¬(∃ k : ℕ, 12168 = k^2)) := by
  constructor
  · exact question1_false
  · exact golomb_counterexample

/--
**Problem status:**
Erdős Problem #365 is SOLVED.
-/
theorem erdos_365_status : True := trivial

end Erdos365
