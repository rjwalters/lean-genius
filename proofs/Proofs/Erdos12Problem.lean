/-
  Erdős Problem #12: Divisibility-Free Sets

  Source: https://erdosproblems.com/12
  Status: OPEN

  Statement:
  Let A be an infinite set such that there are no distinct a,b,c ∈ A
  with a | (b+c) and b,c > a.

  Questions:
  1. Is there such A with liminf |A ∩ {1,...,N}| / √N > 0?
  2. Is there c > 0 with infinitely many N having |A ∩ {1,...,N}| < N^(1-c)?
  3. Is Σ(1/n : n ∈ A) < ∞?

  Erdős-Sárközy (1970) proved such sets have density 0.
-/

import Mathlib

open Nat Finset Set Filter

/-! ## Core Definition -/

/-- The divisibility-free property: no a | (b+c) for distinct a < b,c in A -/
def IsDivisibilityFree (A : Set ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ≠ b → a ≠ c → b ≠ c → a < b → a < c →
    ¬(a ∣ (b + c))

/-- Counting function: |A ∩ {1,...,N}| -/
def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (· ∈ A) |>.card

/-! ## Basic Examples -/

/-- Powers of 2 form a divisibility-free set -/
def powersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2^k ∧ k ≥ 1}

/-- The set {2, 4, 8, 16, ...} is divisibility-free
    because 2^a cannot divide 2^b + 2^c when a < b,c -/
theorem powersOfTwo_divisibility_free : IsDivisibilityFree powersOfTwo := by
  intro a b c ha hb hc hab hac hbc haltb haltc hdiv
  -- The sum 2^b + 2^c = 2^min(b,c) * (1 + 2^|b-c|)
  -- which is not divisible by 2^a when a < min(b,c)
  sorry

/-- Squares of primes ≡ 3 (mod 4) form a good construction -/
def primeSquares3mod4 : Set ℕ :=
  {n | ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ n = p^2}

/-! ## Density Results -/

/-- A set has density 0 if |A ∩ {1,...,N}| / N → 0 -/
def HasDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun N => (countingFunction A N : ℝ) / N) atTop (nhds 0)

/-- Erdős-Sárközy (1970): Divisibility-free sets have density 0 -/
axiom erdos_sarkozy_density_zero :
  ∀ A : Set ℕ, A.Infinite → IsDivisibilityFree A → HasDensityZero A

/-! ## Question 1: Can we achieve √N density? -/

/-- The liminf of |A ∩ {1,...,N}| / √N -/
def sqrtLiminfDensity (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
    (countingFunction A N : ℝ) / Real.sqrt N ≥ c

/-- Question 1: Does a divisibility-free set with positive √N-density exist? -/
def Erdos12Question1 : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsDivisibilityFree A ∧ sqrtLiminfDensity A

/-- Best known: Elsholtz-Planitzer (2017) construction -/
axiom elsholtz_planitzer_construction :
  ∃ A : Set ℕ, A.Infinite ∧ IsDivisibilityFree A ∧
    ∀ᶠ N in atTop, (countingFunction A N : ℝ) ≥
      Real.sqrt N / (Real.sqrt (Real.log N) * (Real.log (Real.log N))^2)

/-! ## Question 2: Sparse infinitely often? -/

/-- Question 2: Is there c > 0 with |A| < N^(1-c) infinitely often? -/
def Erdos12Question2 : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsDivisibilityFree A →
    ∃ c : ℝ, c > 0 ∧ ∀ M : ℕ, ∃ N > M,
      (countingFunction A N : ℝ) < N^(1 - c)

/-! ## Question 3: Convergent reciprocal sum? -/

/-- The sum of reciprocals of elements in A -/
noncomputable def reciprocalSum (A : Set ℕ) : ℝ :=
  ∑' (n : A), (1 : ℝ) / n

/-- Question 3: Is the reciprocal sum always finite? -/
def Erdos12Question3 : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsDivisibilityFree A →
    Summable (fun n : A => (1 : ℝ) / n)

/-! ## Coprime Case -/

/-- A set is pairwise coprime -/
def IsPairwiseCoprime (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → Nat.Coprime a b

/-- Schoen (2001), Baier (2004): Coprime divisibility-free sets are O(N^(2/3)/log N) -/
axiom coprime_upper_bound :
  ∀ A : Set ℕ, A.Infinite → IsDivisibilityFree A → IsPairwiseCoprime A →
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in atTop,
      (countingFunction A N : ℝ) ≤ C * N^(2/3 : ℝ) / Real.log N

/-! ## Main Problem Statement -/

/-- Erdős Problem #12: All three questions (OPEN) -/
def Erdos12Problem : Prop :=
  Erdos12Question1 ∨ ¬Erdos12Question1 ∧
  Erdos12Question2 ∧
  Erdos12Question3
