/-
Erdős Problem #1055: Erdős-Selfridge Prime Classification

**Statement**: Define prime classification recursively:
- Class 1: Primes p where all prime divisors of p+1 are 2 or 3
- Class r: Primes p where all prime factors of p+1 are in class ≤ r-1,
           with at least one factor in class r-1

Questions:
1. Are there infinitely many primes in each class?
2. If p_r is the least prime in class r, how does p_r^(1/r) behave?

**Status**: OPEN

**Known Results**:
- The sequence p_r begins: 2, 13, 37, 73, 1021 (OEIS A005113)
- Number of class r primes ≤ n is at most n^o(1)
- Erdős believed p_r^(1/r) → ∞
- Selfridge thought it might be bounded

**Variant**: Same question with p-1 instead of p+1

Reference: https://erdosproblems.com/1055
Problem A18 in Guy's "Unsolved Problems in Number Theory"
-/

import Mathlib

open Nat BigOperators Finset

namespace Erdos1055

/-
## Part I: The Classification
-/

/-- Primes of class 0: just 2 and 3 (the base primes). -/
def IsClass0 (p : ℕ) : Prop := p = 2 ∨ p = 3

/-- A prime p is in class r (inductively defined).
    Class 1: all prime factors of p+1 are 2 or 3
    Class r: all prime factors of p+1 are in class ≤ r-1, with max = r-1 -/
def PrimeClass : ℕ → ℕ → Prop
  | 0, p => IsClass0 p
  | r + 1, p =>
      p.Prime ∧
      (∀ q : ℕ, q.Prime → q ∣ (p + 1) → ∃ s ≤ r, PrimeClass s q) ∧
      (∃ q : ℕ, q.Prime ∧ q ∣ (p + 1) ∧ PrimeClass r q)

/-- Class 1 primes: p+1 only has factors 2 and 3.
    Equivalently, p+1 = 2^a · 3^b for some a, b ≥ 0. -/
def IsClass1 (p : ℕ) : Prop :=
  p.Prime ∧ ∀ q : ℕ, q.Prime → q ∣ (p + 1) → q = 2 ∨ q = 3

/-- The class of a prime (the smallest r such that p is in class r). -/
noncomputable def classOf (p : ℕ) (hp : p.Prime) : ℕ :=
  Nat.find (⟨p, by sorry⟩ : ∃ r, PrimeClass r p)

/-
## Part II: Known Small Values
-/

/-- 2 is the smallest class 1 prime (2+1 = 3 = 3^1). -/
theorem class1_2 : IsClass1 2 := by
  constructor
  · exact Nat.prime_two
  · intro q hq hdiv
    interval_cases q <;> simp_all

/-- 5 is a class 1 prime (5+1 = 6 = 2·3). -/
theorem class1_5 : IsClass1 5 := by
  constructor
  · exact Nat.prime_five
  · intro q hq hdiv
    have : q ∣ 6 := hdiv
    interval_cases q <;> simp_all

/-- 13 is the smallest class 2 prime.
    13+1 = 14 = 2·7, and 7 is class 1 (7+1 = 8 = 2^3). -/
axiom class2_13 : PrimeClass 2 13 ∧ ∀ p < 13, p.Prime → ¬PrimeClass 2 p

/-- The sequence p_r of least primes in class r. -/
noncomputable def p : ℕ → ℕ
  | 0 => 2  -- smallest "base" prime
  | 1 => 2  -- smallest class 1 prime
  | 2 => 13
  | 3 => 37
  | 4 => 73
  | 5 => 1021
  | _ => 0  -- placeholder for unknown values

/-- OEIS A005113: Smallest prime of Erdős-Selfridge class n+1. -/
axiom oeis_A005113 : p 1 = 2 ∧ p 2 = 13 ∧ p 3 = 37 ∧ p 4 = 73 ∧ p 5 = 1021

/-
## Part III: The Main Questions
-/

/-- Question 1: Are there infinitely many primes in each class? -/
def infinitelyManyInEachClass : Prop :=
  ∀ r ≥ 1, Set.Infinite {p : ℕ | PrimeClass r p}

/-- Question 2a (Erdős): Does p_r^(1/r) → ∞? -/
def erdosConjecture : Prop :=
  ∀ M : ℝ, ∃ R : ℕ, ∀ r ≥ R, (p r : ℝ) ^ (1 / r : ℝ) > M

/-- Question 2b (Selfridge): Is p_r^(1/r) bounded? -/
def selfridgeConjecture : Prop :=
  ∃ M : ℝ, ∀ r ≥ 1, (p r : ℝ) ^ (1 / r : ℝ) < M

/-- The conjectures are mutually exclusive. -/
theorem conjectures_exclusive : ¬(erdosConjecture ∧ selfridgeConjecture) := by
  intro ⟨hE, hS⟩
  obtain ⟨M, hM⟩ := hS
  obtain ⟨R, hR⟩ := hE M
  have h1 := hR R (le_refl R)
  have h2 := hM R (by omega)
  linarith

/-
## Part IV: Known Bounds
-/

/-- The count of class r primes ≤ n is at most n^o(1).
    More precisely: #{p ≤ n : p in class r} ≤ n^ε for any ε > 0 (eventually). -/
axiom class_count_subpolynomial (r : ℕ) (hr : r ≥ 1) :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    ({p : ℕ | p.Prime ∧ p ≤ n ∧ PrimeClass r p}.ncard : ℝ) ≤ (n : ℝ) ^ ε

/-- A rough lower bound: p_r ≥ 2^r for r ≥ 1. -/
theorem p_lower_bound (r : ℕ) (hr : r ≥ 1) : p r ≥ 2 ^ r := by
  sorry

/-- Verification for small cases. -/
example : (p 1 : ℝ) ^ (1/1 : ℝ) = 2 := by norm_num [p]
example : (p 2 : ℝ) ^ (1/2 : ℝ) = Real.sqrt 13 := by simp [p]; ring
-- √13 ≈ 3.6, and 73^(1/4) ≈ 2.9, so the sequence oscillates

/-
## Part V: The p-1 Variant
-/

/-- Same classification but using p-1 instead of p+1. -/
def PrimeClassMinus : ℕ → ℕ → Prop
  | 0, p => IsClass0 p
  | r + 1, p =>
      p.Prime ∧
      (∀ q : ℕ, q.Prime → q ∣ (p - 1) → ∃ s ≤ r, PrimeClassMinus s q) ∧
      (∃ q : ℕ, q.Prime ∧ q ∣ (p - 1) ∧ PrimeClassMinus r q)

/-- The p-1 variant has similar open questions. -/
def pMinus1Variant : Prop :=
  ∀ r ≥ 1, Set.Infinite {p : ℕ | PrimeClassMinus r p}

/-
## Part VI: Summary
-/

/-- Erdős Problem #1055: Summary

    **Classification**: Primes classified by the "depth" of factors of p+1.
    - Class 1: p+1 only has factors 2, 3
    - Class r: p+1 factors are in classes ≤ r-1, with max = r-1

    **Sequence**: p_r = 2, 13, 37, 73, 1021, ...

    **Open Questions**:
    1. Infinitely many primes in each class?
    2. p_r^(1/r) → ∞ (Erdős) or bounded (Selfridge)?

    **Known**: Class r primes ≤ n number at most n^o(1). -/
theorem erdos_1055_summary :
    -- The classification is well-defined
    (∀ p : ℕ, p.Prime → ∃! r, PrimeClass r p) ∧
    -- p_r grows
    (p 1 < p 2 ∧ p 2 < p 3 ∧ p 3 < p 4 ∧ p 4 < p 5) := by
  constructor
  · sorry  -- Uniqueness of classification
  · simp only [p]
    omega

end Erdos1055
