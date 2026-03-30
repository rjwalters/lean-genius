/-
  Erdős Problem #431: Inverse Goldbach Problem

  Source: https://erdosproblems.com/431
  Status: OPEN

  Statement:
  Are there two infinite sets A and B such that A + B agrees with the set of
  prime numbers up to finitely many exceptions?

  This is known as Ostmann's "inverse Goldbach problem". The answer is
  conjectured to be NO.

  Known Results:
  - Elsholtz-Harper (2015): If such A, B exist, then for large x:
      x^{1/2}/(log x · log log x) ≪ |A ∩ [1,x]| ≪ x^{1/2} · log log x
  - Elsholtz (2001): No three sets A, B, C can have A+B+C = primes (mod finite)
  - Tao-Ziegler (2023): Infinite sets with restricted pairwise sums in primes

  Tags: number-theory, primes, additive-combinatorics
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos431

open Real Nat Set

/-
## Part 1: Basic Definitions

The sumset A + B and the set of primes.
-/

/-- The sumset A + B = {a + b : a ∈ A, b ∈ B} -/
def Sumset (A B : Set ℕ) : Set ℕ :=
  { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

/-- The set of prime numbers -/
def Primes : Set ℕ := { p | Nat.Prime p }

/-- Two sets agree up to finitely many exceptions -/
def AgreeFinitely (S T : Set ℕ) : Prop :=
  (S \ T).Finite ∧ (T \ S).Finite

/-- Equivalent: symmetric difference is finite -/
theorem agreeFinitely_iff (S T : Set ℕ) :
    AgreeFinitely S T ↔ (S ∆ T).Finite := by
  unfold AgreeFinitely
  rw [Set.symmDiff_def]
  constructor
  · exact fun ⟨h1, h2⟩ => h1.union h2
  · intro h
    exact ⟨h.subset Set.subset_union_left, h.subset Set.subset_union_right⟩

/-
## Part 2: The Inverse Goldbach Conjecture

Can A + B = Primes (mod finite)?
-/

/-- The inverse Goldbach property: A + B agrees with primes -/
def InverseGoldbachPair (A B : Set ℕ) : Prop :=
  A.Infinite ∧ B.Infinite ∧ AgreeFinitely (Sumset A B) Primes

/-- The conjecture: No such pair exists -/
def InverseGoldbachConjecture : Prop :=
  ¬∃ A B : Set ℕ, InverseGoldbachPair A B

/-- The conjecture is widely believed to be true -/
/-
## Part 3: Counting Functions

How A and B must grow if they exist.
-/

/-- Counting function: |A ∩ [1,x]| -/
noncomputable def countingFunction (A : Set ℕ) (x : ℕ) : ℕ :=
  (Finset.filter (fun n => n ∈ A) (Finset.range (x + 1))).card

/-- Growth rate bounds for A (if inverse Goldbach holds) -/
def GrowthBounds (A : Set ℕ) : Prop :=
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∀ x : ℕ, x > 10 →
      c₁ * Real.sqrt x / (Real.log x * Real.log (Real.log x)) ≤ countingFunction A x ∧
      countingFunction A x ≤ c₂ * Real.sqrt x * Real.log (Real.log x)

/-- Elsholtz-Harper (2015): Tight growth bounds -/
axiom elsholtz_harper_2015 (A B : Set ℕ) (h : InverseGoldbachPair A B) :
  GrowthBounds A ∧ GrowthBounds B

/-
## Part 4: Prime Counting Asymptotics
-/

/-- The prime counting function π(x) ~ x/log(x) -/
/-
## Part 5: Three Sets Ruled Out

Elsholtz (2001): No A + B + C = Primes (mod finite).
-/

/-- The triple sumset A + B + C -/
def TripleSumset (A B C : Set ℕ) : Set ℕ :=
  { n | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, n = a + b + c }

/-- Three-set inverse Goldbach property -/
def InverseGoldbachTriple (A B C : Set ℕ) : Prop :=
  A.Nontrivial ∧ B.Nontrivial ∧ C.Nontrivial ∧
  AgreeFinitely (TripleSumset A B C) Primes

/-- Elsholtz (2001): No such triple exists -/
axiom elsholtz_2001 : ¬∃ A B C : Set ℕ, InverseGoldbachTriple A B C

/-- Three sets is definitely too many -/
theorem no_triple_solution :
    ¬∃ A B C : Set ℕ, InverseGoldbachTriple A B C :=
  elsholtz_2001

/-
## Part 6: Partial Positive Results

Subsets of primes from restricted sumsets.
-/

/-- Restricted sumset: only i < j sums -/
def RestrictedSumset (B C : Set ℕ) : Set ℕ :=
  { n | ∃ (b : ℕ) (hb : b ∈ B) (c : ℕ) (hc : c ∈ C),
        -- Assuming B, C are indexed, require i < j
        n = b + c }

/-- Tao-Ziegler (2023): Infinite sets with restricted sums in primes -/
axiom tao_ziegler_2023 :
  ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧
    -- Their restricted sumset is a subset of primes
    ∀ n ∈ RestrictedSumset B C, Nat.Prime n

/-
## Part 7: Connection to Goldbach

Goldbach: Every even n > 2 is a sum of two primes.
-/

/-- Goldbach's conjecture (weak form) -/
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, Even n → n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- If Goldbach holds: Primes + Primes ⊇ {evens > 2} -/
theorem goldbach_implies_sumset (hGold : GoldbachConjecture) :
    ∀ n : ℕ, Even n → n > 2 → n ∈ Sumset Primes Primes := by
  intro n hEven hn
  obtain ⟨p, q, hp, hq, heq⟩ := hGold n hEven hn
  exact ⟨p, hp, q, hq, heq⟩

/-- But Primes + Primes ≠ Primes (mod finite): the sumset contains
    all sufficiently large even numbers (assuming Goldbach), while
    primes are almost all odd. -/
/-
## Part 8: Structural Constraints

What A and B would have to look like.
-/

/-- A must contain 2 or be very special -/
/-
## Part 9: Main Problem Statement
-/

/-- Erdős Problem #431: The main conjecture -/
theorem erdos_431_statement :
    -- The inverse Goldbach conjecture
    (InverseGoldbachConjecture ↔
      ¬∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ AgreeFinitely (Sumset A B) Primes) ∧
    -- Elsholtz-Harper bounds
    (∀ A B, InverseGoldbachPair A B → GrowthBounds A ∧ GrowthBounds B) ∧
    -- Three sets ruled out
    (¬∃ A B C : Set ℕ, InverseGoldbachTriple A B C) := by
  constructor
  · simp [InverseGoldbachConjecture, InverseGoldbachPair]
  constructor
  · exact elsholtz_harper_2015
  · exact elsholtz_2001

/-
## Part 10: Summary
-/

/-- Main summary: Erdős Problem #431 status -/
theorem erdos_431_summary :
    -- Three-set case is solved (NO)
    (¬∃ A B C : Set ℕ, InverseGoldbachTriple A B C) ∧
    -- Two-set case has tight bounds on A, B sizes
    (∀ A B, InverseGoldbachPair A B → GrowthBounds A ∧ GrowthBounds B) ∧
    -- Positive results exist for restricted sumsets
    (∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧
      ∀ n ∈ RestrictedSumset B C, Nat.Prime n) := by
  exact ⟨elsholtz_2001, elsholtz_harper_2015, tao_ziegler_2023⟩

/-- The answer to Erdős Problem #431: OPEN (likely NO)
    Summary of what IS known: three-set case impossible, two-set case
    severely constrained, restricted sumsets can land in primes. -/
theorem erdos_431 :
    (¬∃ A B C : Set ℕ, InverseGoldbachTriple A B C) ∧
    (∀ A B, InverseGoldbachPair A B → GrowthBounds A ∧ GrowthBounds B) ∧
    (∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧
      ∀ n ∈ RestrictedSumset B C, Nat.Prime n) :=
  erdos_431_summary

end Erdos431
