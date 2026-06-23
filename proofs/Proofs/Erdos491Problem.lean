/-
  Erdős Problem #491: Characterization of Additive Functions with Bounded Differences

  Source: https://erdosproblems.com/491
  Status: SOLVED by Wirsing (1970)

  Statement:
  Let f: ℕ → ℝ be an additive function (f(ab) = f(a) + f(b) when gcd(a,b) = 1).
  If |f(n+1) - f(n)| < c for all n and some constant c, must there exist c'
  such that f(n) = c'·log(n) + O(1)?

  Background:
  Erdős (1946) proved weaker results:
  - If f(n+1) - f(n) = o(1), then f(n) = c·log(n)
  - If f(n+1) ≥ f(n), then f(n) = c·log(n)
  Wirsing (1970) proved the full conjecture affirmatively.

  Key Insight:
  Additive functions with bounded consecutive differences are essentially
  logarithmic. The logarithm is characterized as the unique (up to scaling)
  additive function with this regularity property.

  Tags: number-theory, additive-functions, logarithm, characterization
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos491

open Real

/- ## Part I: Basic Definitions

Additive functions and their properties.
-/

/-- A function f: ℕ → ℝ is additive if f(ab) = f(a) + f(b) when gcd(a,b) = 1 -/
def IsAdditive (f : ℕ → ℝ) : Prop :=
  f 1 = 0 ∧ ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b

/-- A function is completely additive if f(ab) = f(a) + f(b) always -/
def IsCompletelyAdditive (f : ℕ → ℝ) : Prop :=
  f 1 = 0 ∧ ∀ a b : ℕ, f (a * b) = f a + f b

/-- Completely additive implies additive -/
theorem completely_additive_is_additive (f : ℕ → ℝ) :
    IsCompletelyAdditive f → IsAdditive f := fun ⟨h1, h2⟩ =>
  ⟨h1, fun a b _ => h2 a b⟩

/- ## Part II: Bounded Differences Condition

The key hypothesis: |f(n+1) - f(n)| < c.
-/

/-- f has bounded consecutive differences -/
def HasBoundedDifferences (f : ℕ → ℝ) (c : ℝ) : Prop :=
  c > 0 ∧ ∀ n : ℕ, |f (n + 1) - f n| < c

/- ## Part III: Erdős's Earlier Results (1946)

Weaker conditions that still characterize the logarithm.
-/

/-- f(n+1) - f(n) = o(1) means differences tend to 0 -/
def DifferencesTendToZero (f : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun n => f (n + 1) - f n) Filter.atTop (nhds 0)

/-- f is monotonically non-decreasing -/
def IsMonotone (f : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, f (n + 1) ≥ f n

/-- Erdős (1946): If additive and differences → 0, then f(n) = c·log(n) -/
axiom erdos_1946_o1 (f : ℕ → ℝ) (hf : IsAdditive f)
    (hd : DifferencesTendToZero f) :
  ∃ c : ℝ, ∀ n : ℕ, n ≥ 1 → f n = c * Real.log n

/- ## Part IV: Wirsing's Theorem (1970)

The full solution to Erdős's problem.
-/

/-- f(n) = c·log(n) + O(1) means bounded distance from c·log -/
def IsLogPlusO1 (f : ℕ → ℝ) (c' : ℝ) : Prop :=
  ∃ M : ℝ, M > 0 ∧ ∀ n : ℕ, n ≥ 1 → |f n - c' * Real.log n| ≤ M

/-- Wirsing's Theorem (1970): Bounded differences imply f = c·log + O(1) -/
axiom wirsing_theorem (f : ℕ → ℝ) (hf : IsAdditive f)
    (c : ℝ) (hc : HasBoundedDifferences f c) :
  ∃ c' : ℝ, IsLogPlusO1 f c'

/-- Wirsing's constant: the coefficient of the logarithm -/
noncomputable def wirsingConstant (f : ℕ → ℝ) (hf : IsAdditive f)
    (c : ℝ) (hc : HasBoundedDifferences f c) : ℝ :=
  Classical.choose (wirsing_theorem f hf c hc)

/- ## Part V: Erdős Problem #491 Statement

The main theorem combining all results.
-/

/-- Erdős Problem #491: The characterization of additive functions -/
theorem erdos_491 (f : ℕ → ℝ) (hf : IsAdditive f)
    (c : ℝ) (hc : HasBoundedDifferences f c) :
    ∃ c' : ℝ, IsLogPlusO1 f c' :=
  wirsing_theorem f hf c hc

/-- Alternative formulation with explicit bound -/
theorem erdos_491_explicit (f : ℕ → ℝ) (hf : IsAdditive f)
    (c : ℝ) (hc : HasBoundedDifferences f c) :
    ∃ c' M : ℝ, M > 0 ∧ ∀ n : ℕ, n ≥ 1 → |f n - c' * Real.log n| ≤ M := by
  obtain ⟨c', M, hM, h⟩ := wirsing_theorem f hf c hc
  exact ⟨c', M, hM, h⟩

/- ## Part VI: Properties of the Characterization

Further consequences of Wirsing's theorem.
-/

/-- The coefficient c' is unique -/
axiom wirsing_constant_unique (f : ℕ → ℝ) (hf : IsAdditive f)
    (c' c'' : ℝ) (h' : IsLogPlusO1 f c') (h'' : IsLogPlusO1 f c'') :
  c' = c''

/- ## Part VII: Examples and Non-Examples
-/

/-- A non-additive function need not satisfy the conclusion -/
def nonExample : ℕ → ℝ := fun n => (n : ℝ)

theorem non_example_bounded_diff :
    HasBoundedDifferences nonExample 2 := by
  constructor
  · norm_num
  · intro n
    simp [nonExample]
    norm_num

/- ## Part VIII: Connection to Prime Factorization

Additive functions are determined by values on primes.
-/

/-- The completely additive extension from primes -/
noncomputable def additiveFromPrimes (g : ℕ → ℝ) : ℕ → ℝ :=
  fun n => if n = 0 then 0 else ∑ p ∈ n.primeFactors, g p * n.factorization p

/- ## Part IX: Rate of Convergence

How quickly does f(n) approach c'·log(n)?
-/

/- ## Part X: Related Problems

Connections to other additive function problems.
-/

/- ## Part XI: Summary
-/

/-- Main summary: Erdős Problem #491 is solved -/
theorem erdos_491_summary :
    -- Additive functions with bounded differences are log + O(1)
    (∀ f : ℕ → ℝ, ∀ hf : IsAdditive f, ∀ c : ℝ, ∀ hc : HasBoundedDifferences f c,
      ∃ c' : ℝ, IsLogPlusO1 f c') ∧
    -- Erdős's 1946 results are special cases
    (∀ f : ℕ → ℝ, IsAdditive f → DifferencesTendToZero f →
      ∃ c : ℝ, ∀ n : ℕ, n ≥ 1 → f n = c * Real.log n) ∧
    -- The coefficient c' is unique
    (∀ f : ℕ → ℝ, ∀ c' c'' : ℝ, IsLogPlusO1 f c' → IsLogPlusO1 f c'' → c' = c'') := by
  exact ⟨wirsing_theorem, erdos_1946_o1, wirsing_constant_unique⟩

/-- Erdős Problem #491: SOLVED by Wirsing (1970)
    The answer is YES — additive + bounded differences implies f = c'·log + O(1). -/
theorem erdos_491_answer (f : ℕ → ℝ) (hf : IsAdditive f)
    (c : ℝ) (hc : HasBoundedDifferences f c) :
    ∃ c' : ℝ, IsLogPlusO1 f c' :=
  wirsing_theorem f hf c hc

end Erdos491
