/-
Erdős Problem #283: Egyptian Fractions and Polynomial Values

Source: https://erdosproblems.com/283
Status: PARTIALLY SOLVED (Graham 1963 proved for p(x) = x; Alekseyev 2019 proved for p(x) = x²)

Statement:
Let p : ℤ → ℤ be a polynomial with positive leading coefficient, and suppose there
is no integer d ≥ 2 that divides p(n) for all n ≥ 1. Is it true that for all
sufficiently large m, there exist distinct positive integers n₁ < n₂ < ... < nₖ such that:

  1/n₁ + 1/n₂ + ... + 1/nₖ = 1   (an Egyptian fraction summing to 1)
  p(n₁) + p(n₂) + ... + p(nₖ) = m  (polynomial values sum to m)

Key Results:
- Graham (1963): TRUE for p(x) = x
- Alekseyev (2019): TRUE for p(x) = x², for all m > 8542
- van Doorn (2025): Extended to many linear and quadratic polynomials
- General case: OPEN

References:
- [Gr63] Graham, "A theorem on partitions" J. Austral. Math. Soc. (1963)
- [Al19] Alekseyev, "On partitions into squares" (2019)
- [vD25] van Doorn, arXiv:2502.02200 (2025)
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic

open Polynomial Filter Finset

namespace Erdos283

/- ## Part I: Egyptian Fractions -/

/-- A finite sequence of distinct positive integers that sum to 1 as unit fractions. -/
def IsEgyptianDecomposition (s : Finset ℕ) : Prop :=
  (∀ n ∈ s, n > 0) ∧ (∑ n ∈ s, (1 : ℚ) / n) = 1

/-- Example: {2, 3, 6} gives the Egyptian fraction 1/2 + 1/3 + 1/6 = 1. -/
theorem egyptian_example_236 : IsEgyptianDecomposition {2, 3, 6} := by
  constructor
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> norm_num
  · native_decide

/-- Example: {2, 4, 6, 12} gives 1/2 + 1/4 + 1/6 + 1/12 = 1. -/
theorem egyptian_example_2_4_6_12 : IsEgyptianDecomposition {2, 4, 6, 12} := by
  constructor
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> norm_num
  · native_decide

/- ## Part II: The Polynomial Condition -/

/-- A polynomial has no universal divisor if there's no d ≥ 2 dividing p(n) for all n ≥ 1. -/
def HasNoUniversalDivisor (p : ℤ[X]) : Prop :=
  ¬∃ d : ℤ, d ≥ 2 ∧ ∀ n : ℤ, n ≥ 1 → d ∣ p.eval n

/-- The identity polynomial p(x) = x has no universal divisor. -/
theorem X_has_no_universal_divisor : HasNoUniversalDivisor X := by
  intro ⟨d, hd, hdiv⟩
  have h1 := hdiv 1 (by omega : (1 : ℤ) ≥ 1)
  simp only [eval_X] at h1
  have hu : IsUnit d := isUnit_of_dvd_one h1
  have : d = 1 ∨ d = -1 := Int.isUnit_iff.mp hu
  omega

/-- The polynomial p(x) = x² has no universal divisor. -/
theorem sq_has_no_universal_divisor : HasNoUniversalDivisor (X^2) := by
  intro ⟨d, hd, hdiv⟩
  have h1 := hdiv 1 (by omega : (1 : ℤ) ≥ 1)
  simp only [eval_pow, eval_X, one_pow] at h1
  have hu : IsUnit d := isUnit_of_dvd_one h1
  have : d = 1 ∨ d = -1 := Int.isUnit_iff.mp hu
  omega

/- ## Part III: The Main Conjecture -/

/-- The Erdős condition: for sufficiently large m, there exists an Egyptian fraction
    decomposition whose polynomial values sum to m. -/
def ErdosCondition (p : ℤ[X]) : Prop :=
  HasNoUniversalDivisor p →
  ∀ᶠ m : ℤ in atTop, ∃ s : Finset ℕ, IsEgyptianDecomposition s ∧
    (∑ n ∈ s, p.eval (n : ℤ)) = m

/-- **Erdős Problem #283** (OPEN for general p):
    Does ErdosCondition hold for all polynomials p with positive leading coefficient? -/
def erdos_283_conjecture : Prop := ∀ p : ℤ[X], ErdosCondition p

/- ## Part IV: Graham's Theorem (1963) -/

/-- **Graham's Theorem (1963)**: The Erdős condition holds for p(x) = x.

This means: for all sufficiently large m, there exist distinct positive integers
n₁ < n₂ < ... < nₖ such that 1/n₁ + ... + 1/nₖ = 1 and n₁ + ... + nₖ = m. -/
axiom graham_theorem : ErdosCondition X

/- ## Part V: Alekseyev's Theorem (2019) -/

/-- **Alekseyev's Theorem (2019)**: For all m > 8542, there exist distinct positive
    integers whose reciprocals sum to 1 and whose squares sum to m. -/
axiom alekseyev_theorem : ∀ m : ℤ, m > 8542 →
  ∃ s : Finset ℕ, IsEgyptianDecomposition s ∧ (∑ n ∈ s, (n : ℤ)^2) = m

/-- Alekseyev's concrete example: {2, 4, 6, 12} sums to 200 as squares. -/
theorem alekseyev_example : (∑ n ∈ ({2, 4, 6, 12} : Finset ℕ), (n : ℤ)^2) = 200 := by
  native_decide

/- ## Part VI: van Doorn's Extensions (2025) -/

/-- van Doorn proved results for p(x) = x + c for various c. -/
/-- van Doorn proved results for p(x) = x² + c for various c. -/
/- ## Part VII: Cassels' Theorem -/

/-- **Cassels (1960)**: Under the polynomial conditions, every sufficiently large
    integer is a sum of p(nᵢ) with distinct nᵢ (without Egyptian fraction constraint). -/
/- ## Part VIII: Egyptian Fraction Structure -/

/-- There are infinitely many Egyptian fraction decompositions summing to 1. -/
/-- The simplest Egyptian fraction decomposition: {1} since 1/1 = 1. -/
theorem trivial_egyptian : IsEgyptianDecomposition {1} := by
  constructor
  · intro n hn
    simp only [mem_singleton] at hn
    omega
  · native_decide

/- ## Part IX: Summary -/

/-- **Summary of Erdős Problem #283:**

PROBLEM: For polynomials p with no universal divisor, can every large m
be written as p(n₁) + ... + p(nₖ) where 1/n₁ + ... + 1/nₖ = 1?

STATUS: PARTIALLY SOLVED
- p(x) = x: YES (Graham 1963)
- p(x) = x²: YES for m > 8542 (Alekseyev 2019)
- General polynomial: OPEN

This theorem packages both known results. -/
theorem erdos_283_summary :
    ErdosCondition X ∧
    (∀ m : ℤ, m > 8542 → ∃ s : Finset ℕ, IsEgyptianDecomposition s ∧
      (∑ n ∈ s, (n : ℤ)^2) = m) :=
  ⟨graham_theorem, alekseyev_theorem⟩

end Erdos283
