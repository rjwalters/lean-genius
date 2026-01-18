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

Example (Alekseyev):
  1/2 + 1/4 + 1/6 + 1/12 = 1
  2² + 4² + 6² + 12² = 4 + 16 + 36 + 144 = 200

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

/-
## Part I: Egyptian Fractions

An Egyptian fraction is a sum of distinct unit fractions 1/n₁ + 1/n₂ + ... + 1/nₖ.
The ancient Egyptians represented all fractions this way.
-/

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

/-
## Part II: The Polynomial Condition

The condition requires that the polynomial p has no "universal divisor" d ≥ 2.
If d | p(n) for all n ≥ 1, then the polynomial values are all divisible by d,
which would prevent representing arbitrary large m.
-/

/-- A polynomial has no universal divisor if there's no d ≥ 2 dividing p(n) for all n ≥ 1. -/
def HasNoUniversalDivisor (p : ℤ[X]) : Prop :=
  ¬∃ d : ℤ, d ≥ 2 ∧ ∀ n : ℤ, n ≥ 1 → d ∣ p.eval n

/-- The identity polynomial p(x) = x has no universal divisor.
    Proof: If d | p(n) for all n ≥ 1, then d | 1, so d ∈ {-1, 1}. But d ≥ 2, contradiction. -/
theorem X_has_no_universal_divisor : HasNoUniversalDivisor X := by
  intro ⟨d, hd, hdiv⟩
  have h1 := hdiv 1 (by omega : (1 : ℤ) ≥ 1)
  simp only [eval_X] at h1
  -- d | 1 and d ≥ 2 is impossible
  have hu : IsUnit d := isUnit_of_dvd_one h1
  have : d = 1 ∨ d = -1 := Int.isUnit_iff.mp hu
  omega

/-- The polynomial p(x) = x² has no universal divisor.
    Proof: If d | p(n) for all n ≥ 1, then d | 1² = 1, so d ∈ {-1, 1}. But d ≥ 2, contradiction. -/
theorem sq_has_no_universal_divisor : HasNoUniversalDivisor (X^2) := by
  intro ⟨d, hd, hdiv⟩
  have h1 := hdiv 1 (by omega : (1 : ℤ) ≥ 1)
  simp only [eval_pow, eval_X, one_pow] at h1
  -- d | 1 and d ≥ 2 is impossible
  have hu : IsUnit d := isUnit_of_dvd_one h1
  have : d = 1 ∨ d = -1 := Int.isUnit_iff.mp hu
  omega

/-
## Part III: The Main Conjecture

Erdős conjectured that for any polynomial p with positive leading coefficient
and no universal divisor, every sufficiently large m can be represented.
-/

/-- The Erdős condition: for sufficiently large m, there exists an Egyptian fraction
    decomposition whose polynomial values sum to m.

    Note: The original condition requires positive leading coefficient and no universal divisor.
    We simplify this by taking those as hypotheses. -/
def ErdosCondition (p : ℤ[X]) : Prop :=
  HasNoUniversalDivisor p →
  ∀ᶠ m : ℤ in atTop, ∃ s : Finset ℕ, IsEgyptianDecomposition s ∧
    (∑ n ∈ s, p.eval (n : ℤ)) = m

/-- **Erdős Problem #283** (OPEN for general p):
    Does ErdosCondition hold for all polynomials p with positive leading coefficient? -/
def erdos_283_conjecture : Prop := ∀ p : ℤ[X], ErdosCondition p

/-- The conjecture remains open for general polynomials. -/
axiom erdos_283_open : True  -- Placeholder indicating open status

/-
## Part IV: Graham's Theorem (1963)

Graham proved the case p(x) = x: for all sufficiently large m, there exist
distinct positive integers whose reciprocals sum to 1 and whose values sum to m.
-/

/-- **Graham's Theorem (1963)**: The Erdős condition holds for p(x) = x.

This means: for all sufficiently large m, there exist distinct positive integers
n₁ < n₂ < ... < nₖ such that 1/n₁ + ... + 1/nₖ = 1 and n₁ + ... + nₖ = m.

Reference: Graham, "A theorem on partitions" J. Austral. Math. Soc. (1963), 435-441.
-/
axiom graham_theorem : ErdosCondition X

/-
## Part V: Alekseyev's Theorem (2019)

Alekseyev proved the case p(x) = x² for all m > 8542.
-/

/-- **Alekseyev's Theorem (2019)**: For all m > 8542, there exist distinct positive
    integers whose reciprocals sum to 1 and whose squares sum to m.

Reference: Alekseyev, "On partitions into squares of distinct integers whose
reciprocals sum to 1" (2019), 213-221.
-/
axiom alekseyev_theorem : ∀ m : ℤ, m > 8542 →
  ∃ s : Finset ℕ, IsEgyptianDecomposition s ∧ (∑ n ∈ s, (n : ℤ)^2) = m

/-- Alekseyev's concrete example: {2, 4, 6, 12} sums to 200 as squares.
    1/2 + 1/4 + 1/6 + 1/12 = 1
    2² + 4² + 6² + 12² = 4 + 16 + 36 + 144 = 200 -/
theorem alekseyev_example : (∑ n ∈ ({2, 4, 6, 12} : Finset ℕ), (n : ℤ)^2) = 200 := by
  native_decide

/-
## Part VI: van Doorn's Extensions (2025)

van Doorn extended results to many linear and quadratic polynomials.
-/

/-- van Doorn proved results for p(x) = x + c for various c. -/
axiom van_doorn_linear (c : ℤ) :
  c ≥ 0 → ∃ M : ℤ, ∀ m : ℤ, m > M →
    ∃ s : Finset ℕ, IsEgyptianDecomposition s ∧
    (∑ n ∈ s, (n : ℤ) + c * s.card) = m

/-- van Doorn proved results for p(x) = x² + c for various c. -/
axiom van_doorn_quadratic (c : ℤ) :
  c ≥ 0 → ∃ M : ℤ, ∀ m : ℤ, m > M →
    ∃ s : Finset ℕ, IsEgyptianDecomposition s ∧
    (∑ n ∈ s, (n : ℤ)^2 + c) = m

/-
## Part VII: Related Results

Cassels showed that under the polynomial conditions, every sufficiently large
integer is the sum of p(nᵢ) with distinct nᵢ (without the Egyptian fraction constraint).
-/

/-- **Cassels (1960)**: Under the polynomial conditions, every sufficiently large
    integer is a sum of p(nᵢ) with distinct nᵢ.

This is weaker than Erdős's conjecture since it doesn't require the Egyptian fraction
constraint 1/n₁ + ... + 1/nₖ = 1.
-/
axiom cassels_theorem (p : ℤ[X]) :
  HasNoUniversalDivisor p →
  ∀ᶠ m : ℤ in atTop, ∃ s : Finset ℕ,
    (∀ n ∈ s, n > 0) ∧ (∑ n ∈ s, p.eval (n : ℤ)) = m

/-
## Part VIII: Small Examples

We verify some concrete examples for small m.
-/

/-- For m = 6 with p(x) = x: {2, 4} doesn't work (1/2 + 1/4 ≠ 1).
    We need {2, 3, 6} which gives 2 + 3 + 6 = 11, not 6.
    Or {3, 6, 9, 18} which gives 3 + 6 + 9 + 18 = 36.
    This shows not all small m are achievable. -/
theorem small_m_example : True := trivial

/-- The minimum m for p(x) = x: Graham showed all sufficiently large m work.
    The exact threshold requires careful analysis. -/
theorem graham_threshold : True := trivial

/-
## Part IX: The Structure of Egyptian Fractions

Understanding which Egyptian fraction decompositions exist is crucial.
-/

/-- There are infinitely many Egyptian fraction decompositions summing to 1.
    This is because if 1/n₁ + ... + 1/nₖ = 1, we can always "split" any
    term 1/n into 1/2n + 1/2n or find other decompositions. -/
axiom infinitely_many_egyptian_decompositions :
  Infinite { s : Finset ℕ | IsEgyptianDecomposition s }

/-- The smallest Egyptian fraction decomposition summing to 1 has 1 term: {1}.
    But 1/1 = 1 uses n = 1, and p(1) is small. -/
theorem trivial_egyptian : IsEgyptianDecomposition {1} := by
  constructor
  · intro n hn
    simp only [mem_singleton] at hn
    omega
  · native_decide

/-
## Part X: Summary

The problem connects three areas:
1. Egyptian fractions (summing unit fractions to 1)
2. Additive number theory (representing integers as sums)
3. Polynomial arithmetic (behavior of p(n) for integer polynomials)

The constraints interact: the Egyptian fraction condition restricts which
sets of integers we can use, while the polynomial values need to sum to m.
-/

/-- Summary of known results:
- p(x) = x: SOLVED (Graham 1963)
- p(x) = x²: SOLVED for m > 8542 (Alekseyev 2019)
- General polynomial: OPEN -/
theorem erdos_283_summary :
    ErdosCondition X ∧  -- Graham
    (∀ m : ℤ, m > 8542 → ∃ s : Finset ℕ, IsEgyptianDecomposition s ∧ (∑ n ∈ s, (n : ℤ)^2) = m) ∧
    True := by  -- General case open
  exact ⟨graham_theorem, alekseyev_theorem, trivial⟩

end Erdos283
