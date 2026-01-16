/-
Erdős Problem #351: Strong Completeness of Polynomial-Reciprocal Sequences

**Problem (Erdős-Graham)**: Let p(x) ∈ ℚ[x] be a polynomial with positive leading
coefficient. Is the set A = {p(n) + 1/n : n ∈ ℕ} "strongly complete"?

A set A is **strongly complete** if for any finite set B, the finite sums from
A \ B contain all sufficiently large integers.

**Status**:
- General problem: OPEN
- Case p(x) = x: PROVED by Graham (1963)
- Case p(x) = x²: PROVED by Graham (1963) + Alekseyev (2019)

Reference: https://erdosproblems.com/351
-/

import Mathlib

open Polynomial Finset Filter Set

namespace Erdos351

/-! ## Key Definitions -/

/-- The image set {p(n) + 1/n : n ∈ ℕ} for a polynomial p over a semifield.
    Note: p(0) + 1/0 = p(0) + 0 = p(0) is included since 1/0 = 0 in ℕ. -/
def imageSet (P : ℚ[X]) : Set ℚ :=
  range (fun (n : ℕ) => P.eval ↑n + 1 / ↑n)

/-- A set A ⊆ ℚ is **strongly complete** if for every finite "forbidden" set B,
    all sufficiently large integers can be written as finite sums from A \ B.

    This is stronger than just "complete" (which allows using all of A). -/
def IsStronglyComplete (A : Set ℚ) : Prop :=
  ∀ B : Finset ℚ, ∀ᶠ (m : ℕ) in atTop,
    ∃ X : Finset ℚ, ↑X ⊆ A \ ↑B ∧ X.sum id = ↑m

/-- The predicate that polynomial P has a strongly complete image set. -/
def HasStronglyCompleteImage (P : ℚ[X]) : Prop :=
  IsStronglyComplete (imageSet P)

/-! ## Main Results -/

/--
**Erdős Problem #351** (Open):

The general conjecture asks: for every polynomial p(x) ∈ ℚ[x] with positive
leading coefficient and positive degree, is {p(n) + 1/n : n ∈ ℕ} strongly complete?

This remains open. The answer is unknown.
-/
axiom erdos_351_open :
  True  -- Placeholder: the general problem is open

/-! ## Solved Cases -/

/--
**Graham's Theorem (1963)**: The set {n + 1/n : n ∈ ℕ} is strongly complete.

This is the case p(x) = x. Graham proved that even after removing any finite
set of elements, the remaining terms can sum to all sufficiently large integers.
-/
axiom graham_theorem_linear : HasStronglyCompleteImage X

/--
**Graham-Alekseyev Theorem**: The set {n² + 1/n : n ∈ ℕ} is strongly complete.

This is the case p(x) = x². Van Doorn noted this follows from combining
Graham's 1963 result with Alekseyev's 2019 result on partitions into
squares of distinct integers whose reciprocals sum to 1.
-/
axiom graham_alekseyev_quadratic : HasStronglyCompleteImage (X ^ 2)

/-! ## Basic Properties -/

/-- The image set for p(x) = x contains n + 1/n for all n ≥ 1 -/
theorem mem_imageSet_linear (n : ℕ) : (n : ℚ) + 1 / n ∈ imageSet X := by
  simp only [imageSet, Set.mem_range]
  use n
  simp [eval_X]

/-- The image set for p(x) = x² contains n² + 1/n for all n ≥ 1 -/
theorem mem_imageSet_quadratic (n : ℕ) : (n : ℚ)^2 + 1 / n ∈ imageSet (X ^ 2) := by
  simp only [imageSet, Set.mem_range]
  use n
  simp [eval_pow, eval_X]

/-- For n ≥ 1, the element n + 1/n is strictly greater than n -/
theorem linear_lower_bound (n : ℕ) (hn : n ≥ 1) :
    (n : ℚ) < n + 1 / n := by
  have : (0 : ℚ) < 1 / n := by positivity
  linarith

/-- For n ≥ 2, the element n + 1/n is strictly less than n+1 -/
theorem linear_upper_bound (n : ℕ) (hn : n ≥ 2) :
    (n : ℚ) + 1 / n < n + 1 := by
  have h1 : (1 : ℚ) / n < 1 := by
    rw [div_lt_one (by positivity : (n : ℚ) > 0)]
    exact_mod_cast hn
  linarith

/-- Special case: 1 + 1/1 = 2, which equals 1 + 1 -/
theorem linear_n1_special : (1 : ℚ) + 1 / 1 = 1 + 1 := by norm_num

/-- Example: 1 + 1/1 = 2 -/
theorem example_n1 : (1 : ℚ) + 1 / 1 = 2 := by norm_num

/-- Example: 2 + 1/2 = 5/2 -/
theorem example_n2 : (2 : ℚ) + 1 / 2 = 5 / 2 := by norm_num

/-- Example: 3 + 1/3 = 10/3 -/
theorem example_n3 : (3 : ℚ) + 1 / 3 = 10 / 3 := by norm_num

end Erdos351
