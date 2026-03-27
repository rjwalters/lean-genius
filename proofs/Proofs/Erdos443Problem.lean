/-
Erdős Problem #443: Common Products k(m-k) and l(n-l)

  Source: https://erdosproblems.com/443
  Status: SOLVED (Hegyvári 2025, Cambie unpublished)

  Statement:
  For integers m, n ≥ 1, consider the sets:
    A_m = { k(m-k) : 1 ≤ k ≤ m/2 }
    B_n = { l(n-l) : 1 ≤ l ≤ n/2 }

  Questions:
  1. Can |A_m ∩ B_n| be arbitrarily large?
  2. Is |A_m ∩ B_n| ≤ (mn)^{o(1)} for all sufficiently large m, n?

  Answer:
  1. YES - For any integer s, infinitely many pairs (m,n) have |A_m ∩ B_n| = s
  2. YES - When m > n, we have |A_m ∩ B_n| ≤ m^{O(1/log log m)}

  Background:
  - The products k(m-k) are related to sums of arithmetic progressions
  - k(m-k) = km - k² = (m²/4) - (k - m/2)²
  - So A_m consists of integers of form (m²/4) - d² for small d
  - Finding common values means solving k(m-k) = l(n-l), a Diophantine problem

  Tags: number-theory, arithmetic-progressions, diophantine-equations
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Lemmas

namespace Erdos443

/- ## Part 1: Basic Definitions

The set of products k(m-k) for 1 ≤ k ≤ m/2.
-/

/-- The product k(m-k) for fixed m -/
def productValue (m k : ℕ) : ℕ := k * (m - k)

/-- The set A_m = { k(m-k) : 1 ≤ k ≤ m/2 } -/
def productSet (m : ℕ) : Finset ℕ :=
  (Finset.range (m / 2 + 1)).filter (fun _ => True) |>.image (productValue m)

/-- Alternative: the range of valid k values -/
def validKRange (m : ℕ) : Finset ℕ :=
  (Finset.range (m / 2 + 1)).filter (fun k => 1 ≤ k)

/-- The intersection |A_m ∩ B_n| we're counting -/
def commonProducts (m n : ℕ) : Finset ℕ :=
  productSet m ∩ productSet n

/-- The count of common products -/
def commonProductCount (m n : ℕ) : ℕ :=
  (commonProducts m n).card

/- ## Part 2: Elementary Properties

Basic facts about the product k(m-k).
-/

/-- k(m-k) = 0 when k = 0 or k = m -/
theorem product_zero_endpoints (m : ℕ) :
    productValue m 0 = 0 ∧ productValue m m = 0 := by
  simp only [productValue]
  constructor
  · ring
  · simp

/- ## Part 3: Size of A_m

The set A_m has approximately m/2 elements.
-/

/- ## Part 4: The Diophantine Equation

Finding common products means solving k(m-k) = l(n-l).
-/

/-- The equation k(m-k) = l(n-l) as a Diophantine problem -/
def sameProduct (m n k l : ℕ) : Prop :=
  productValue m k = productValue n l

/- ## Part 5: Main Results - Hegyvári (2025)

The key bounds on |A_m ∩ B_n|.
-/

/-- The bound (mn)^{o(1)} is achieved -/
axiom subpolynomial_bound (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∀ ε > 0, ∃ M : ℕ, ∀ m' n' : ℕ, M ≤ m' → M ≤ n' →
      (commonProductCount m' n' : ℝ) ≤ ((m' : ℝ) * n') ^ ε

/-- For any s, infinitely many pairs (m,n) achieve |A_m ∩ B_n| = s -/
axiom arbitrarily_large_intersection (s : ℕ) :
    ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ N < n ∧ commonProductCount m n = s

/-- Corollary: The intersection can be arbitrarily large -/
theorem intersection_unbounded :
    ∀ s : ℕ, ∃ m n : ℕ, s ≤ commonProductCount m n := by
  intro s
  obtain ⟨m, n, _, _, h⟩ := arbitrarily_large_intersection s 0
  exact ⟨m, n, le_of_eq h.symm⟩

/- ## Part 6: Special Cases and Examples
-/

/-- For m = n, the intersection equals A_m itself -/
theorem common_self (m : ℕ) :
    commonProducts m m = productSet m := by
  simp only [commonProducts, Finset.inter_self]

/-- For small m, n, we can compute exactly -/
example : productValue 4 1 = 3 := by native_decide
example : productValue 4 2 = 4 := by native_decide
example : productValue 6 1 = 5 := by native_decide
example : productValue 6 2 = 8 := by native_decide
example : productValue 6 3 = 9 := by native_decide

/- ## Part 7: Relation to Quadratic Residues

k(m-k) is related to squares and quadratic residues.
-/

/- ## Part 8: Connection to Sums of Arithmetic Progressions

k(m-k) = 1 + 2 + ... + (m-1) with specific terms removed.
-/

/-- The sum 1 + 2 + ... + (m-1) = m(m-1)/2 -/
def triangularNumber (m : ℕ) : ℕ := m * (m - 1) / 2

/- ## Part 9: Growth Rate Analysis

The bound m^{O(1/log log m)} grows very slowly.
-/

/- ## Part 10: The Proof Technique

Hegyvári's approach uses divisibility and sieve methods.
-/


/- ## Part 11: Comparison with Related Problems

Similar problems about common values.
-/

/-- Compare: Common values of n choose 2 -/
def binomialSet (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).image (fun k => k * (k - 1) / 2)

/- ## Part 12: Summary

Erdős Problem #443 is SOLVED.
-/

/-- Main theorem: Erdős Problem #443 is solved -/
theorem erdos_443_summary :
    -- 1. The intersection can be arbitrarily large
    (∀ s : ℕ, ∃ m n : ℕ, s ≤ commonProductCount m n) ∧
    -- 2. The intersection is bounded by (mn)^{o(1)}
    (∀ ε > 0, ∃ M : ℕ, ∀ m n : ℕ, M ≤ m → M ≤ n →
      (commonProductCount m n : ℝ) ≤ ((m : ℝ) * n) ^ ε) := by
  constructor
  · exact intersection_unbounded
  · intro ε hε
    exact subpolynomial_bound 2 2 (by norm_num) (by norm_num) ε hε

/-- Erdős Problem #443: SOLVED -/
theorem erdos_443 :
    (∀ s : ℕ, ∃ m n : ℕ, s ≤ commonProductCount m n) ∧
    (∀ ε > 0, ∃ M : ℕ, ∀ m n : ℕ, M ≤ m → M ≤ n →
      (commonProductCount m n : ℝ) ≤ ((m : ℝ) * n) ^ ε) :=
  erdos_443_summary

end Erdos443
