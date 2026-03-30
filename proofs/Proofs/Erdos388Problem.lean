/-
# Erdős Problem #388 — Products of Consecutive Integers

Can one classify all solutions of
  ∏_{i=1}^{k₁} (m₁ + i) = ∏_{j=1}^{k₂} (m₂ + j)
where k₁, k₂ > 3 and m₁ + k₁ ≤ m₂?
Are there only finitely many solutions?

More generally, for k₁ > 2 and fixed nonzero a, b:
  a · ∏_{i=1}^{k₁} (m₁ + i) = b · ∏_{j=1}^{k₂} (m₂ + j)
should have only finitely many solutions.

## Background

The product of k consecutive integers starting from m+1 is the
falling factorial (m+k)! / m!, equivalently (m+k).choose k · k!.
Equating two such products asks when two blocks of consecutive
integers have the same product — a Diophantine question related
to the Brocard–Ramanujan problem and Erdős–Selfridge theorem.

## Key Context

- Erdős and Selfridge (1975) proved that a product of two or more
  consecutive positive integers is never a perfect power.
- The problem generalizes: when can two *disjoint* blocks of
  consecutive integers have equal (or proportional) products?
- Related to Problems #363 and #931.

*Reference:* [erdosproblems.com/388](https://www.erdosproblems.com/388)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.LocallyFinite

open Finset BigOperators

/- ## Core Definitions -/

/-- Product of k consecutive integers starting from m+1:
  (m+1)(m+2)···(m+k) = (m+k)! / m! -/
def consecutiveProduct (m k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (m + i)

/-- A solution to the equal-products equation: two disjoint blocks
of consecutive integers with the same product.
We require k₁, k₂ > 3 and the blocks to be disjoint (m₁ + k₁ ≤ m₂). -/
structure EqualProductSolution where
  m₁ : ℕ
  m₂ : ℕ
  k₁ : ℕ
  k₂ : ℕ
  hk₁ : 3 < k₁
  hk₂ : 3 < k₂
  disjoint : m₁ + k₁ ≤ m₂
  equal : consecutiveProduct m₁ k₁ = consecutiveProduct m₂ k₂

/-- The set of all solutions to the equal-products equation. -/
def equalProductSolutions : Set EqualProductSolution :=
  Set.univ

/- ## Main Conjecture -/

/-- **Erdős Problem #388 (Open).**
There are only finitely many solutions to
  ∏_{i=1}^{k₁} (m₁+i) = ∏_{j=1}^{k₂} (m₂+j)
with k₁, k₂ > 3 and m₁ + k₁ ≤ m₂. -/
/- ## Generalized Version -/

/-- A solution to the generalized proportional-products equation:
  a · ∏_{i=1}^{k₁} (m₁+i) = b · ∏_{j=1}^{k₂} (m₂+j)
with fixed nonzero a, b and k₁ > 2. -/
structure ProportionalProductSolution (a b : ℕ) where
  m₁ : ℕ
  m₂ : ℕ
  k₁ : ℕ
  k₂ : ℕ
  hk₁ : 2 < k₁
  disjoint : m₁ + k₁ ≤ m₂
  proportional : a * consecutiveProduct m₁ k₁ = b * consecutiveProduct m₂ k₂

/-- **Generalized Conjecture.**
For fixed nonzero a, b and k₁ > 2, the equation
  a · ∏(m₁+i) = b · ∏(m₂+j)
has only finitely many solutions. -/
/- ## Related Classical Results -/

/-- **Erdős–Selfridge (1975).** A product of two or more consecutive
positive integers is never a perfect power.
That is, (m+1)(m+2)···(m+k) ≠ nʳ for k ≥ 2 and r ≥ 2. -/
/-- The product of consecutive integers connects to factorials:
  consecutiveProduct m k = (m + k)! / m!
Proved by induction on k, using Nat.factorial and Finset.prod_Icc. -/
theorem consecutiveProduct_eq_factorial_ratio (m k : ℕ) :
    consecutiveProduct m k * m.factorial = (m + k).factorial := by
  induction k with
  | zero => simp [consecutiveProduct]
  | succ n ih =>
    simp only [consecutiveProduct] at ih ⊢
    rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) from by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
    rw [show m + (n + 1) = m + n + 1 from by omega]
    rw [mul_comm (m + n + 1), mul_assoc, ih]
    rw [show m + (n + 1) = (m + n) + 1 from by omega, Nat.factorial_succ]
    ring

/-- **Trivial family.** If k₁ = k₂ and m₁ = m₂ then the products are
trivially equal. The conjecture excludes this by requiring disjointness. -/
theorem trivial_equal_product (m k : ℕ) :
    consecutiveProduct m k = consecutiveProduct m k := rfl
