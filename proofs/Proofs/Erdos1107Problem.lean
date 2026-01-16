/-
Erdős Problem #1107: Sums of r-Powerful Numbers

Let r ≥ 2. A number n is r-powerful (or r-full) if for every prime p
dividing n, we have p^r | n.

**Question**: Is every sufficiently large integer the sum of at most
r + 1 many r-powerful numbers?

**Status**:
- OPEN in general (for arbitrary r ≥ 2)
- SOLVED for r = 2 by Heath-Brown (1988)

Heath-Brown proved that every sufficiently large integer is the sum of
at most three squareful (2-powerful) numbers using the theory of ternary
quadratic forms.

This problem was posed by Erdős and Ivić in the 1986 Oberwolfach problem book.

References:
- https://erdosproblems.com/1107
- Heath-Brown, D. R. "Ternary quadratic forms and sums of three square-full
  numbers" Séminaire de Théorie des Nombres, Paris 1986-87 (1988), 137-163.
-/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Nat Filter

namespace Erdos1107

/-!
## Definitions

We define r-powerful (r-full) numbers and what it means for a number to be
expressible as a sum of r-powerful numbers.
-/

/--
A natural number `n` is `r`-powerful (or `r`-full) if for every prime `p`
dividing `n`, we have `p^r ∣ n`.

Examples:
- 1 is r-powerful for all r (vacuously, no prime factors)
- 4 = 2² is 2-powerful (squareful)
- 8 = 2³ is 2-powerful and 3-powerful
- 36 = 2² · 3² is 2-powerful
- 72 = 2³ · 3² is 2-powerful
-/
def IsFull (r n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ r ∣ n

/-- IsFull is decidable for concrete values. -/
instance IsFull.decidable (r n : ℕ) : Decidable (IsFull r n) := by
  unfold IsFull
  infer_instance

/--
A natural number `n` is expressible as a sum of at most `k` many `r`-powerful
numbers.
-/
def SumOfRPowerful (r n : ℕ) : Prop :=
  ∃ s : List ℕ, s.length ≤ r + 1 ∧ (∀ x ∈ s, IsFull r x) ∧ s.sum = n

/-!
## Basic Properties
-/

/-- 0 is r-powerful for all r (vacuously, no prime factors). -/
theorem isFull_zero (r : ℕ) : IsFull r 0 := by
  simp [IsFull]

/-- 1 is r-powerful for all r (vacuously, no prime factors). -/
theorem isFull_one (r : ℕ) : IsFull r 1 := by
  simp [IsFull]

/-- Every natural number is 0-powerful (p^0 = 1 divides everything). -/
theorem isFull_of_zero (n : ℕ) : IsFull 0 n := by
  intro p _
  simp

/-- Every natural number is 1-powerful (p^1 = p divides n if p is a prime factor). -/
theorem isFull_of_one (n : ℕ) : IsFull 1 n := by
  intro p hp
  simp only [pow_one]
  exact dvd_of_mem_primeFactors hp

/-- If n is k-powerful and k ≥ m, then n is m-powerful. -/
theorem isFull_of_le {k m n : ℕ} (hk : m ≤ k) (h : IsFull k n) : IsFull m n := by
  intro p hp
  have hdiv : p ^ k ∣ n := h p hp
  exact Nat.pow_dvd_of_le_of_pow_dvd hk hdiv

/-!
## Concrete Examples of 2-Powerful (Squareful) Numbers
-/

/-- 4 = 2² is 2-powerful. -/
theorem isFull_four : IsFull 2 4 := by native_decide

/-- 8 = 2³ is 2-powerful. -/
theorem isFull_eight : IsFull 2 8 := by native_decide

/-- 9 = 3² is 2-powerful. -/
theorem isFull_nine : IsFull 2 9 := by native_decide

/-- 36 = 2² · 3² is 2-powerful. -/
theorem isFull_thirtySix : IsFull 2 36 := by native_decide

/-!
## Main Theorems

Erdős Problem #1107 has two parts:
1. The general conjecture for r ≥ 2 (OPEN)
2. The special case r = 2 proved by Heath-Brown (1988)
-/

/--
**Erdős Problem #1107** (Open Conjecture):
For all r ≥ 2, every sufficiently large integer is the sum of at most
r + 1 many r-powerful numbers.

This remains open for r > 2. The techniques used for r = 2 do not
generalize directly.
-/
axiom erdos_1107 : ∀ r ≥ 2, ∀ᶠ n in atTop, SumOfRPowerful r n

/--
**Heath-Brown's Theorem (1988)**:
Every sufficiently large integer is the sum of at most three
squareful (2-powerful) numbers.

This resolves Erdős Problem #1107 for r = 2. The proof uses the
theory of ternary quadratic forms and deep results on the
representations of integers by such forms.
-/
axiom erdos_1107_squareful : ∀ᶠ n in atTop, SumOfRPowerful 2 n

/-!
## Verified Example

We verify that small numbers can be expressed as sums of squareful numbers.
-/

/-- 13 = 4 + 9 is the sum of two squareful numbers. -/
theorem sum_example_13 : SumOfRPowerful 2 13 := by
  use [4, 9]
  constructor
  · -- length ≤ 3
    simp
  constructor
  · -- all elements are 2-powerful
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> native_decide
  · -- sum = 13
    native_decide

/-- 17 = 8 + 9 is the sum of two squareful numbers. -/
theorem sum_example_17 : SumOfRPowerful 2 17 := by
  use [8, 9]
  constructor
  · simp
  constructor
  · intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> native_decide
  · native_decide

end Erdos1107
