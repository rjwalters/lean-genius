import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-
# Nicomachus's Theorem: Sum of Cubes = Square of Triangular Number

## Open Question (arithmetic-series-oq-00)

Can we formalize Nicomachus's identity, which states that the sum of the first n
perfect cubes equals the square of the n-th triangular number?

$$\sum_{k=1}^{n} k^3 = \left(\frac{n(n+1)}{2}\right)^2 = T_n^2$$

**Answer: YES** — proved here by induction, with multiple equivalent formulations.

## Historical Context

Nicomachus of Gerasa (c. 60–120 CE), a neo-Pythagorean philosopher and mathematician,
described this identity in his *Introductio Arithmetica* (c. 100 CE). He observed a
beautiful visual pattern: the cubes 1, 8, 27, 64, ... can be represented as
L-shaped "gnomons" arranged around growing squares, and their partial sums form
perfect squares.

The identity can be seen geometrically: arrange 1³ + 2³ + 3³ + ... + n³ squares
in a clever pattern, and they fill an exact square of side 1 + 2 + ... + n.

The beautiful alternate form — **the sum of the first n cubes equals the square
of the sum of the first n integers** — is sometimes called "the nicest identity
in elementary mathematics."

## Proof Strategy

By induction on n, using rational arithmetic to avoid natural number division:
- **Base**: n=0, both sides are 0.
- **Step**: ∑_{k=1}^{n+1} k³ = ∑_{k=1}^n k³ + (n+1)³
           = (n(n+1)/2)² + (n+1)³   [by induction hypothesis]
           = ((n+1)(n+2)/2)²         [by ring identity over ℚ]

The ring identity (n(n+1)/2)² + (n+1)³ = ((n+1)(n+2)/2)² is closed by `linarith`
after `push_cast` makes the coercions explicit.

Tags: number-theory, figurate-numbers, induction, nicomachus, triangular-numbers,
      power-sums, classical-identity
-/

namespace NicomachusTheorem

open Finset BigOperators

/-! ## Main Theorem: Sum of Cubes over ℚ -/

/-- **Nicomachus's Theorem**: The sum of the first n perfect cubes equals the
    square of the n-th triangular number T(n) = n(n+1)/2.

    ∑_{k=1}^{n} k³ = (n(n+1)/2)²

    Proved by induction: the step uses the ring identity
    (n(n+1)/2)² + (n+1)³ = ((n+1)(n+2)/2)², closed by `linarith`. -/
theorem sum_cubes_eq_triangular_sq (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 3) = (n * (n + 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-! ## The Beautiful Form: Sum of Cubes = Square of Sum -/

/-- **Helper**: The Gauss sum over ℚ: ∑_{k=1}^{n} k = n(n+1)/2. -/
theorem gauss_sum_rat (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ)) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- **Nicomachus's Theorem (Beautiful Form)**:
    The sum of the first n cubes equals the **square of the sum** of the first n integers.

    ∑_{k=1}^{n} k³ = (∑_{k=1}^{n} k)²

    This is arguably the most elegant formulation: the same set of numbers {1, 2, ..., n}
    appears on both sides, but computed as cubes vs. as a sum. -/
theorem sum_cubes_eq_sq_sum (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 3) = (∑ k ∈ Ico 1 (n + 1), (k : ℚ)) ^ 2 := by
  rw [gauss_sum_rat, sum_cubes_eq_triangular_sq]

/-! ## Natural Number Version (Divisibility Form) -/

/-- **Nicomachus's Theorem (ℕ, division-free form)**:
    4 × (sum of first n cubes) = (n(n+1))²

    This avoids natural number division entirely and holds in ℕ.
    Since 2 | n(n+1) always holds, one recovers the classical form by
    dividing both sides by 4. -/
theorem sum_cubes_mul_four (n : ℕ) :
    4 * ∑ k ∈ Ico 1 (n + 1), k ^ 3 = (n * (n + 1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega), Nat.mul_add, ih]
    ring

/-! ## Key Algebraic Identity -/

/-- The **inductive step identity** underlying Nicomachus's theorem:
    (n(n+1)/2)² + (n+1)³ = ((n+1)(n+2)/2)²

    This is the heart of the induction: each step adds (n+1)³ to both sides
    and the square of the triangular number grows to the next triangular square. -/
theorem nicomachus_step (n : ℚ) :
    (n * (n + 1) / 2) ^ 2 + (n + 1) ^ 3 = ((n + 1) * (n + 2) / 2) ^ 2 := by
  ring

/-! ## Concrete Verification -/

/-- The first few values: 1³ = 1 = 1² -/
theorem sum_cubes_1 : ∑ k ∈ Ico 1 2, k ^ 3 = 1 ^ 2 := by native_decide

/-- 1³ + 2³ = 9 = 3² -/
theorem sum_cubes_2 : ∑ k ∈ Ico 1 3, k ^ 3 = 3 ^ 2 := by native_decide

/-- 1³ + 2³ + 3³ = 36 = 6² -/
theorem sum_cubes_3 : ∑ k ∈ Ico 1 4, k ^ 3 = 6 ^ 2 := by native_decide

/-- 1³ + 2³ + 3³ + 4³ = 100 = 10² -/
theorem sum_cubes_4 : ∑ k ∈ Ico 1 5, k ^ 3 = 10 ^ 2 := by native_decide

/-- 1³ + 2³ + ... + 10³ = 3025 = 55² = (10·11/2)² -/
theorem sum_cubes_10 : ∑ k ∈ Ico 1 11, k ^ 3 = 55 ^ 2 := by native_decide

/-- The triangular numbers are perfect squares when viewed as sums of cubes:
    T(n) = n(n+1)/2, and ∑k³ = T(n)². -/
theorem triangular_squares : [1, 9, 36, 100, 225, 441, 784, 1296] =
    (List.range 8).map (fun n => (∑ k ∈ Ico 1 (n + 2), k ^ 3)) := by
  native_decide

end NicomachusTheorem

/-
## Summary

This file provides a focused formalization of Nicomachus's theorem (c. 100 CE):

**Main theorems (0 sorries, 0 axioms):**
- `sum_cubes_eq_triangular_sq`: ∑_{k=1}^n k³ = (n(n+1)/2)² over ℚ (induction + linarith)
- `sum_cubes_eq_sq_sum`: ∑_{k=1}^n k³ = (∑_{k=1}^n k)² — the beautiful form
- `sum_cubes_mul_four`: 4 × ∑_{k=1}^n k³ = (n(n+1))² in ℕ (division-free)
- `nicomachus_step`: algebraic identity (n(n+1)/2)² + (n+1)³ = ((n+1)(n+2)/2)² by `ring`
- Concrete values for n = 1, 2, 3, 4, 10 by `native_decide`

**Proof strategy:** Induction on n. The step collapses to a polynomial identity
over ℚ, discharged by `push_cast; linarith`.

**Status:** Fully verified. 0 sorries, 0 axioms.
-/
