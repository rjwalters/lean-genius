import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-
# Nicomachus's Theorem: ∑ k³ = (∑ k)²

## Open Question (nicomachus-sum-of-cubes-oq-01)

"The sum of the first n cubes equals the square of the nth triangular number."
Equivalently, the sum of the first n cubes equals the square of the sum of the
first n natural numbers:

    ∑_{k<n} k³ = (∑_{k<n} k)²

## Result

A fully machine-checked, self-contained proof by induction.  The inductive step
hinges on the elementary closed form for the triangular number,
`Finset.sum_range_id_mul_two`, which gives `2·∑_{k<n} k = n·(n−1)`.  Everything
stays inside ℕ; the single subtraction `n − 1` is handled by a case split so
`ring` never sees truncated subtraction.

## Novelty

Mathlib has the Gauss triangular-number identity (`sum_range_id_mul_two`) but
*not* the sum-of-cubes identity.  This file supplies it, together with the
classical "first n cubes" corollary phrased over `range (n+1)`.

0 sorries, 0 axioms.
-/

namespace NicomachusSumOfCubes

open Finset

/-- The algebraic heart of the inductive step: for every `m : ℕ`,
`m³ = m²·(m−1) + m²`.  A case split removes the truncated subtraction so `ring`
closes each branch. -/
theorem cube_eq (m : ℕ) : m ^ 3 = m ^ 2 * (m - 1) + m ^ 2 := by
  cases m with
  | zero => rfl
  | succ p => simp only [Nat.succ_sub_one]; ring

/-- **Nicomachus's Theorem.**  The sum of the first `n` cubes equals the square
of the sum of the first `n` natural numbers (i.e. the square of the `n`-th
triangular number):

`∑_{k<n} k³ = (∑_{k<n} k)²`. -/
theorem sum_cubes (n : ℕ) :
    ∑ k ∈ range n, k ^ 3 = (∑ k ∈ range n, k) ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    -- Goal: (∑ k ∈ range m, k)² + m³ = (∑ k ∈ range m, k + m)²
    have h2 : 2 * (∑ k ∈ range m, k) = m * (m - 1) := by
      have h := sum_range_id_mul_two m; omega
    have expand :
        (∑ k ∈ range m, k + m) ^ 2
          = (∑ k ∈ range m, k) ^ 2 + (2 * (∑ k ∈ range m, k)) * m + m ^ 2 := by
      ring
    rw [expand, h2, cube_eq m]
    ring

/-- **Sum of the first `n` cubes** (the `1`-indexed "first `n` cubes" phrasing).
Since the `k = 0` term vanishes, summing over `range (n+1)` counts `1³,…,n³`,
and the identity reads `∑_{k=0}^{n} k³ = (∑_{k=0}^{n} k)²`. -/
theorem sum_cubes_first (n : ℕ) :
    ∑ k ∈ range (n + 1), k ^ 3 = (∑ k ∈ range (n + 1), k) ^ 2 :=
  sum_cubes (n + 1)

/-- The closed-form triangular version: four times the sum of the first `n`
cubes equals the square of `n·(n−1)`, the doubled triangular number squared.
Stated multiplicatively to stay axiom- and division-free in ℕ. -/
theorem four_mul_sum_cubes (n : ℕ) :
    4 * (∑ k ∈ range n, k ^ 3) = (n * (n - 1)) ^ 2 := by
  have hcube := sum_cubes n
  have h2 := sum_range_id_mul_two n
  -- 4·∑k³ = 4·(∑k)² = (2·∑k)² = ((∑k)·2)² = (n·(n−1))²
  calc
    4 * (∑ k ∈ range n, k ^ 3)
        = 4 * (∑ k ∈ range n, k) ^ 2 := by rw [hcube]
    _ = ((∑ k ∈ range n, k) * 2) ^ 2 := by ring
    _ = (n * (n - 1)) ^ 2 := by rw [h2]

end NicomachusSumOfCubes
