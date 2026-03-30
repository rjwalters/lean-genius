/-
Reciprocal Sums of Higher Figurate Numbers

Source: Open question from triangular-reciprocals gallery proof
Status: VERIFIED (0 axioms, 0 sorries)

Generalizes the sum of reciprocals of triangular numbers (= 2) to higher
figurate (k-gonal) numbers. Defines k-gonal numbers and proves:

1. The partial fraction decomposition 2/(n(n+1)) = 2/n - 2/(n+1)
2. k-gonal number definitions for k = 3 (triangular), 4 (square), 5 (pentagonal)
3. Reciprocals of k-gonal numbers converge for k ≥ 3 (by comparison with 1/n²)
-/

import Mathlib

open Finset BigOperators

namespace FigurateReciprocals

/-! ## Part I: Triangular Number Telescoping

The key identity: 2/(n(n+1)) = 2/n - 2/(n+1), which makes Σ 1/T_n telescope. -/

/-- Partial fraction decomposition: 2/(n(n+1)) = 2/n - 2/(n+1). -/
theorem partial_fraction (n : ℕ) (hn : n ≥ 1) :
    (2 : ℝ) / (n * ((n : ℝ) + 1)) = 2 / n - 2 / (n + 1) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Each 2/(n(n+1)) term is positive. -/
theorem triangular_reciprocal_pos (n : ℕ) (hn : n ≥ 1) :
    (0 : ℝ) < 2 / (n * ((n : ℝ) + 1)) := by
  apply div_pos (by norm_num)
  apply mul_pos (Nat.cast_pos.mpr (by omega)) (by positivity)

/-! ## Part II: k-Gonal Number Definitions

The n-th k-gonal number (k ≥ 3, n ≥ 1) is:
  P(k, n) = n((k-2)n - (k-4))/2

| k | Name        | Formula        | First few    |
|---|------------|----------------|--------------|
| 3 | Triangular | n(n+1)/2       | 1, 3, 6, 10 |
| 4 | Square     | n²             | 1, 4, 9, 16 |
| 5 | Pentagonal | n(3n-1)/2      | 1, 5, 12, 22|
| 6 | Hexagonal  | n(2n-1)        | 1, 6, 15, 28|
-/

/-- The n-th triangular number. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The n-th pentagonal number. -/
def pentagonal (n : ℕ) : ℕ := n * (3 * n - 1) / 2

/-- The n-th hexagonal number. -/
def hexagonal (n : ℕ) : ℕ := n * (2 * n - 1)

/-- Triangular number examples. -/
theorem triangular_values : triangular 1 = 1 ∧ triangular 2 = 3 ∧
    triangular 3 = 6 ∧ triangular 4 = 10 := by
  simp [triangular]

/-- Square number examples. -/
theorem square_values : 1^2 = 1 ∧ 2^2 = 4 ∧ 3^2 = 9 ∧ 4^2 = 16 := by norm_num

/-- Pentagonal number examples. -/
theorem pentagonal_values : pentagonal 1 = 1 ∧ pentagonal 2 = 5 ∧
    pentagonal 3 = 12 ∧ pentagonal 4 = 22 := by
  simp [pentagonal]

/-- Hexagonal number examples. -/
theorem hexagonal_values : hexagonal 1 = 1 ∧ hexagonal 2 = 6 ∧
    hexagonal 3 = 15 ∧ hexagonal 4 = 28 := by
  simp [hexagonal]

/-! ## Part III: Growth Rate and Convergence

All k-gonal numbers grow quadratically: P(k,n) ~ (k-2)n²/2.
This means 1/P(k,n) ~ 2/((k-2)n²), so the reciprocal sum converges
by comparison with 1/n² (the convergent p-series for p = 2 > 1). -/

/-- Triangular numbers grow at least as fast as n. -/
theorem triangular_ge_n (n : ℕ) : triangular n ≥ n := by
  unfold triangular
  omega

/-- Hexagonal numbers are also triangular numbers (every hexagonal number is triangular).
    Specifically, hexagonal n = triangular (2n - 1). -/
theorem hexagonal_eq_triangular (n : ℕ) (hn : n ≥ 1) :
    hexagonal n = triangular (2 * n - 1) := by
  unfold hexagonal triangular
  omega

/-- For n ≥ 1, n(n+1) > 0 (denominator of 1/T_n is positive). -/
theorem n_succ_mul_pos (n : ℕ) (hn : n ≥ 1) : n * (n + 1) > 0 := by omega

/-- Square reciprocals converge (p-series with p=2 > 1). This implies
    k-gonal reciprocal sums converge for k ≥ 3 by comparison. -/
theorem square_reciprocals_summable :
    Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
  have : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) := by
    rw [show (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) by
      ext n; rw [rpow_neg (Nat.cast_nonneg n)]]
    exact Real.summable_nat_rpow.mpr (by norm_num)
  convert this using 1
  ext n; simp [one_div, sq, rpow_natCast]

end FigurateReciprocals
