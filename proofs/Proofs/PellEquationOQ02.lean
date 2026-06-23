import Mathlib

/-!
# Pell's Equation OQ-02: The Size of the Fundamental Solution

## The Open Question

The parent (`PellEquation.lean`) records open questions about the **size of the fundamental
solution** of `x² − D y² = 1`: heuristically `log(x₁ + y₁√D) ≈ √D`, but the distribution is
poorly understood, and its relationship to the continued-fraction period is subtle.

## What this file proves

We give the elementary, rigorous facts about the size of solutions, using Mathlib's
`Pell.Solution₁` theory:

* `x_sq_ge_d_add_one`: every nontrivial solution (`x > 1`) satisfies `x² ≥ D + 1`, i.e.
  `x > √D` — the rigorous lower bound behind the heuristic `x₁ ≈ √D`;
* `IsFundamental.x_sq_ge_d_add_one`: the fundamental solution obeys the same bound;
* `IsFundamental.is_minimal`: the fundamental solution has the **smallest** `x` among all
  nontrivial solutions (Mathlib's `IsFundamental.x_le_x`), so its size is the genuine extremal
  quantity the open question asks about;
* concrete fundamental solutions for `D = 2, 3, 5` with their sizes, illustrating the irregular
  growth `(3,2), (2,1), (9,4)`.

**Honest scope.** The deep content — the *upper* bound / distribution of `x₁` and its link to the
continued-fraction period — remains open; this file pins down the elementary lower bound and the
extremal (minimality) characterization.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace PellEquationOQ02

open Pell Pell.Solution₁

variable {d : ℤ}

/-- **Lower bound on the size of a nontrivial solution.** Any solution with `x > 1` satisfies
    `x² ≥ D + 1` (so `x > √D`): since `y ≠ 0` forces `y² ≥ 1` and `D > 0`, the Pell relation
    `x² = 1 + D y² ≥ 1 + D`. -/
theorem x_sq_ge_d_add_one {a : Solution₁ d} (ha : 1 < a.x) : a.x ^ 2 ≥ d + 1 := by
  have hd : 0 < d := Solution₁.d_pos_of_one_lt_x ha
  have hy : a.y ≠ 0 := Solution₁.y_ne_zero_of_one_lt_x ha
  have hy1 : 1 ≤ a.y ^ 2 := by
    have h0 : a.y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    have h1 := sq_nonneg a.y
    omega
  have hx := a.prop_x
  nlinarith [mul_nonneg hd.le (by linarith : (0 : ℤ) ≤ a.y ^ 2 - 1)]

/-- The fundamental solution satisfies the same size lower bound `x² ≥ D + 1`. -/
theorem IsFundamental.x_sq_ge_d_add_one {a : Solution₁ d} (h : IsFundamental a) :
    a.x ^ 2 ≥ d + 1 :=
  _root_.PellEquationOQ02.x_sq_ge_d_add_one h.1

/-- **The fundamental solution is the smallest.** Among all nontrivial solutions, the fundamental
    one minimizes `x` — so the "size of the fundamental solution" is a genuine extremal quantity.
    (Restatement of Mathlib's `IsFundamental.x_le_x`.) -/
theorem IsFundamental.is_minimal {a : Solution₁ d} (h : IsFundamental a) {b : Solution₁ d}
    (hb : 1 < b.x) : a.x ≤ b.x :=
  h.x_le_x hb

/-! ## Concrete fundamental solutions for small D -/

/-- `(3, 2)` solves `x² − 2y² = 1` (the fundamental solution for `D = 2`). -/
def sol2 : Solution₁ (2 : ℤ) := Solution₁.mk 3 2 (by norm_num)

theorem sol2_x : sol2.x = 3 := by simp [sol2]
theorem sol2_y : sol2.y = 2 := by simp [sol2]

/-- `(2, 1)` solves `x² − 3y² = 1` (the fundamental solution for `D = 3`). -/
def sol3 : Solution₁ (3 : ℤ) := Solution₁.mk 2 1 (by norm_num)

theorem sol3_x : sol3.x = 2 := by simp [sol3]

/-- `(9, 4)` solves `x² − 5y² = 1` (the fundamental solution for `D = 5`). -/
def sol5 : Solution₁ (5 : ℤ) := Solution₁.mk 9 4 (by norm_num)

theorem sol5_x : sol5.x = 9 := by simp [sol5]

/-- The concrete solutions illustrate the size lower bound `x² ≥ D + 1`:
    `9 ≥ 3`, `4 ≥ 4`, `81 ≥ 6`. The irregular jump `x₁ = 3, 2, 9` for `D = 2, 3, 5` is the
    "poorly understood distribution" of the open question. -/
theorem concrete_bounds :
    sol2.x ^ 2 ≥ (2 : ℤ) + 1 ∧ sol3.x ^ 2 ≥ (3 : ℤ) + 1 ∧ sol5.x ^ 2 ≥ (5 : ℤ) + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sol2_x, sol3_x, sol5_x] <;> norm_num

end PellEquationOQ02

/-!
## Summary

The elementary size theory of Pell solutions:

- `x_sq_ge_d_add_one`: every nontrivial solution has `x² ≥ D + 1` (`x > √D`).
- `IsFundamental.x_sq_ge_d_add_one`, `IsFundamental.is_minimal`: the fundamental solution obeys
  the bound and is the smallest nontrivial solution.
- `sol2`, `sol3`, `sol5` and `concrete_bounds`: fundamental solutions `(3,2), (2,1), (9,4)` for
  `D = 2, 3, 5`, illustrating both the bound and the irregular growth.

The upper bound / distribution of `x₁` and its continued-fraction-period connection remain open.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
