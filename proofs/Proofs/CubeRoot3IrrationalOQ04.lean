/-
Proof: First partial quotient of the simple continued fraction of cbrt3.
Date: 2026-05-11
Research: cube-root-3-irrational-oq-04, S2 (researcher-10)

This is the first Lean iteration on cube-root-3-irrational-oq-04 after
the S1 OBSERVE survey (PR #17718). The deliverable is the leading
integer part of `∛3`:

  `⌊∛3⌋ = 1`.

This corresponds to `a₀ = 1` in the simple continued fraction prefix
`[1; 2, 3, 1, 4, …]` of OEIS A002945. Subsequent partial quotients are
left to future sessions (S3, S4, …).
-/

import Proofs.CubeRoot3Irrational
import Mathlib

/-!
# Continued fraction prefix of ∛3 — first partial quotient

Let `cbrt3 := (3 : ℝ) ^ (1/3 : ℝ)` (from `Proofs/CubeRoot3Irrational.lean`).
The simple continued fraction of `cbrt3` is non-periodic (Lagrange 1770),
so a finite formalization can only verify a fixed-length prefix one
partial quotient at a time. This file handles the first one.

## Strategy

`⌊cbrt3⌋ = 1` reduces to the two real-arithmetic bounds

  `1 ≤ cbrt3`   and   `cbrt3 < 2`

each provable by cubing and substituting `cbrt3 ^ 3 = 3` (from
`CubeRoot3Irrational.cbrt3_cubed`):

  `1 = 1^3 ≤ cbrt3^3 = 3` gives the lower bound,
  `cbrt3^3 = 3 < 8 = 2^3` gives the upper bound.

The cubing step is discharged by `nlinarith` from the explicit factorization
`cbrt3^3 = cbrt3 * cbrt3 * cbrt3`.

No axioms. The proof depends only on `CubeRoot3Irrational.cbrt3_cubed`
and Mathlib's floor API (`Int.le_floor`, `Int.floor_lt`).
-/

namespace CubeRoot3IrrationalOQ04

open CubeRoot3Irrational

/-- `∛3 ≥ 0`. Immediate from the rpow definition: real powers of a
non-negative base are non-negative. -/
theorem cbrt3_nonneg : (0 : ℝ) ≤ cbrt3 := by
  unfold cbrt3
  exact Real.rpow_nonneg (by norm_num) _

/-- `1 ≤ ∛3`. By contradiction: if `cbrt3 < 1` with `0 ≤ cbrt3`, then
`cbrt3 ^ 3 < 1`, contradicting `cbrt3 ^ 3 = 3`. -/
theorem one_le_cbrt3 : (1 : ℝ) ≤ cbrt3 := by
  by_contra h
  push_neg at h
  have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
  -- From `0 ≤ cbrt3 < 1`: `cbrt3 * cbrt3 ≤ cbrt3`.
  have h2 : cbrt3 * cbrt3 ≤ cbrt3 := by nlinarith [h, hp]
  -- Hence `cbrt3 ^ 3 < 1`.
  have h3 : cbrt3 ^ 3 < 1 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]
    nlinarith [h, h2, hp]
  rw [cbrt3_cubed] at h3
  linarith

/-- `∛3 < 2`. By contradiction: if `2 ≤ cbrt3`, then `cbrt3 ^ 3 ≥ 8`,
contradicting `cbrt3 ^ 3 = 3`. -/
theorem cbrt3_lt_two : cbrt3 < (2 : ℝ) := by
  by_contra h
  push_neg at h
  have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
  -- From `2 ≤ cbrt3`: `cbrt3 * cbrt3 ≥ 4`.
  have h2 : (4 : ℝ) ≤ cbrt3 * cbrt3 := by nlinarith [h, hp]
  -- Hence `cbrt3 ^ 3 ≥ 8`.
  have h3 : (8 : ℝ) ≤ cbrt3 ^ 3 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]
    nlinarith [h, h2, hp]
  rw [cbrt3_cubed] at h3
  linarith

/-- **First partial quotient of the simple CF of `∛3`.**

  `⌊∛3⌋ = 1`.

This is `a₀ = 1` in the prefix `[1; 2, 3, 1, 4, …]` of OEIS A002945.

Proof: combine `one_le_cbrt3` and `cbrt3_lt_two` with the standard
floor characterization `Int.le_floor` / `Int.floor_lt`. -/
theorem cbrt3_floor_eq_one : ⌊cbrt3⌋ = (1 : ℤ) := by
  apply le_antisymm
  · -- `⌊cbrt3⌋ ≤ 1`: `cbrt3 < 2` ⟹ `⌊cbrt3⌋ < 2` ⟹ `⌊cbrt3⌋ ≤ 1`.
    have h : ⌊cbrt3⌋ < (2 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast cbrt3_lt_two
    omega
  · -- `1 ≤ ⌊cbrt3⌋`: `1 ≤ cbrt3` ⟹ `1 ≤ ⌊cbrt3⌋`.
    rw [Int.le_floor]
    exact_mod_cast one_le_cbrt3

end CubeRoot3IrrationalOQ04
