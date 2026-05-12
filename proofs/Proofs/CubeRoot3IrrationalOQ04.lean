/-
Proof: First two partial quotients of the simple continued fraction of cbrt3.
Date: 2026-05-11 (S2), 2026-05-12 (S3)
Research: cube-root-3-irrational-oq-04, S2 (researcher-10) → S3 (researcher-8)

This file develops the leading partial quotients of the simple continued
fraction of `∛3`:

  `⌊∛3⌋ = 1`           — `a₀` (S2)
  `⌊1/(∛3 - 1)⌋ = 2`   — `a₁` (S3, this iteration)

corresponding to the prefix `[1; 2, 3, 1, 4, …]` of OEIS A002945.
Subsequent partial quotients (`a₂ = 3`, `a₃ = 1`, `a₄ = 4`) are left to
future sessions (S4+).
-/

import Proofs.CubeRoot3Irrational
import Mathlib

/-!
# Continued fraction prefix of ∛3 — first two partial quotients

Let `cbrt3 := (3 : ℝ) ^ (1/3 : ℝ)` (from `Proofs/CubeRoot3Irrational.lean`).
The simple continued fraction of `cbrt3` is non-periodic (Lagrange 1770),
so a finite formalization can only verify a fixed-length prefix one
partial quotient at a time. This file handles `a₀` and `a₁`.

## Strategy

Each partial-quotient identity reduces to two real-arithmetic bounds:

* `a₀ = 1` ← `1 ≤ cbrt3 < 2`     (cube targets: `1 < 3 < 8`)
* `a₁ = 2` ← `4/3 < cbrt3 < 3/2` (cube targets: `64/27 < 3 < 27/8`)

Each bound is proved by cubing both sides and substituting
`cbrt3 ^ 3 = 3` (from `CubeRoot3Irrational.cbrt3_cubed`). The cubing
step is discharged by `nlinarith` from the explicit factorization
`cbrt3^3 = cbrt3 * cbrt3 * cbrt3`.

The floor identities are then assembled by `le_antisymm` from the two
halves via `Int.le_floor` / `Int.floor_lt`. For `a₁` the algebraic
manipulation of `1/(cbrt3-1)` uses `div_lt_iff₀` and `le_div_iff₀`
after establishing `0 < cbrt3 - 1`.

No axioms. The proof depends only on `CubeRoot3Irrational.cbrt3_cubed`
and Mathlib's floor / ordered-field API.
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

/-! ## Second partial quotient: `a₁ = 2`

The second partial quotient of the simple CF is `a₁ = ⌊1/(cbrt3 - 1)⌋`,
which we show equals `2`.

The two strict bounds needed are

  `4/3 < cbrt3`   and   `cbrt3 < 3/2`,

each proved by cubing (cube targets `64/27 < 3 < 27/8`).
-/

/-- `4/3 < ∛3`. Cube target: `(4/3)^3 = 64/27 < 3`. -/
theorem four_thirds_lt_cbrt3 : (4/3 : ℝ) < cbrt3 := by
  by_contra h
  push_neg at h
  have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
  -- From `cbrt3 ≤ 4/3`: `cbrt3 ^ 2 ≤ 16/9`.
  have h2 : cbrt3 * cbrt3 ≤ 16/9 := by nlinarith [h, hp]
  -- Hence `cbrt3 ^ 3 ≤ 64/27`.
  have h3 : cbrt3 ^ 3 ≤ 64/27 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]
    nlinarith [h, h2, hp]
  rw [cbrt3_cubed] at h3
  linarith

/-- `∛3 < 3/2`. Cube target: `(3/2)^3 = 27/8 > 3`. -/
theorem cbrt3_lt_three_halves : cbrt3 < (3/2 : ℝ) := by
  by_contra h
  push_neg at h
  have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
  -- From `3/2 ≤ cbrt3`: `cbrt3 ^ 2 ≥ 9/4`.
  have h2 : (9/4 : ℝ) ≤ cbrt3 * cbrt3 := by nlinarith [h, hp]
  -- Hence `cbrt3 ^ 3 ≥ 27/8`.
  have h3 : (27/8 : ℝ) ≤ cbrt3 ^ 3 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]
    nlinarith [h, h2, hp]
  rw [cbrt3_cubed] at h3
  linarith

/-- **Second partial quotient of the simple CF of `∛3`.**

  `⌊1/(∛3 - 1)⌋ = 2`.

This is `a₁ = 2` in the prefix `[1; 2, 3, 1, 4, …]` of OEIS A002945.

Proof: the strict bounds `4/3 < cbrt3 < 3/2` give `1/3 < cbrt3 - 1 < 1/2`,
hence `2 < 1/(cbrt3 - 1) < 3`. The floor identity follows by
`le_antisymm` using `Int.le_floor` / `Int.floor_lt`. -/
theorem cbrt3_a1 : ⌊1 / (cbrt3 - 1)⌋ = (2 : ℤ) := by
  -- `cbrt3 - 1 > 0`: follows from `4/3 < cbrt3`.
  have hpos : (0 : ℝ) < cbrt3 - 1 := by
    have := four_thirds_lt_cbrt3
    linarith
  apply le_antisymm
  · -- `⌊1/(cbrt3-1)⌋ ≤ 2`: from `1/(cbrt3-1) < 3`.
    have hlt : 1 / (cbrt3 - 1) < (3 : ℝ) := by
      rw [div_lt_iff₀ hpos]
      -- Goal: `1 < 3 * (cbrt3 - 1)`, i.e. `cbrt3 > 4/3`.
      linarith [four_thirds_lt_cbrt3]
    have hflt : ⌊1 / (cbrt3 - 1)⌋ < (3 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `2 ≤ ⌊1/(cbrt3-1)⌋`: from `2 ≤ 1/(cbrt3-1)`.
    have hge : (2 : ℝ) ≤ 1 / (cbrt3 - 1) := by
      rw [le_div_iff₀ hpos]
      -- Goal: `2 * (cbrt3 - 1) ≤ 1`, i.e. `cbrt3 ≤ 3/2`.
      linarith [cbrt3_lt_three_halves]
    rw [Int.le_floor]
    exact_mod_cast hge

end CubeRoot3IrrationalOQ04
