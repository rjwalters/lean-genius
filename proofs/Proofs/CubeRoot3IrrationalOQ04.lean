/-
Proof: First three partial quotients of the simple continued fraction of cbrt3.
Date: 2026-05-11 (S2), 2026-05-12 (S3, S4)
Research: cube-root-3-irrational-oq-04, S2 (researcher-10) → S3 (researcher-8) → S4 (researcher-3)

This file develops the leading partial quotients of the simple continued
fraction of `∛3`:

  `⌊∛3⌋ = 1`                                  — `a₀` (S2)
  `⌊1/(∛3 - 1)⌋ = 2`                          — `a₁` (S3)
  `⌊1/(1/(∛3 - 1) - 2)⌋ = 3`                  — `a₂` (S4, this iteration)

corresponding to the prefix `[1; 2, 3, 1, 4, …]` of OEIS A002945.
Subsequent partial quotients (`a₃ = 1`, `a₄ = 4`) are left to future sessions
(S5+).
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

/-! ## Third partial quotient: `a₂ = 3`

The third partial quotient of the simple CF is

  `a₂ = ⌊1/(1/(∛3 - 1) - 2)⌋`,

which we show equals `3`.

The two strict bounds needed are

  `10/7 < cbrt3`   and   `cbrt3 < 13/9`,

each proved by cubing. The cube targets are

  `(10/7)^3 = 1000/343 < 3 = 1029/343` (strict: `1000 < 1029`),
  `(13/9)^3 = 2197/729 > 3 = 2187/729` (strict: `2197 > 2187`).

Both cube boundaries are within `0.1` of `3`, so the cubing argument is
delicate but follows the same template as S2/S3.

Algebraic chain: from `10/7 < cbrt3 < 13/9` we get `3/7 < cbrt3 - 1 < 4/9`,
hence `9/4 < 1/(cbrt3-1) < 7/3`, hence `1/4 < 1/(cbrt3-1) - 2 < 1/3`, hence
`3 < 1/(1/(cbrt3-1) - 2) < 4`, so the floor equals `3`.
-/

/-- `10/7 < ∛3`. Cube target: `(10/7)^3 = 1000/343 < 1029/343 = 3`. -/
theorem ten_sevenths_lt_cbrt3 : (10/7 : ℝ) < cbrt3 := by
  by_contra h
  push_neg at h
  have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
  -- From `cbrt3 ≤ 10/7`: `cbrt3 ^ 2 ≤ 100/49`.
  have h2 : cbrt3 * cbrt3 ≤ 100/49 := by nlinarith [h, hp]
  -- Hence `cbrt3 ^ 3 ≤ 1000/343`.
  have h3 : cbrt3 ^ 3 ≤ 1000/343 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]
    nlinarith [h, h2, hp]
  rw [cbrt3_cubed] at h3
  linarith

/-- `∛3 < 13/9`. Cube target: `(13/9)^3 = 2197/729 > 2187/729 = 3`. -/
theorem cbrt3_lt_thirteen_ninths : cbrt3 < (13/9 : ℝ) := by
  by_contra h
  push_neg at h
  have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
  -- From `13/9 ≤ cbrt3`: `cbrt3 ^ 2 ≥ 169/81`.
  have h2 : (169/81 : ℝ) ≤ cbrt3 * cbrt3 := by nlinarith [h, hp]
  -- Hence `cbrt3 ^ 3 ≥ 2197/729`.
  have h3 : (2197/729 : ℝ) ≤ cbrt3 ^ 3 := by
    have eq : cbrt3 ^ 3 = cbrt3 * cbrt3 * cbrt3 := by ring
    rw [eq]
    nlinarith [h, h2, hp]
  rw [cbrt3_cubed] at h3
  linarith

/-- **Third partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(∛3 - 1) - 2)⌋ = 3`.

This is `a₂ = 3` in the prefix `[1; 2, 3, 1, 4, …]` of OEIS A002945.

Proof: from `10/7 < cbrt3 < 13/9` derive
`9/4 < 1/(cbrt3-1) < 7/3`, hence `1/4 < 1/(cbrt3-1) - 2 < 1/3`, hence
`3 < 1/(1/(cbrt3-1) - 2) < 4`. The floor identity follows by
`le_antisymm` using `Int.le_floor` / `Int.floor_lt`. -/
theorem cbrt3_a2 : ⌊1 / (1 / (cbrt3 - 1) - 2)⌋ = (3 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0`.
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- Step 2: `9/4 < 1/(cbrt3-1)` from `cbrt3 < 13/9`.
  have hinner_gt : (9/4 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(9/4) * (cbrt3 - 1) < 1`, i.e. `9 cbrt3 - 9 < 4`, i.e. `cbrt3 < 13/9`.
    linarith [cbrt3_lt_thirteen_ninths]
  -- Step 3: `1/(cbrt3-1) < 7/3` from `10/7 < cbrt3`.
  have hinner_lt : 1 / (cbrt3 - 1) < (7/3 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (7/3) * (cbrt3 - 1)`, i.e. `3 < 7 cbrt3 - 7`, i.e. `10/7 < cbrt3`.
    linarith [ten_sevenths_lt_cbrt3]
  -- Step 4: `0 < 1/(cbrt3-1) - 2` from `9/4 < 1/(cbrt3-1)`.
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 5: floor antisymmetry.
  apply le_antisymm
  · -- `⌊1/x₂⌋ ≤ 3`: from `1/x₂ < 4`.
    have hlt : 1 / (1 / (cbrt3 - 1) - 2) < (4 : ℝ) := by
      rw [div_lt_iff₀ hpos2]
      -- Goal: `1 < 4 * (1/(cbrt3-1) - 2) = 4 · 1/(cbrt3-1) - 8`,
      -- which from `hinner_gt : 9/4 < 1/(cbrt3-1)` reduces to `9 < 4/(cbrt3-1)`.
      linarith [hinner_gt]
    have hflt : ⌊1 / (1 / (cbrt3 - 1) - 2)⌋ < (4 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `3 ≤ ⌊1/x₂⌋`: from `3 ≤ 1/x₂` (in fact `3 < 1/x₂` is strict; we use `≤`).
    have hge : (3 : ℝ) ≤ 1 / (1 / (cbrt3 - 1) - 2) := by
      rw [le_div_iff₀ hpos2]
      -- Goal: `3 * (1/(cbrt3-1) - 2) ≤ 1`, i.e. `3 · 1/(cbrt3-1) - 6 ≤ 1`,
      -- which from `hinner_lt : 1/(cbrt3-1) < 7/3` reduces to `3/(cbrt3-1) < 7`.
      linarith [hinner_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

end CubeRoot3IrrationalOQ04
