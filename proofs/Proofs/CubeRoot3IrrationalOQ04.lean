/-
Proof: First four partial quotients of the simple continued fraction of cbrt3.
Date: 2026-05-11 (S2), 2026-05-12 (S3, S4, S5)
Research: cube-root-3-irrational-oq-04, S2 (researcher-10) → S3 (researcher-8)
          → S4 (researcher-3) → S5 (researcher-5)

This file develops the leading partial quotients of the simple continued
fraction of `∛3`:

  `⌊∛3⌋ = 1`                                          — `a₀` (S2)
  `⌊1/(∛3 - 1)⌋ = 2`                                  — `a₁` (S3)
  `⌊1/(1/(∛3 - 1) - 2)⌋ = 3`                          — `a₂` (S4)
  `⌊1/(1/(1/(∛3 - 1) - 2) - 3)⌋ = 1`                  — `a₃` (S5, this iteration)

corresponding to the prefix `[1; 2, 3, 1, 4, …]` of OEIS A002945.
The remaining partial quotient (`a₄ = 4`) is left to future sessions (S6+).

The S5 lower bound `23/16 < cbrt3` is imported from
`Proofs/CubeRoot3IrrationalOQ04Helpers.lean` (S5-prep, researcher-1), where
it is proved in two lines via the cubing-iff helper
`Cbrt3Helpers.lt_cbrt3_iff_cube_lt`. The upper bound `cbrt3 < 13/9` is the
S4 `cbrt3_lt_thirteen_ninths` already in this file.
-/

import Proofs.CubeRoot3Irrational
import Proofs.CubeRoot3IrrationalOQ04Helpers
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

/-! ## Step S5: fourth partial quotient

The fourth partial quotient of the simple CF is

  `a₃ = ⌊1/(1/(1/(∛3 - 1) - 2) - 3)⌋`,

which we show equals `1`.

The two strict bounds needed are

  `23/16 < cbrt3`   and   `cbrt3 < 13/9`,

each proved by cubing. The lower bound `23/16 < cbrt3` is
`Cbrt3Helpers.twenty_three_sixteenths_lt_cbrt3` from
`Proofs/CubeRoot3IrrationalOQ04Helpers.lean` (S5-prep — cube target
`12167/4096 < 12288/4096 = 3`). The upper bound is the S4-proved
`cbrt3_lt_thirteen_ninths` above.

Both cube boundaries are very close to `3` (`12167/4096 ≈ 2.970` and
`2197/729 ≈ 3.014`), confirming that `(23/16, 13/9)` is a very tight
two-sided sandwich for `cbrt3` — the next convergents `62/43, 75/52`
will be tighter still.

Algebraic chain (`x₂ := 1/(cbrt3-1) - 2`, `x₃ := 1/x₂ - 3`):

```
  23/16 < cbrt3   < 13/9
  7/16  < cbrt3-1 < 4/9
  9/4   < 1/(cbrt3-1) < 16/7
  1/4   < x₂      < 2/7
  7/2   < 1/x₂    < 4
  1/2   < x₃      < 1
  1     < 1/x₃    < 2     (this gives ⌊1/x₃⌋ = 1)
```

All seven steps are linear (after inverting strictly-positive
denominators), so the proof is a chain of `lt_div_iff₀` / `div_lt_iff₀`
/ `le_div_iff₀` rewrites with `linarith` closing each new bound from
the previous. -/

/-- **Fourth partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(1/(∛3 - 1) - 2) - 3)⌋ = 1`.

This is `a₃ = 1` in the prefix `[1; 2, 3, 1, 4, …]` of OEIS A002945.

Proof: from `23/16 < cbrt3 < 13/9` derive successively
`9/4 < 1/(cbrt3-1) < 16/7`, `1/4 < 1/(cbrt3-1) - 2 < 2/7`,
`7/2 < 1/(1/(cbrt3-1) - 2) < 4`, `1/2 < 1/(1/(cbrt3-1) - 2) - 3 < 1`,
and finally `1 < 1/(1/(1/(cbrt3-1) - 2) - 3) < 2`. The floor identity
follows by `le_antisymm` using `Int.le_floor` / `Int.floor_lt`. -/
theorem cbrt3_a3 :
    ⌊1 / (1 / (1 / (cbrt3 - 1) - 2) - 3)⌋ = (1 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S5 lower bound: `23/16 < cbrt3` (from the cubing-iff helper).
  have h_lo : (23/16 : ℝ) < cbrt3 :=
    Cbrt3Helpers.twenty_three_sixteenths_lt_cbrt3
  -- Step 2: `9/4 < 1/(cbrt3-1)` from `cbrt3 < 13/9`.
  have hy1_gt : (9/4 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(9/4) * (cbrt3 - 1) < 1`, i.e. `cbrt3 < 13/9`.
    linarith [cbrt3_lt_thirteen_ninths]
  -- Step 3: `1/(cbrt3-1) < 16/7` from `23/16 < cbrt3`.
  have hy1_lt : 1 / (cbrt3 - 1) < (16/7 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (16/7) * (cbrt3 - 1)`, i.e. `23/16 < cbrt3`.
    linarith [h_lo]
  -- Step 4: `x₂ := 1/(cbrt3-1) - 2` satisfies `1/4 < x₂ < 2/7`.
  have hx2_gt : (1/4 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (2/7 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 5: `1/x₂` satisfies `7/2 < 1/x₂ < 4`.
  have hy2_gt : (7/2 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    -- Goal: `(7/2) * x₂ < 1`, i.e. `x₂ < 2/7`.
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (4 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    -- Goal: `1 < 4 * x₂`, i.e. `1/4 < x₂`.
    linarith [hx2_gt]
  -- Step 6: `x₃ := 1/x₂ - 3` satisfies `1/2 < x₃ < 1`.
  have hx3_gt : (1/2 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (1 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- Step 7: floor antisymmetry on `1/x₃ ∈ (1, 2)`.
  apply le_antisymm
  · -- `⌊1/x₃⌋ ≤ 1`: from `1/x₃ < 2`.
    have hlt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (2 : ℝ) := by
      rw [div_lt_iff₀ hpos3]
      -- Goal: `1 < 2 * x₃`, i.e. `1/2 < x₃`.
      linarith [hx3_gt]
    have hflt : ⌊1 / (1 / (1 / (cbrt3 - 1) - 2) - 3)⌋ < (2 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `1 ≤ ⌊1/x₃⌋`: from `1 ≤ 1/x₃` (in fact `1 < 1/x₃` strictly).
    have hge : (1 : ℝ) ≤ 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
      rw [le_div_iff₀ hpos3]
      -- Goal: `1 * x₃ ≤ 1`, i.e. `x₃ ≤ 1` (from the strict `x₃ < 1`).
      linarith [hx3_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

end CubeRoot3IrrationalOQ04
