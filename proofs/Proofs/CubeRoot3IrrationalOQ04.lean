/-
Proof: First seven partial quotients of the simple continued fraction of cbrt3.
Date: 2026-05-11 (S2), 2026-05-12 (S3, S4, S5), 2026-05-13 (S6, S7, S8)
Research: cube-root-3-irrational-oq-04, S2 (researcher-10) → S3 (researcher-8)
          → S4 (researcher-3) → S5 (researcher-5) → S6 (researcher-11)
          → S7 (researcher-1) → S8 (researcher-10)

This file develops the leading partial quotients of the simple continued
fraction of `∛3`:

  `⌊∛3⌋ = 1`                                                            — `a₀` (S2)
  `⌊1/(∛3 - 1)⌋ = 2`                                                    — `a₁` (S3)
  `⌊1/(1/(∛3 - 1) - 2)⌋ = 3`                                            — `a₂` (S4)
  `⌊1/(1/(1/(∛3 - 1) - 2) - 3)⌋ = 1`                                    — `a₃` (S5)
  `⌊1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1)⌋ = 4`                            — `a₄` (S6)
  `⌊1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4)⌋ = 1`                    — `a₅` (S7)
  `⌊1/(1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4) - 1)⌋ = 5`            — `a₆` (S8, this iteration)

corresponding to the prefix `[1; 2, 3, 1, 4, 1, 5, …]` of OEIS A002945.
The next partial quotient (`a₇`, currently believed to be `1`) is left
to future sessions (S9+).

The S5 lower bound `23/16 < cbrt3` is imported from
`Proofs/CubeRoot3IrrationalOQ04Helpers.lean` (S5-prep, researcher-1).
The S6 bounds `62/43 < cbrt3 < 75/52` are imported from the same helper
file (S6-prep, researcher-11), each proved in two lines via the
cubing-iff helpers `Cbrt3Helpers.lt_cbrt3_iff_cube_lt` /
`Cbrt3Helpers.cbrt3_lt_iff_three_lt_cube`. The S7 new lower bound
`437/303 < cbrt3` (the sixth CF convergent, cube gap `≈ 3.3·10⁻⁵`)
is added to the same helper file (S7-prep, researcher-1). The S8 new
upper bound `cbrt3 < 512/355` (the seventh CF convergent, cube gap
`≈ 2.5·10⁻⁵`; the recursion uses `a₇ = 1` per OEIS A002945, giving
`p₇/q₇ = (1·437+75)/(1·303+52) = 512/355`) is added to the same
helper file (S8-prep, this iteration).
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

/-! ## Step S6: fifth partial quotient

The fifth partial quotient of the simple CF is

  `a₄ = ⌊1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1)⌋`,

which we show equals `4`.

The two strict bounds needed are

  `62/43 < cbrt3`   and   `cbrt3 < 75/52`,

each proved by cubing in `CubeRoot3IrrationalOQ04Helpers.lean`
(`sixty_two_over_forty_three_lt_cbrt3` / `cbrt3_lt_seventy_five_over_fifty_two`).
The two cube targets `238328/79507 < 3` and `3 < 421875/140608` differ
from `3` by only `193/79507 ≈ 2.4·10⁻³` and `51/140608 ≈ 3.6·10⁻⁴`
respectively — the tightest cubing sandwich in the prefix so far,
consistent with `62/43` being the fifth convergent.

Algebraic chain (`x₂ := 1/(cbrt3-1) - 2`, `x₃ := 1/x₂ - 3`,
`x₄ := 1/x₃ - 1`):

```
  62/43 < cbrt3 < 75/52
  19/43 < cbrt3-1 < 23/52
  52/23 < 1/(cbrt3-1) < 43/19
  6/23  < x₂    < 5/19
  19/5  < 1/x₂  < 23/6
  4/5   < x₃    < 5/6
  6/5   < 1/x₃  < 5/4
  1/5   < x₄    < 1/4
  4     < 1/x₄  < 5      (this gives ⌊1/x₄⌋ = 4)
```

All nine reciprocation/subtraction steps are linear after inverting
strictly-positive denominators (each `hposᵢ` follows by `linarith`
from the previous strict lower bound), so the proof is the same
`lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain as S5, one step
deeper. The final floor identity uses `Int.le_floor` / `Int.floor_lt`. -/

/-- **Fifth partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1)⌋ = 4`.

This is `a₄ = 4` in the prefix `[1; 2, 3, 1, 4, …]` of OEIS A002945.

Proof: from `62/43 < cbrt3 < 75/52` derive successively
`52/23 < 1/(cbrt3-1) < 43/19`, `6/23 < x₂ < 5/19`,
`19/5 < 1/x₂ < 23/6`, `4/5 < x₃ < 5/6`,
`6/5 < 1/x₃ < 5/4`, `1/5 < x₄ < 1/4`, and finally
`4 < 1/x₄ < 5`. The floor identity follows by `le_antisymm` using
`Int.le_floor` / `Int.floor_lt`. -/
theorem cbrt3_a4 :
    ⌊1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1)⌋ = (4 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S6 cubing bounds: `62/43 < cbrt3 < 75/52` (from the cubing-iff helpers).
  have h_lo : (62/43 : ℝ) < cbrt3 :=
    Cbrt3Helpers.sixty_two_over_forty_three_lt_cbrt3
  have h_hi : cbrt3 < (75/52 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_seventy_five_over_fifty_two
  -- Step 2: `52/23 < 1/(cbrt3-1)` from `cbrt3 < 75/52`.
  have hy1_gt : (52/23 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(52/23) * (cbrt3 - 1) < 1`, i.e. `cbrt3 < 75/52`.
    linarith [h_hi]
  -- Step 3: `1/(cbrt3-1) < 43/19` from `62/43 < cbrt3`.
  have hy1_lt : 1 / (cbrt3 - 1) < (43/19 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (43/19) * (cbrt3 - 1)`, i.e. `62/43 < cbrt3`.
    linarith [h_lo]
  -- Step 4: `x₂ := 1/(cbrt3-1) - 2` satisfies `6/23 < x₂ < 5/19`.
  have hx2_gt : (6/23 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (5/19 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 5: `1/x₂` satisfies `19/5 < 1/x₂ < 23/6`.
  have hy2_gt : (19/5 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    -- Goal: `(19/5) * x₂ < 1`, i.e. `x₂ < 5/19`.
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (23/6 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    -- Goal: `1 < (23/6) * x₂`, i.e. `6/23 < x₂`.
    linarith [hx2_gt]
  -- Step 6: `x₃ := 1/x₂ - 3` satisfies `4/5 < x₃ < 5/6`.
  have hx3_gt : (4/5 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (5/6 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- Step 7: `1/x₃` satisfies `6/5 < 1/x₃ < 5/4`.
  have hy3_gt : (6/5 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    -- Goal: `(6/5) * x₃ < 1`, i.e. `x₃ < 5/6`.
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (5/4 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    -- Goal: `1 < (5/4) * x₃`, i.e. `4/5 < x₃`.
    linarith [hx3_gt]
  -- Step 8: `x₄ := 1/x₃ - 1` satisfies `1/5 < x₄ < 1/4`.
  have hx4_gt : (1/5 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (1/4 : ℝ) := by linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- Step 9: floor antisymmetry on `1/x₄ ∈ (4, 5)`.
  apply le_antisymm
  · -- `⌊1/x₄⌋ ≤ 4`: from `1/x₄ < 5`.
    have hlt : 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (5 : ℝ) := by
      rw [div_lt_iff₀ hpos4]
      -- Goal: `1 < 5 * x₄`, i.e. `1/5 < x₄`.
      linarith [hx4_gt]
    have hflt : ⌊1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1)⌋ < (5 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `4 ≤ ⌊1/x₄⌋`: from `4 ≤ 1/x₄` (in fact `4 < 1/x₄` strictly).
    have hge : (4 : ℝ) ≤ 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
      rw [le_div_iff₀ hpos4]
      -- Goal: `4 * x₄ ≤ 1`, i.e. `x₄ ≤ 1/4` (from the strict `x₄ < 1/4`).
      linarith [hx4_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

/-! ## Step S7: sixth partial quotient

The sixth partial quotient of the simple CF is

  `a₅ = ⌊1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4)⌋`,

which we show equals `1`.

The two strict bounds needed are

  `437/303 < cbrt3`   and   `cbrt3 < 75/52`,

each proved by cubing in `CubeRoot3IrrationalOQ04Helpers.lean`
(`four_thirty_seven_over_three_oh_three_lt_cbrt3` /
`cbrt3_lt_seventy_five_over_fifty_two`). The upper bound is reused
from S6; only the lower bound is new (it is the sixth convergent
`p₆/q₆ = 437/303`, succeeding S6's `p₄/q₄ = 62/43`).

The cube target `83453453/27818127 < 3` differs from `3` by only
`928/27818127 ≈ 3.3·10⁻⁵` — almost two orders of magnitude tighter
than S6's lower-side gap of `2.4·10⁻³`. This is the tightest cubing
boundary in the prefix so far, consistent with `437/303` being the
sixth convergent.

Algebraic chain (`x₂ := 1/(cbrt3-1) - 2`, `x₃ := 1/x₂ - 3`,
`x₄ := 1/x₃ - 1`, `x₅ := 1/x₄ - 4`):

```
  437/303 < cbrt3 < 75/52
  134/303 < cbrt3-1 < 23/52
  52/23   < 1/(cbrt3-1) < 303/134
  6/23    < x₂    < 35/134
  134/35  < 1/x₂  < 23/6
  29/35   < x₃    < 5/6
  6/5     < 1/x₃  < 35/29
  1/5     < x₄    < 6/29
  29/6    < 1/x₄  < 5
  5/6     < x₅    < 1
  1       < 1/x₅  < 6/5    (this gives ⌊1/x₅⌋ = 1)
```

All eleven reciprocation/subtraction steps are linear after inverting
strictly-positive denominators, so the proof is the same
`lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain as S6, one step
deeper. The final floor identity uses `Int.le_floor` / `Int.floor_lt`. -/

/-- **Sixth partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4)⌋ = 1`.

This is `a₅ = 1` in the prefix `[1; 2, 3, 1, 4, 1, …]` of OEIS A002945.

Proof: from `437/303 < cbrt3 < 75/52` derive successively
`52/23 < 1/(cbrt3-1) < 303/134`, `6/23 < x₂ < 35/134`,
`134/35 < 1/x₂ < 23/6`, `29/35 < x₃ < 5/6`,
`6/5 < 1/x₃ < 35/29`, `1/5 < x₄ < 6/29`,
`29/6 < 1/x₄ < 5`, `5/6 < x₅ < 1`, and finally
`1 < 1/x₅ < 6/5`. The floor identity follows by `le_antisymm` using
`Int.le_floor` / `Int.floor_lt`. -/
theorem cbrt3_a5 :
    ⌊1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4)⌋ = (1 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S7 cubing bounds: `437/303 < cbrt3 < 75/52` (cubing-iff helpers).
  have h_lo : (437/303 : ℝ) < cbrt3 :=
    Cbrt3Helpers.four_thirty_seven_over_three_oh_three_lt_cbrt3
  have h_hi : cbrt3 < (75/52 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_seventy_five_over_fifty_two
  -- Step 2: `52/23 < 1/(cbrt3-1) < 303/134`.
  have hy1_gt : (52/23 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(52/23) * (cbrt3 - 1) < 1`, i.e. `cbrt3 < 75/52`.
    linarith [h_hi]
  have hy1_lt : 1 / (cbrt3 - 1) < (303/134 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (303/134) * (cbrt3 - 1)`, i.e. `437/303 < cbrt3`.
    linarith [h_lo]
  -- Step 3: `x₂ := 1/(cbrt3-1) - 2` satisfies `6/23 < x₂ < 35/134`.
  have hx2_gt : (6/23 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (35/134 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 4: `1/x₂` satisfies `134/35 < 1/x₂ < 23/6`.
  have hy2_gt : (134/35 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    -- Goal: `(134/35) * x₂ < 1`, i.e. `x₂ < 35/134`.
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (23/6 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    -- Goal: `1 < (23/6) * x₂`, i.e. `6/23 < x₂`.
    linarith [hx2_gt]
  -- Step 5: `x₃ := 1/x₂ - 3` satisfies `29/35 < x₃ < 5/6`.
  have hx3_gt : (29/35 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (5/6 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- Step 6: `1/x₃` satisfies `6/5 < 1/x₃ < 35/29`.
  have hy3_gt : (6/5 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    -- Goal: `(6/5) * x₃ < 1`, i.e. `x₃ < 5/6`.
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (35/29 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    -- Goal: `1 < (35/29) * x₃`, i.e. `29/35 < x₃`.
    linarith [hx3_gt]
  -- Step 7: `x₄ := 1/x₃ - 1` satisfies `1/5 < x₄ < 6/29`.
  have hx4_gt : (1/5 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (6/29 : ℝ) := by linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- Step 8: `1/x₄` satisfies `29/6 < 1/x₄ < 5`.
  have hy4_gt : (29/6 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
    rw [lt_div_iff₀ hpos4]
    -- Goal: `(29/6) * x₄ < 1`, i.e. `x₄ < 6/29`.
    linarith [hx4_lt]
  have hy4_lt : 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (5 : ℝ) := by
    rw [div_lt_iff₀ hpos4]
    -- Goal: `1 < 5 * x₄`, i.e. `1/5 < x₄`.
    linarith [hx4_gt]
  -- Step 9: `x₅ := 1/x₄ - 4` satisfies `5/6 < x₅ < 1`.
  have hx5_gt : (5/6 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by
    linarith
  have hx5_lt : 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 < (1 : ℝ) := by
    linarith
  have hpos5 : (0 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by
    linarith
  -- Step 10: floor antisymmetry on `1/x₅ ∈ (1, 6/5)`.
  apply le_antisymm
  · -- `⌊1/x₅⌋ ≤ 1`: from `1/x₅ < 2`.
    have hlt :
        1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) < (2 : ℝ) := by
      rw [div_lt_iff₀ hpos5]
      -- Goal: `1 < 2 * x₅`. From `x₅ > 5/6 > 1/2`, immediate.
      linarith [hx5_gt]
    have hflt :
        ⌊1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4)⌋ < (2 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `1 ≤ ⌊1/x₅⌋`: from `1 ≤ 1/x₅` (in fact `1 < 1/x₅` strictly).
    have hge :
        (1 : ℝ) ≤ 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) := by
      rw [le_div_iff₀ hpos5]
      -- Goal: `1 * x₅ ≤ 1`, i.e. `x₅ ≤ 1` (from the strict `x₅ < 1`).
      linarith [hx5_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

/-! ## Step S8: seventh partial quotient

The seventh partial quotient of the simple CF is

  `a₆ = ⌊1/(1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4) - 1)⌋`,

which we show equals `5`.

The two strict bounds needed are

  `437/303 < cbrt3`   and   `cbrt3 < 512/355`,

each proved by cubing in `CubeRoot3IrrationalOQ04Helpers.lean`
(`four_thirty_seven_over_three_oh_three_lt_cbrt3` /
`cbrt3_lt_five_twelve_over_three_fifty_five`). The lower bound is
reused from S7; only the upper bound is new (it is the seventh
convergent `p₇/q₇ = 512/355`, with `a₇ = 1` per OEIS A002945:
`p₇ = 1·437 + 75 = 512` and `q₇ = 1·303 + 52 = 355`).

The cube target `512³ = 134_217_728 > 134_216_625 = 3 · 355³` has gap
`1103/44_738_875 ≈ 2.5·10⁻⁵` — comparable to S7's lower-side gap of
`928/27_818_127 ≈ 3.3·10⁻⁵`. The seventh convergent alternates above
the value while the sixth convergent `437/303` lies below; the
sandwich is therefore strictly tight from both sides.

Algebraic chain (`x₂ := 1/(cbrt3-1) - 2`, `x₃ := 1/x₂ - 3`,
`x₄ := 1/x₃ - 1`, `x₅ := 1/x₄ - 4`, `x₆ := 1/x₅ - 1`):

```
  437/303   < cbrt3            < 512/355
  134/303   < cbrt3-1          < 157/355
  355/157   < 1/(cbrt3-1)      < 303/134
  41/157    < x₂               < 35/134
  134/35    < 1/x₂             < 157/41
  29/35     < x₃               < 34/41
  41/34     < 1/x₃             < 35/29
  7/34      < x₄               < 6/29
  29/6      < 1/x₄             < 34/7
  5/6       < x₅               < 6/7
  7/6       < 1/x₅             < 6/5
  1/6       < x₆               < 1/5
  5         < 1/x₆             < 6        (this gives ⌊1/x₆⌋ = 5)
```

All twelve reciprocation/subtraction steps are linear after inverting
strictly-positive denominators, so the proof is the same
`lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain as S7, one step
deeper. The final floor identity uses `Int.le_floor` / `Int.floor_lt`. -/

/-- **Seventh partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4) - 1)⌋ = 5`.

This is `a₆ = 5` in the prefix `[1; 2, 3, 1, 4, 1, 5, 1, …]` of OEIS A002945.

Proof: from `437/303 < cbrt3 < 512/355` derive successively
`355/157 < 1/(cbrt3-1) < 303/134`, `41/157 < x₂ < 35/134`,
`134/35 < 1/x₂ < 157/41`, `29/35 < x₃ < 34/41`,
`41/34 < 1/x₃ < 35/29`, `7/34 < x₄ < 6/29`,
`29/6 < 1/x₄ < 34/7`, `5/6 < x₅ < 6/7`,
`7/6 < 1/x₅ < 6/5`, `1/6 < x₆ < 1/5`, and finally
`5 < 1/x₆ < 6`. The floor identity follows by `le_antisymm` using
`Int.le_floor` / `Int.floor_lt`. -/
theorem cbrt3_a6 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1)⌋
      = (5 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S8 cubing bounds: `437/303 < cbrt3 < 512/355` (cubing-iff helpers).
  have h_lo : (437/303 : ℝ) < cbrt3 :=
    Cbrt3Helpers.four_thirty_seven_over_three_oh_three_lt_cbrt3
  have h_hi : cbrt3 < (512/355 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_five_twelve_over_three_fifty_five
  -- Step 2: `355/157 < 1/(cbrt3-1) < 303/134`.
  have hy1_gt : (355/157 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(355/157) * (cbrt3 - 1) < 1`, i.e. `cbrt3 < 512/355`.
    linarith [h_hi]
  have hy1_lt : 1 / (cbrt3 - 1) < (303/134 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (303/134) * (cbrt3 - 1)`, i.e. `437/303 < cbrt3`.
    linarith [h_lo]
  -- Step 3: `x₂ := 1/(cbrt3-1) - 2` satisfies `41/157 < x₂ < 35/134`.
  have hx2_gt : (41/157 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (35/134 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 4: `1/x₂` satisfies `134/35 < 1/x₂ < 157/41`.
  have hy2_gt : (134/35 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    -- Goal: `(134/35) * x₂ < 1`, i.e. `x₂ < 35/134`.
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (157/41 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    -- Goal: `1 < (157/41) * x₂`, i.e. `41/157 < x₂`.
    linarith [hx2_gt]
  -- Step 5: `x₃ := 1/x₂ - 3` satisfies `29/35 < x₃ < 34/41`.
  have hx3_gt : (29/35 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (34/41 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- Step 6: `1/x₃` satisfies `41/34 < 1/x₃ < 35/29`.
  have hy3_gt : (41/34 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    -- Goal: `(41/34) * x₃ < 1`, i.e. `x₃ < 34/41`.
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (35/29 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    -- Goal: `1 < (35/29) * x₃`, i.e. `29/35 < x₃`.
    linarith [hx3_gt]
  -- Step 7: `x₄ := 1/x₃ - 1` satisfies `7/34 < x₄ < 6/29`.
  have hx4_gt : (7/34 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by
    linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (6/29 : ℝ) := by
    linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- Step 8: `1/x₄` satisfies `29/6 < 1/x₄ < 34/7`.
  have hy4_gt : (29/6 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
    rw [lt_div_iff₀ hpos4]
    -- Goal: `(29/6) * x₄ < 1`, i.e. `x₄ < 6/29`.
    linarith [hx4_lt]
  have hy4_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (34/7 : ℝ) := by
    rw [div_lt_iff₀ hpos4]
    -- Goal: `1 < (34/7) * x₄`, i.e. `7/34 < x₄`.
    linarith [hx4_gt]
  -- Step 9: `x₅ := 1/x₄ - 4` satisfies `5/6 < x₅ < 6/7`.
  have hx5_gt :
      (5/6 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by
    linarith
  have hx5_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 < (6/7 : ℝ) := by
    linarith
  have hpos5 :
      (0 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  -- Step 10: `1/x₅` satisfies `7/6 < 1/x₅ < 6/5`.
  have hy5_gt :
      (7/6 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) := by
    rw [lt_div_iff₀ hpos5]
    -- Goal: `(7/6) * x₅ < 1`, i.e. `x₅ < 6/7`.
    linarith [hx5_lt]
  have hy5_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) < (6/5 : ℝ) := by
    rw [div_lt_iff₀ hpos5]
    -- Goal: `1 < (6/5) * x₅`, i.e. `5/6 < x₅`.
    linarith [hx5_gt]
  -- Step 11: `x₆ := 1/x₅ - 1` satisfies `1/6 < x₆ < 1/5`.
  have hx6_gt :
      (1/6 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  have hx6_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 < (1/5 : ℝ) := by
    linarith
  have hpos6 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  -- Step 12: floor antisymmetry on `1/x₆ ∈ (5, 6)`.
  apply le_antisymm
  · -- `⌊1/x₆⌋ ≤ 5`: from `1/x₆ < 6`.
    have hlt :
        1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1)
          < (6 : ℝ) := by
      rw [div_lt_iff₀ hpos6]
      -- Goal: `1 < 6 * x₆`. From `x₆ > 1/6`, immediate.
      linarith [hx6_gt]
    have hflt :
        ⌊1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1)⌋
          < (6 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `5 ≤ ⌊1/x₆⌋`: from `5 ≤ 1/x₆` (in fact `5 < 1/x₆` strictly).
    have hge :
        (5 : ℝ)
          ≤ 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) := by
      rw [le_div_iff₀ hpos6]
      -- Goal: `5 * x₆ ≤ 1`, i.e. `x₆ ≤ 1/5` (from the strict `x₆ < 1/5`).
      linarith [hx6_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

/-! ## S9 act: eighth partial quotient `a₇ = 1`

For `a₇ = 1` (eighth partial quotient of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of OEIS A002945) we need bounds
on a one-more-level nested fraction. The chain reuses the
`Cbrt3Helpers.cbrt3_lt_five_twelve_over_three_fifty_five` upper bound
(`cbrt3 < 512/355`) but tightens the lower side from S8's `437/303`
to S9's new helper `949/658 < cbrt3` — the eighth convergent
`p₈/q₈ = 949/658` with `a₈ = 1`.

Algebraic chain (`x₂ := 1/(cbrt3-1) - 2`, `x₃ := 1/x₂ - 3`,
`x₄ := 1/x₃ - 1`, `x₅ := 1/x₄ - 4`, `x₆ := 1/x₅ - 1`, `x₇ := 1/x₆ - 5`):

```
  949/658   < cbrt3            < 512/355
  291/658   < cbrt3-1          < 157/355
  355/157   < 1/(cbrt3-1)      < 658/291
  41/157    < x₂               < 76/291
  291/76    < 1/x₂             < 157/41
  63/76     < x₃               < 34/41
  41/34     < 1/x₃             < 76/63
  7/34      < x₄               < 13/63
  63/13     < 1/x₄             < 34/7
  11/13     < x₅               < 6/7
  7/6       < 1/x₅             < 13/11
  1/6       < x₆               < 2/11
  11/2      < 1/x₆             < 6
  1/2       < x₇               < 1
  1         < 1/x₇             < 2        (this gives ⌊1/x₇⌋ = 1)
```

All fourteen reciprocation/subtraction steps are linear after
inverting strictly-positive denominators, so the proof is the same
`lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain as S8, one step
deeper. The final floor identity uses `Int.le_floor` / `Int.floor_lt`. -/

set_option maxHeartbeats 400000 in
/-- **Eighth partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)⌋ = 1`.

This is `a₇ = 1` in the prefix `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of
OEIS A002945.

Proof: from `949/658 < cbrt3 < 512/355` derive successively
`355/157 < 1/(cbrt3-1) < 658/291`, `41/157 < x₂ < 76/291`,
`291/76 < 1/x₂ < 157/41`, `63/76 < x₃ < 34/41`,
`41/34 < 1/x₃ < 76/63`, `7/34 < x₄ < 13/63`,
`63/13 < 1/x₄ < 34/7`, `11/13 < x₅ < 6/7`,
`7/6 < 1/x₅ < 13/11`, `1/6 < x₆ < 2/11`,
`11/2 < 1/x₆ < 6`, `1/2 < x₇ < 1`, and finally
`1 < 1/x₇ < 2`. The floor identity follows by `le_antisymm` using
`Int.le_floor` / `Int.floor_lt`.

Note: the seven-level nesting pushes Lean's term-elaboration above the
default 200_000-heartbeat budget; `set_option maxHeartbeats 400000`
(scoped via `in`) suffices — the proof completes well under that. -/
theorem cbrt3_a7 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)⌋
      = (1 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S9 cubing bounds: `949/658 < cbrt3 < 512/355` (cubing-iff helpers).
  have h_lo : (949/658 : ℝ) < cbrt3 :=
    Cbrt3Helpers.nine_forty_nine_over_six_fifty_eight_lt_cbrt3
  have h_hi : cbrt3 < (512/355 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_five_twelve_over_three_fifty_five
  -- Step 2: `355/157 < 1/(cbrt3-1) < 658/291`.
  have hy1_gt : (355/157 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(355/157) * (cbrt3 - 1) < 1`, i.e. `cbrt3 < 512/355`.
    linarith [h_hi]
  have hy1_lt : 1 / (cbrt3 - 1) < (658/291 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (658/291) * (cbrt3 - 1)`, i.e. `949/658 < cbrt3`.
    linarith [h_lo]
  -- Step 3: `x₂ := 1/(cbrt3-1) - 2` satisfies `41/157 < x₂ < 76/291`.
  have hx2_gt : (41/157 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (76/291 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 4: `1/x₂` satisfies `291/76 < 1/x₂ < 157/41`.
  have hy2_gt : (291/76 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    -- Goal: `(291/76) * x₂ < 1`, i.e. `x₂ < 76/291`.
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (157/41 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    -- Goal: `1 < (157/41) * x₂`, i.e. `41/157 < x₂`.
    linarith [hx2_gt]
  -- Step 5: `x₃ := 1/x₂ - 3` satisfies `63/76 < x₃ < 34/41`.
  have hx3_gt : (63/76 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (34/41 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- Step 6: `1/x₃` satisfies `41/34 < 1/x₃ < 76/63`.
  have hy3_gt : (41/34 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    -- Goal: `(41/34) * x₃ < 1`, i.e. `x₃ < 34/41`.
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (76/63 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    -- Goal: `1 < (76/63) * x₃`, i.e. `63/76 < x₃`.
    linarith [hx3_gt]
  -- Step 7: `x₄ := 1/x₃ - 1` satisfies `7/34 < x₄ < 13/63`.
  have hx4_gt : (7/34 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by
    linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (13/63 : ℝ) := by
    linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- Step 8: `1/x₄` satisfies `63/13 < 1/x₄ < 34/7`.
  have hy4_gt : (63/13 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
    rw [lt_div_iff₀ hpos4]
    -- Goal: `(63/13) * x₄ < 1`, i.e. `x₄ < 13/63`.
    linarith [hx4_lt]
  have hy4_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (34/7 : ℝ) := by
    rw [div_lt_iff₀ hpos4]
    -- Goal: `1 < (34/7) * x₄`, i.e. `7/34 < x₄`.
    linarith [hx4_gt]
  -- Step 9: `x₅ := 1/x₄ - 4` satisfies `11/13 < x₅ < 6/7`.
  have hx5_gt :
      (11/13 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by
    linarith
  have hx5_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 < (6/7 : ℝ) := by
    linarith
  have hpos5 :
      (0 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  -- Step 10: `1/x₅` satisfies `7/6 < 1/x₅ < 13/11`.
  have hy5_gt :
      (7/6 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) := by
    rw [lt_div_iff₀ hpos5]
    -- Goal: `(7/6) * x₅ < 1`, i.e. `x₅ < 6/7`.
    linarith [hx5_lt]
  have hy5_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) < (13/11 : ℝ) := by
    rw [div_lt_iff₀ hpos5]
    -- Goal: `1 < (13/11) * x₅`, i.e. `11/13 < x₅`.
    linarith [hx5_gt]
  -- Step 11: `x₆ := 1/x₅ - 1` satisfies `1/6 < x₆ < 2/11`.
  have hx6_gt :
      (1/6 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  have hx6_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 < (2/11 : ℝ) := by
    linarith
  have hpos6 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  -- Step 12: `1/x₆` satisfies `11/2 < 1/x₆ < 6`.
  have hy6_gt :
      (11/2 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) := by
    rw [lt_div_iff₀ hpos6]
    -- Goal: `(11/2) * x₆ < 1`, i.e. `x₆ < 2/11`.
    linarith [hx6_lt]
  have hy6_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) < (6 : ℝ) := by
    rw [div_lt_iff₀ hpos6]
    -- Goal: `1 < 6 * x₆`, i.e. `1/6 < x₆`.
    linarith [hx6_gt]
  -- Step 13: `x₇ := 1/x₆ - 5` satisfies `1/2 < x₇ < 1`.
  have hx7_gt :
      (1/2 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  have hx7_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 < (1 : ℝ) := by
    linarith
  have hpos7 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  -- Step 14: floor antisymmetry on `1/x₇ ∈ (1, 2)`.
  apply le_antisymm
  · -- `⌊1/x₇⌋ ≤ 1`: from `1/x₇ < 2`.
    have hlt :
        1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)
          < (2 : ℝ) := by
      rw [div_lt_iff₀ hpos7]
      -- Goal: `1 < 2 * x₇`. From `x₇ > 1/2`, immediate.
      linarith [hx7_gt]
    have hflt :
        ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)⌋
          < (2 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `1 ≤ ⌊1/x₇⌋`: from `1 ≤ 1/x₇` (in fact `1 < 1/x₇` strictly).
    have hge :
        (1 : ℝ)
          ≤ 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) := by
      rw [le_div_iff₀ hpos7]
      -- Goal: `1 * x₇ ≤ 1`, i.e. `x₇ ≤ 1` (from the strict `x₇ < 1`).
      linarith [hx7_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

/-! ## S10 act: ninth partial quotient `a₈ = 1`

For `a₈ = 1` (ninth partial quotient of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of OEIS A002945) we extend the
S9 chain by one more reciprocation/subtraction layer. The chain
reuses the S9 lower bound
`Cbrt3Helpers.nine_forty_nine_over_six_fifty_eight_lt_cbrt3`
(`949/658 < cbrt3`) but tightens the upper side from S8's `512/355`
to S10's new helper `cbrt3 < 6206/4303` — the ninth convergent
`p₉/q₉ = 6206/4303` with `a₉ = 6`.

Algebraic chain (`x₂ := 1/(cbrt3-1) - 2`, …, `x₇ := 1/x₆ - 5`,
`x₈ := 1/x₇ - 1`):

```
  949/658   < cbrt3            < 6206/4303
  291/658   < cbrt3-1          < 1903/4303
  4303/1903 < 1/(cbrt3-1)      < 658/291
  497/1903  < x₂               < 76/291
  291/76    < 1/x₂             < 1903/497
  63/76     < x₃               < 412/497
  497/412   < 1/x₃             < 76/63
  85/412    < x₄               < 13/63
  63/13     < 1/x₄             < 412/85
  11/13     < x₅               < 72/85
  85/72     < 1/x₅             < 13/11
  13/72     < x₆               < 2/11
  11/2      < 1/x₆             < 72/13
  1/2       < x₇               < 7/13
  13/7      < 1/x₇             < 2
  6/7       < x₈               < 1
  1         < 1/x₈             < 7/6        (this gives ⌊1/x₈⌋ = 1)
```

All sixteen reciprocation/subtraction steps are linear after
inverting strictly-positive denominators, so the proof is the same
`lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain as S9, one step
deeper. The final floor identity uses `Int.le_floor` / `Int.floor_lt`.

Pre-claim Python sanity check (per
`feedback_researcher_cf_convergent_recursion_direction_trap`):
`6206³ = 239_020_589_816`, `3 · 4303³ = 239_020_578_381`, diff
`+11_435 > 0` confirming `cbrt3 < 6206/4303` (above, as expected for
the odd-index ninth convergent). -/

set_option maxHeartbeats 800000 in
/-- **Ninth partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(1/(1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1)⌋ = 1`.

This is `a₈ = 1` in the prefix `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of
OEIS A002945.

Proof: from `949/658 < cbrt3 < 6206/4303` derive successively
`4303/1903 < 1/(cbrt3-1) < 658/291`, `497/1903 < x₂ < 76/291`,
`291/76 < 1/x₂ < 1903/497`, `63/76 < x₃ < 412/497`,
`497/412 < 1/x₃ < 76/63`, `85/412 < x₄ < 13/63`,
`63/13 < 1/x₄ < 412/85`, `11/13 < x₅ < 72/85`,
`85/72 < 1/x₅ < 13/11`, `13/72 < x₆ < 2/11`,
`11/2 < 1/x₆ < 72/13`, `1/2 < x₇ < 7/13`,
`13/7 < 1/x₇ < 2`, `6/7 < x₈ < 1`, and finally
`1 < 1/x₈ < 7/6`. The floor identity follows by `le_antisymm` using
`Int.le_floor` / `Int.floor_lt`.

Note: the eight-level nesting pushes Lean's term-elaboration above
the S9 budget of 400_000 heartbeats; `set_option maxHeartbeats 800000`
(scoped via `in`) is allotted for the deepest `linarith` /
`div_lt_iff₀` rewrite step on the eight-fold nested fraction. -/
theorem cbrt3_a8 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1)⌋
      = (1 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S10 cubing bounds: `949/658 < cbrt3 < 6206/4303` (cubing-iff helpers).
  have h_lo : (949/658 : ℝ) < cbrt3 :=
    Cbrt3Helpers.nine_forty_nine_over_six_fifty_eight_lt_cbrt3
  have h_hi : cbrt3 < (6206/4303 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_six_two_oh_six_over_four_three_oh_three
  -- Step 2: `4303/1903 < 1/(cbrt3-1) < 658/291`.
  have hy1_gt : (4303/1903 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(4303/1903) * (cbrt3 - 1) < 1`, i.e. `cbrt3 < 6206/4303`.
    linarith [h_hi]
  have hy1_lt : 1 / (cbrt3 - 1) < (658/291 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (658/291) * (cbrt3 - 1)`, i.e. `949/658 < cbrt3`.
    linarith [h_lo]
  -- Step 3: `x₂ := 1/(cbrt3-1) - 2` satisfies `497/1903 < x₂ < 76/291`.
  have hx2_gt : (497/1903 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (76/291 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 4: `1/x₂` satisfies `291/76 < 1/x₂ < 1903/497`.
  have hy2_gt : (291/76 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    -- Goal: `(291/76) * x₂ < 1`, i.e. `x₂ < 76/291`.
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (1903/497 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    -- Goal: `1 < (1903/497) * x₂`, i.e. `497/1903 < x₂`.
    linarith [hx2_gt]
  -- Step 5: `x₃ := 1/x₂ - 3` satisfies `63/76 < x₃ < 412/497`.
  have hx3_gt : (63/76 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (412/497 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- Step 6: `1/x₃` satisfies `497/412 < 1/x₃ < 76/63`.
  have hy3_gt : (497/412 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    -- Goal: `(497/412) * x₃ < 1`, i.e. `x₃ < 412/497`.
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (76/63 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    -- Goal: `1 < (76/63) * x₃`, i.e. `63/76 < x₃`.
    linarith [hx3_gt]
  -- Step 7: `x₄ := 1/x₃ - 1` satisfies `85/412 < x₄ < 13/63`.
  have hx4_gt : (85/412 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by
    linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (13/63 : ℝ) := by
    linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- Step 8: `1/x₄` satisfies `63/13 < 1/x₄ < 412/85`.
  have hy4_gt : (63/13 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
    rw [lt_div_iff₀ hpos4]
    -- Goal: `(63/13) * x₄ < 1`, i.e. `x₄ < 13/63`.
    linarith [hx4_lt]
  have hy4_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (412/85 : ℝ) := by
    rw [div_lt_iff₀ hpos4]
    -- Goal: `1 < (412/85) * x₄`, i.e. `85/412 < x₄`.
    linarith [hx4_gt]
  -- Step 9: `x₅ := 1/x₄ - 4` satisfies `11/13 < x₅ < 72/85`.
  have hx5_gt :
      (11/13 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by
    linarith
  have hx5_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 < (72/85 : ℝ) := by
    linarith
  have hpos5 :
      (0 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  -- Step 10: `1/x₅` satisfies `85/72 < 1/x₅ < 13/11`.
  have hy5_gt :
      (85/72 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) := by
    rw [lt_div_iff₀ hpos5]
    -- Goal: `(85/72) * x₅ < 1`, i.e. `x₅ < 72/85`.
    linarith [hx5_lt]
  have hy5_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) < (13/11 : ℝ) := by
    rw [div_lt_iff₀ hpos5]
    -- Goal: `1 < (13/11) * x₅`, i.e. `11/13 < x₅`.
    linarith [hx5_gt]
  -- Step 11: `x₆ := 1/x₅ - 1` satisfies `13/72 < x₆ < 2/11`.
  have hx6_gt :
      (13/72 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  have hx6_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 < (2/11 : ℝ) := by
    linarith
  have hpos6 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  -- Step 12: `1/x₆` satisfies `11/2 < 1/x₆ < 72/13`.
  have hy6_gt :
      (11/2 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) := by
    rw [lt_div_iff₀ hpos6]
    -- Goal: `(11/2) * x₆ < 1`, i.e. `x₆ < 2/11`.
    linarith [hx6_lt]
  have hy6_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) < (72/13 : ℝ) := by
    rw [div_lt_iff₀ hpos6]
    -- Goal: `1 < (72/13) * x₆`, i.e. `13/72 < x₆`.
    linarith [hx6_gt]
  -- Step 13: `x₇ := 1/x₆ - 5` satisfies `1/2 < x₇ < 7/13`.
  have hx7_gt :
      (1/2 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  have hx7_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 < (7/13 : ℝ) := by
    linarith
  have hpos7 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  -- Step 14: `1/x₇` satisfies `13/7 < 1/x₇ < 2`.
  have hy7_gt :
      (13/7 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) := by
    rw [lt_div_iff₀ hpos7]
    -- Goal: `(13/7) * x₇ < 1`, i.e. `x₇ < 7/13`.
    linarith [hx7_lt]
  have hy7_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) < (2 : ℝ) := by
    rw [div_lt_iff₀ hpos7]
    -- Goal: `1 < 2 * x₇`, i.e. `1/2 < x₇`.
    linarith [hx7_gt]
  -- Step 15: `x₈ := 1/x₇ - 1` satisfies `6/7 < x₈ < 1`.
  have hx8_gt :
      (6/7 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by
    linarith
  have hx8_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 < (1 : ℝ) := by
    linarith
  have hpos8 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by
    linarith
  -- Step 16: floor antisymmetry on `1/x₈ ∈ (1, 7/6)`.
  apply le_antisymm
  · -- `⌊1/x₈⌋ ≤ 1`: from `1/x₈ < 7/6 < 2`.
    have hlt :
        1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1)
          < (2 : ℝ) := by
      rw [div_lt_iff₀ hpos8]
      -- Goal: `1 < 2 * x₈`. From `x₈ > 6/7`, `2*(6/7) = 12/7 > 1`, immediate.
      linarith [hx8_gt]
    have hflt :
        ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1)⌋
          < (2 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `1 ≤ ⌊1/x₈⌋`: from `1 ≤ 1/x₈` (in fact `1 < 1/x₈` strictly).
    have hge :
        (1 : ℝ)
          ≤ 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) := by
      rw [le_div_iff₀ hpos8]
      -- Goal: `1 * x₈ ≤ 1`, i.e. `x₈ ≤ 1` (from the strict `x₈ < 1`).
      linarith [hx8_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

set_option maxHeartbeats 1600000 in
/-- **Tenth partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(1/(1/(1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1)⌋ = 6`.

This is `a₉ = 6` in the prefix `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of
OEIS A002945 — the largest partial quotient in the known prefix.

Proof: from `7155/4961 < cbrt3 < 6206/4303` (S11 lower bound new,
S10 upper bound reused) derive successively
`4303/1903 < 1/(cbrt3-1) < 4961/2194`, `497/1903 < x₂ < 573/2194`,
`2194/573 < 1/x₂ < 1903/497`, `475/573 < x₃ < 412/497`,
`497/412 < 1/x₃ < 573/475`, `85/412 < x₄ < 98/475`,
`475/98 < 1/x₄ < 412/85`, `83/98 < x₅ < 72/85`,
`85/72 < 1/x₅ < 98/83`, `13/72 < x₆ < 15/83`,
`83/15 < 1/x₆ < 72/13`, `8/15 < x₇ < 7/13`,
`13/7 < 1/x₇ < 15/8`, `6/7 < x₈ < 7/8`,
`8/7 < 1/x₈ < 7/6`, `1/7 < x₉ < 1/6`, and finally
`6 < 1/x₉ < 7`. The floor identity follows by `le_antisymm` using
`Int.le_floor` / `Int.floor_lt`.

Note: the nine-level nesting pushes Lean's term-elaboration above
the S10 budget of 800_000 heartbeats; `set_option maxHeartbeats 1600000`
(scoped via `in`) is allotted for the deepest `linarith` /
`div_lt_iff₀` rewrite step on the nine-fold nested fraction. The
empirical 2× per-depth scaling has held through S7–S10. -/
theorem cbrt3_a9 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1)
      - 4) - 1) - 5) - 1) - 1)⌋ = (6 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S11 cubing bounds: `7155/4961 < cbrt3 < 6206/4303` (cubing-iff helpers).
  have h_lo : (7155/4961 : ℝ) < cbrt3 :=
    Cbrt3Helpers.seven_one_five_five_over_four_nine_six_one_lt_cbrt3
  have h_hi : cbrt3 < (6206/4303 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_six_two_oh_six_over_four_three_oh_three
  -- Step 2: `4303/1903 < 1/(cbrt3-1) < 4961/2194`.
  have hy1_gt : (4303/1903 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(4303/1903) * (cbrt3 - 1) < 1`, i.e. `cbrt3 < 6206/4303`.
    linarith [h_hi]
  have hy1_lt : 1 / (cbrt3 - 1) < (4961/2194 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (4961/2194) * (cbrt3 - 1)`, i.e. `7155/4961 < cbrt3`.
    linarith [h_lo]
  -- Step 3: `x₂ := 1/(cbrt3-1) - 2` satisfies `497/1903 < x₂ < 573/2194`.
  have hx2_gt : (497/1903 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (573/2194 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 4: `1/x₂` satisfies `2194/573 < 1/x₂ < 1903/497`.
  have hy2_gt : (2194/573 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    -- Goal: `(2194/573) * x₂ < 1`, i.e. `x₂ < 573/2194`.
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (1903/497 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    -- Goal: `1 < (1903/497) * x₂`, i.e. `497/1903 < x₂`.
    linarith [hx2_gt]
  -- Step 5: `x₃ := 1/x₂ - 3` satisfies `475/573 < x₃ < 412/497`.
  have hx3_gt : (475/573 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (412/497 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- Step 6: `1/x₃` satisfies `497/412 < 1/x₃ < 573/475`.
  have hy3_gt : (497/412 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    -- Goal: `(497/412) * x₃ < 1`, i.e. `x₃ < 412/497`.
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (573/475 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    -- Goal: `1 < (573/475) * x₃`, i.e. `475/573 < x₃`.
    linarith [hx3_gt]
  -- Step 7: `x₄ := 1/x₃ - 1` satisfies `85/412 < x₄ < 98/475`.
  have hx4_gt : (85/412 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by
    linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (98/475 : ℝ) := by
    linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- Step 8: `1/x₄` satisfies `475/98 < 1/x₄ < 412/85`.
  have hy4_gt : (475/98 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
    rw [lt_div_iff₀ hpos4]
    -- Goal: `(475/98) * x₄ < 1`, i.e. `x₄ < 98/475`.
    linarith [hx4_lt]
  have hy4_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (412/85 : ℝ) := by
    rw [div_lt_iff₀ hpos4]
    -- Goal: `1 < (412/85) * x₄`, i.e. `85/412 < x₄`.
    linarith [hx4_gt]
  -- Step 9: `x₅ := 1/x₄ - 4` satisfies `83/98 < x₅ < 72/85`.
  have hx5_gt :
      (83/98 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by
    linarith
  have hx5_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 < (72/85 : ℝ) := by
    linarith
  have hpos5 :
      (0 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  -- Step 10: `1/x₅` satisfies `85/72 < 1/x₅ < 98/83`.
  have hy5_gt :
      (85/72 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) := by
    rw [lt_div_iff₀ hpos5]
    -- Goal: `(85/72) * x₅ < 1`, i.e. `x₅ < 72/85`.
    linarith [hx5_lt]
  have hy5_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) < (98/83 : ℝ) := by
    rw [div_lt_iff₀ hpos5]
    -- Goal: `1 < (98/83) * x₅`, i.e. `83/98 < x₅`.
    linarith [hx5_gt]
  -- Step 11: `x₆ := 1/x₅ - 1` satisfies `13/72 < x₆ < 15/83`.
  have hx6_gt :
      (13/72 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  have hx6_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 < (15/83 : ℝ) := by
    linarith
  have hpos6 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  -- Step 12: `1/x₆` satisfies `83/15 < 1/x₆ < 72/13`.
  have hy6_gt :
      (83/15 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) := by
    rw [lt_div_iff₀ hpos6]
    -- Goal: `(83/15) * x₆ < 1`, i.e. `x₆ < 15/83`.
    linarith [hx6_lt]
  have hy6_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) < (72/13 : ℝ) := by
    rw [div_lt_iff₀ hpos6]
    -- Goal: `1 < (72/13) * x₆`, i.e. `13/72 < x₆`.
    linarith [hx6_gt]
  -- Step 13: `x₇ := 1/x₆ - 5` satisfies `8/15 < x₇ < 7/13`.
  have hx7_gt :
      (8/15 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  have hx7_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 < (7/13 : ℝ) := by
    linarith
  have hpos7 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  -- Step 14: `1/x₇` satisfies `13/7 < 1/x₇ < 15/8`.
  have hy7_gt :
      (13/7 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) := by
    rw [lt_div_iff₀ hpos7]
    -- Goal: `(13/7) * x₇ < 1`, i.e. `x₇ < 7/13`.
    linarith [hx7_lt]
  have hy7_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) < (15/8 : ℝ) := by
    rw [div_lt_iff₀ hpos7]
    -- Goal: `1 < (15/8) * x₇`, i.e. `8/15 < x₇`.
    linarith [hx7_gt]
  -- Step 15: `x₈ := 1/x₇ - 1` satisfies `6/7 < x₈ < 7/8`.
  have hx8_gt :
      (6/7 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by
    linarith
  have hx8_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 < (7/8 : ℝ) := by
    linarith
  have hpos8 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by
    linarith
  -- Step 16: `1/x₈` satisfies `8/7 < 1/x₈ < 7/6`.
  have hy8_gt :
      (8/7 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) := by
    rw [lt_div_iff₀ hpos8]
    -- Goal: `(8/7) * x₈ < 1`, i.e. `x₈ < 7/8`.
    linarith [hx8_lt]
  have hy8_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) < (7/6 : ℝ) := by
    rw [div_lt_iff₀ hpos8]
    -- Goal: `1 < (7/6) * x₈`, i.e. `6/7 < x₈`.
    linarith [hx8_gt]
  -- Step 17: `x₉ := 1/x₈ - 1` satisfies `1/7 < x₉ < 1/6`.
  have hx9_gt :
      (1/7 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by
    linarith
  have hx9_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 < (1/6 : ℝ) := by
    linarith
  have hpos9 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by
    linarith
  -- Step 18: floor antisymmetry on `1/x₉ ∈ (6, 7)`.
  apply le_antisymm
  · -- `⌊1/x₉⌋ ≤ 6`: from `1/x₉ < 7`.
    have hlt :
        1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1)
          < (7 : ℝ) := by
      rw [div_lt_iff₀ hpos9]
      -- Goal: `1 < 7 * x₉`. From `x₉ > 1/7`, `7*(1/7) = 1`, immediate.
      linarith [hx9_gt]
    have hflt :
        ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1)⌋
          < (7 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `6 ≤ ⌊1/x₉⌋`: from `6 ≤ 1/x₉` (in fact `6 < 1/x₉` strictly).
    have hge :
        (6 : ℝ)
          ≤ 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) := by
      rw [le_div_iff₀ hpos9]
      -- Goal: `6 * x₉ ≤ 1`, i.e. `x₉ ≤ 1/6` (from the strict `x₉ < 1/6`).
      linarith [hx9_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

set_option maxHeartbeats 3200000 in
/-- **Eleventh partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(1/(1/(1/(1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6)⌋ = 2`.

This is `a₁₀ = 2` in the prefix `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, …]`
of OEIS A002945.

Proof: from `13361/9264 < cbrt3 < 73011/50623` (S12a lower bound + S12b
upper bound, both true CF convergents) derive successively
`50623/22388 < 1/(cbrt3-1) < 9264/4097`,
`5847/22388 < x₂ < 1070/4097`, `4097/1070 < 1/x₂ < 22388/5847`,
`887/1070 < x₃ < 4847/5847`, `5847/4847 < 1/x₃ < 1070/887`,
`1000/4847 < x₄ < 183/887`, `887/183 < 1/x₄ < 4847/1000`,
`155/183 < x₅ < 847/1000`, `1000/847 < 1/x₅ < 183/155`,
`153/847 < x₆ < 28/155`, `155/28 < 1/x₆ < 847/153`,
`15/28 < x₇ < 82/153`, `153/82 < 1/x₇ < 28/15`,
`71/82 < x₈ < 13/15`, `15/13 < 1/x₈ < 82/71`,
`2/13 < x₉ < 11/71`, `71/11 < 1/x₉ < 13/2`,
`5/11 < x₁₀ < 1/2`, and finally `2 < 1/x₁₀ < 11/5 < 3`.
The floor identity follows by `le_antisymm` using
`Int.le_floor` / `Int.floor_lt`.

Note: the ten-level nesting pushes Lean's term-elaboration above
the S11b budget of 1_600_000 heartbeats; `set_option maxHeartbeats
3200000` (scoped via `in`) is allotted for the deepest `linarith` /
`div_lt_iff₀` rewrite step on the ten-fold nested fraction. The
empirical 2× per-depth scaling has held through S7–S11b. -/
theorem cbrt3_a10 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2)
      - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6)⌋ = (2 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S12 cubing bounds: `13361/9264 < cbrt3 < 73011/50623`.
  have h_lo : (13361/9264 : ℝ) < cbrt3 :=
    Cbrt3Helpers.one_three_three_six_one_over_nine_two_six_four_lt_cbrt3
  have h_hi : cbrt3 < (73011/50623 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_seven_three_oh_one_one_over_five_oh_six_two_three
  -- Step 2: `50623/22388 < 1/(cbrt3-1) < 9264/4097`.
  have hy1_gt : (50623/22388 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(50623/22388) * (cbrt3 - 1) < 1`, i.e. `cbrt3 < 73011/50623`.
    linarith [h_hi]
  have hy1_lt : 1 / (cbrt3 - 1) < (9264/4097 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (9264/4097) * (cbrt3 - 1)`, i.e. `13361/9264 < cbrt3`.
    linarith [h_lo]
  -- Step 3: `x₂ := 1/(cbrt3-1) - 2` satisfies `5847/22388 < x₂ < 1070/4097`.
  have hx2_gt : (5847/22388 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (1070/4097 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 4: `1/x₂` satisfies `4097/1070 < 1/x₂ < 22388/5847`.
  have hy2_gt : (4097/1070 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    -- Goal: `(4097/1070) * x₂ < 1`, i.e. `x₂ < 1070/4097`.
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (22388/5847 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    -- Goal: `1 < (22388/5847) * x₂`, i.e. `5847/22388 < x₂`.
    linarith [hx2_gt]
  -- Step 5: `x₃ := 1/x₂ - 3` satisfies `887/1070 < x₃ < 4847/5847`.
  have hx3_gt : (887/1070 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (4847/5847 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- Step 6: `1/x₃` satisfies `5847/4847 < 1/x₃ < 1070/887`.
  have hy3_gt : (5847/4847 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    -- Goal: `(5847/4847) * x₃ < 1`, i.e. `x₃ < 4847/5847`.
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (1070/887 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    -- Goal: `1 < (1070/887) * x₃`, i.e. `887/1070 < x₃`.
    linarith [hx3_gt]
  -- Step 7: `x₄ := 1/x₃ - 1` satisfies `1000/4847 < x₄ < 183/887`.
  have hx4_gt : (1000/4847 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by
    linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (183/887 : ℝ) := by
    linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- Step 8: `1/x₄` satisfies `887/183 < 1/x₄ < 4847/1000`.
  have hy4_gt : (887/183 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
    rw [lt_div_iff₀ hpos4]
    -- Goal: `(887/183) * x₄ < 1`, i.e. `x₄ < 183/887`.
    linarith [hx4_lt]
  have hy4_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (4847/1000 : ℝ) := by
    rw [div_lt_iff₀ hpos4]
    -- Goal: `1 < (4847/1000) * x₄`, i.e. `1000/4847 < x₄`.
    linarith [hx4_gt]
  -- Step 9: `x₅ := 1/x₄ - 4` satisfies `155/183 < x₅ < 847/1000`.
  have hx5_gt :
      (155/183 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by
    linarith
  have hx5_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 < (847/1000 : ℝ) := by
    linarith
  have hpos5 :
      (0 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  -- Step 10: `1/x₅` satisfies `1000/847 < 1/x₅ < 183/155`.
  have hy5_gt :
      (1000/847 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) := by
    rw [lt_div_iff₀ hpos5]
    -- Goal: `(1000/847) * x₅ < 1`, i.e. `x₅ < 847/1000`.
    linarith [hx5_lt]
  have hy5_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) < (183/155 : ℝ) := by
    rw [div_lt_iff₀ hpos5]
    -- Goal: `1 < (183/155) * x₅`, i.e. `155/183 < x₅`.
    linarith [hx5_gt]
  -- Step 11: `x₆ := 1/x₅ - 1` satisfies `153/847 < x₆ < 28/155`.
  have hx6_gt :
      (153/847 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  have hx6_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 < (28/155 : ℝ) := by
    linarith
  have hpos6 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  -- Step 12: `1/x₆` satisfies `155/28 < 1/x₆ < 847/153`.
  have hy6_gt :
      (155/28 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) := by
    rw [lt_div_iff₀ hpos6]
    -- Goal: `(155/28) * x₆ < 1`, i.e. `x₆ < 28/155`.
    linarith [hx6_lt]
  have hy6_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) < (847/153 : ℝ) := by
    rw [div_lt_iff₀ hpos6]
    -- Goal: `1 < (847/153) * x₆`, i.e. `153/847 < x₆`.
    linarith [hx6_gt]
  -- Step 13: `x₇ := 1/x₆ - 5` satisfies `15/28 < x₇ < 82/153`.
  have hx7_gt :
      (15/28 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  have hx7_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 < (82/153 : ℝ) := by
    linarith
  have hpos7 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  -- Step 14: `1/x₇` satisfies `153/82 < 1/x₇ < 28/15`.
  have hy7_gt :
      (153/82 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) := by
    rw [lt_div_iff₀ hpos7]
    -- Goal: `(153/82) * x₇ < 1`, i.e. `x₇ < 82/153`.
    linarith [hx7_lt]
  have hy7_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) < (28/15 : ℝ) := by
    rw [div_lt_iff₀ hpos7]
    -- Goal: `1 < (28/15) * x₇`, i.e. `15/28 < x₇`.
    linarith [hx7_gt]
  -- Step 15: `x₈ := 1/x₇ - 1` satisfies `71/82 < x₈ < 13/15`.
  have hx8_gt :
      (71/82 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by
    linarith
  have hx8_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 < (13/15 : ℝ) := by
    linarith
  have hpos8 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by
    linarith
  -- Step 16: `1/x₈` satisfies `15/13 < 1/x₈ < 82/71`.
  have hy8_gt :
      (15/13 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) := by
    rw [lt_div_iff₀ hpos8]
    -- Goal: `(15/13) * x₈ < 1`, i.e. `x₈ < 13/15`.
    linarith [hx8_lt]
  have hy8_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) < (82/71 : ℝ) := by
    rw [div_lt_iff₀ hpos8]
    -- Goal: `1 < (82/71) * x₈`, i.e. `71/82 < x₈`.
    linarith [hx8_gt]
  -- Step 17: `x₉ := 1/x₈ - 1` satisfies `2/13 < x₉ < 11/71`.
  have hx9_gt :
      (2/13 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by
    linarith
  have hx9_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 < (11/71 : ℝ) := by
    linarith
  have hpos9 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by
    linarith
  -- Step 18: `1/x₉` satisfies `71/11 < 1/x₉ < 13/2`.
  have hy9_gt :
      (71/11 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) := by
    rw [lt_div_iff₀ hpos9]
    -- Goal: `(71/11) * x₉ < 1`, i.e. `x₉ < 11/71`.
    linarith [hx9_lt]
  have hy9_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) < (13/2 : ℝ) := by
    rw [div_lt_iff₀ hpos9]
    -- Goal: `1 < (13/2) * x₉`, i.e. `2/13 < x₉`.
    linarith [hx9_gt]
  -- Step 19: `x₁₀ := 1/x₉ - 6` satisfies `5/11 < x₁₀ < 1/2`.
  have hx10_gt :
      (5/11 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 := by
    linarith
  have hx10_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 < (1/2 : ℝ) := by
    linarith
  have hpos10 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 := by
    linarith
  -- Step 20: floor antisymmetry on `1/x₁₀ ∈ (2, 11/5)`.
  apply le_antisymm
  · -- `⌊1/x₁₀⌋ ≤ 2`: from `1/x₁₀ < 3`.
    have hlt :
        1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6)
          < (3 : ℝ) := by
      rw [div_lt_iff₀ hpos10]
      -- Goal: `1 < 3 * x₁₀`. From `x₁₀ > 5/11`, `3*(5/11) = 15/11 > 1`.
      linarith [hx10_gt]
    have hflt :
        ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6)⌋
          < (3 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `2 ≤ ⌊1/x₁₀⌋`: from `2 ≤ 1/x₁₀` (in fact `2 < 1/x₁₀` strictly).
    have hge :
        (2 : ℝ)
          ≤ 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) := by
      rw [le_div_iff₀ hpos10]
      -- Goal: `2 * x₁₀ ≤ 1`, i.e. `x₁₀ ≤ 1/2` (from the strict `x₁₀ < 1/2`).
      linarith [hx10_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

set_option maxHeartbeats 6400000 in
/-- **Twelfth partial quotient of the simple CF of `∛3`.**

  `⌊1/(1/(1/(1/(1/(1/(1/(1/(1/(1/(1/(∛3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2)⌋ = 5`.

This is `a₁₁ = 5` in the prefix `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, …]`
of OEIS A002945.

Proof: from `597449/414248 < cbrt3 < 73011/50623` (S13a Helper lower
bound, the true 13th CF convergent, paired with the S12b-introduced
12th CF convergent upper bound) derive successively
`50623/22388 < 1/(cbrt3-1) < 414248/183201`,
`5847/22388 < x₂ < 47846/183201`, `183201/47846 < 1/x₂ < 22388/5847`,
`39663/47846 < x₃ < 4847/5847`, `5847/4847 < 1/x₃ < 47846/39663`,
`1000/4847 < x₄ < 8183/39663`, `39663/8183 < 1/x₄ < 4847/1000`,
`6931/8183 < x₅ < 847/1000`, `1000/847 < 1/x₅ < 8183/6931`,
`153/847 < x₆ < 1252/6931`, `6931/1252 < 1/x₆ < 847/153`,
`671/1252 < x₇ < 82/153`, `153/82 < 1/x₇ < 1252/671`,
`71/82 < x₈ < 581/671`, `671/581 < 1/x₈ < 82/71`,
`90/581 < x₉ < 11/71`, `71/11 < 1/x₉ < 581/90`,
`5/11 < x₁₀ < 41/90`, `90/41 < 1/x₁₀ < 11/5`,
`8/41 < x₁₁ < 1/5`, and finally `5 < 1/x₁₁ < 41/8 < 6`.
The floor identity follows by `le_antisymm` using
`Int.le_floor` / `Int.floor_lt`.

Note: the eleven-level nesting pushes Lean's term-elaboration above
the S12b budget of 3_200_000 heartbeats; `set_option maxHeartbeats
6400000` (scoped via `in`) is allotted for the deepest `linarith` /
`div_lt_iff₀` rewrite step on the eleven-fold nested fraction. The
empirical 2× per-depth scaling has held through S7–S12b. -/
theorem cbrt3_a11 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2)
      - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2)⌋ = (5 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S13 cubing bounds: `597449/414248 < cbrt3 < 73011/50623`.
  have h_lo : (597449/414248 : ℝ) < cbrt3 :=
    Cbrt3Helpers.five_nine_seven_four_four_nine_over_four_one_four_two_four_eight_lt_cbrt3
  have h_hi : cbrt3 < (73011/50623 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_seven_three_oh_one_one_over_five_oh_six_two_three
  -- Step 2: `50623/22388 < 1/(cbrt3-1) < 414248/183201`.
  have hy1_gt : (50623/22388 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    -- Goal: `(50623/22388) * (cbrt3 - 1) < 1`, i.e. `cbrt3 < 73011/50623`.
    linarith [h_hi]
  have hy1_lt : 1 / (cbrt3 - 1) < (414248/183201 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    -- Goal: `1 < (414248/183201) * (cbrt3 - 1)`, i.e. `597449/414248 < cbrt3`.
    linarith [h_lo]
  -- Step 3: `x₂ := 1/(cbrt3-1) - 2` satisfies `5847/22388 < x₂ < 47846/183201`.
  have hx2_gt : (5847/22388 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (47846/183201 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- Step 4: `1/x₂` satisfies `183201/47846 < 1/x₂ < 22388/5847`.
  have hy2_gt : (183201/47846 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    -- Goal: `(183201/47846) * x₂ < 1`, i.e. `x₂ < 47846/183201`.
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (22388/5847 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    -- Goal: `1 < (22388/5847) * x₂`, i.e. `5847/22388 < x₂`.
    linarith [hx2_gt]
  -- Step 5: `x₃ := 1/x₂ - 3` satisfies `39663/47846 < x₃ < 4847/5847`.
  have hx3_gt : (39663/47846 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (4847/5847 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- Step 6: `1/x₃` satisfies `5847/4847 < 1/x₃ < 47846/39663`.
  have hy3_gt : (5847/4847 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (47846/39663 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    linarith [hx3_gt]
  -- Step 7: `x₄ := 1/x₃ - 1` satisfies `1000/4847 < x₄ < 8183/39663`.
  have hx4_gt : (1000/4847 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by
    linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (8183/39663 : ℝ) := by
    linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- Step 8: `1/x₄` satisfies `39663/8183 < 1/x₄ < 4847/1000`.
  have hy4_gt : (39663/8183 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
    rw [lt_div_iff₀ hpos4]
    linarith [hx4_lt]
  have hy4_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (4847/1000 : ℝ) := by
    rw [div_lt_iff₀ hpos4]
    linarith [hx4_gt]
  -- Step 9: `x₅ := 1/x₄ - 4` satisfies `6931/8183 < x₅ < 847/1000`.
  have hx5_gt :
      (6931/8183 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by
    linarith
  have hx5_lt :
      1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 < (847/1000 : ℝ) := by
    linarith
  have hpos5 :
      (0 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  -- Step 10: `1/x₅` satisfies `1000/847 < 1/x₅ < 8183/6931`.
  have hy5_gt :
      (1000/847 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) := by
    rw [lt_div_iff₀ hpos5]
    linarith [hx5_lt]
  have hy5_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) < (8183/6931 : ℝ) := by
    rw [div_lt_iff₀ hpos5]
    linarith [hx5_gt]
  -- Step 11: `x₆ := 1/x₅ - 1` satisfies `153/847 < x₆ < 1252/6931`.
  have hx6_gt :
      (153/847 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  have hx6_lt :
      1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 < (1252/6931 : ℝ) := by
    linarith
  have hpos6 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by
    linarith
  -- Step 12: `1/x₆` satisfies `6931/1252 < 1/x₆ < 847/153`.
  have hy6_gt :
      (6931/1252 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) := by
    rw [lt_div_iff₀ hpos6]
    linarith [hx6_lt]
  have hy6_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) < (847/153 : ℝ) := by
    rw [div_lt_iff₀ hpos6]
    linarith [hx6_gt]
  -- Step 13: `x₇ := 1/x₆ - 5` satisfies `671/1252 < x₇ < 82/153`.
  have hx7_gt :
      (671/1252 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  have hx7_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 < (82/153 : ℝ) := by
    linarith
  have hpos7 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by
    linarith
  -- Step 14: `1/x₇` satisfies `153/82 < 1/x₇ < 1252/671`.
  have hy7_gt :
      (153/82 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) := by
    rw [lt_div_iff₀ hpos7]
    linarith [hx7_lt]
  have hy7_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) < (1252/671 : ℝ) := by
    rw [div_lt_iff₀ hpos7]
    linarith [hx7_gt]
  -- Step 15: `x₈ := 1/x₇ - 1` satisfies `71/82 < x₈ < 581/671`.
  have hx8_gt :
      (71/82 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by
    linarith
  have hx8_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 < (581/671 : ℝ) := by
    linarith
  have hpos8 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by
    linarith
  -- Step 16: `1/x₈` satisfies `671/581 < 1/x₈ < 82/71`.
  have hy8_gt :
      (671/581 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) := by
    rw [lt_div_iff₀ hpos8]
    linarith [hx8_lt]
  have hy8_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) < (82/71 : ℝ) := by
    rw [div_lt_iff₀ hpos8]
    linarith [hx8_gt]
  -- Step 17: `x₉ := 1/x₈ - 1` satisfies `90/581 < x₉ < 11/71`.
  have hx9_gt :
      (90/581 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by
    linarith
  have hx9_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 < (11/71 : ℝ) := by
    linarith
  have hpos9 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by
    linarith
  -- Step 18: `1/x₉` satisfies `71/11 < 1/x₉ < 581/90`.
  have hy9_gt :
      (71/11 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) := by
    rw [lt_div_iff₀ hpos9]
    linarith [hx9_lt]
  have hy9_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) < (581/90 : ℝ) := by
    rw [div_lt_iff₀ hpos9]
    linarith [hx9_gt]
  -- Step 19: `x₁₀ := 1/x₉ - 6` satisfies `5/11 < x₁₀ < 41/90`.
  have hx10_gt :
      (5/11 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 := by
    linarith
  have hx10_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 < (41/90 : ℝ) := by
    linarith
  have hpos10 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 := by
    linarith
  -- Step 20: `1/x₁₀` satisfies `90/41 < 1/x₁₀ < 11/5`.
  have hy10_gt :
      (90/41 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) := by
    rw [lt_div_iff₀ hpos10]
    linarith [hx10_lt]
  have hy10_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) < (11/5 : ℝ) := by
    rw [div_lt_iff₀ hpos10]
    linarith [hx10_gt]
  -- Step 21: `x₁₁ := 1/x₁₀ - 2` satisfies `8/41 < x₁₁ < 1/5`.
  have hx11_gt :
      (8/41 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2 := by
    linarith
  have hx11_lt :
      1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2 < (1/5 : ℝ) := by
    linarith
  have hpos11 :
      (0 : ℝ)
        < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2 := by
    linarith
  -- Step 22: floor antisymmetry on `1/x₁₁ ∈ (5, 41/8) ⊂ (5, 6)`.
  apply le_antisymm
  · -- `⌊1/x₁₁⌋ ≤ 5`: from `1/x₁₁ < 6`.
    have hlt :
        1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2)
          < (6 : ℝ) := by
      rw [div_lt_iff₀ hpos11]
      -- Goal: `1 < 6 * x₁₁`. From `x₁₁ > 8/41`, `6*(8/41) = 48/41 > 1`.
      linarith [hx11_gt]
    have hflt :
        ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2)⌋
          < (6 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `5 ≤ ⌊1/x₁₁⌋`: from `5 ≤ 1/x₁₁` (in fact `5 < 1/x₁₁` strictly).
    have hge :
        (5 : ℝ)
          ≤ 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) := by
      rw [le_div_iff₀ hpos11]
      -- Goal: `5 * x₁₁ ≤ 1`, i.e. `x₁₁ ≤ 1/5` (from the strict `x₁₁ < 1/5`).
      linarith [hx11_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

end CubeRoot3IrrationalOQ04
