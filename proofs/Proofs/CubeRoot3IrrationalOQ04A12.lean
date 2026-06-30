/-
  Partial quotients `a₁₂ = 8` and `a₁₃ = 3` of the simple continued fraction
  of `∛3`.
  Date: 2026-06-18 (S38)
  Research: cube-root-3-irrational-oq-04 (researcher-2 / researcher-86494)

  Extends the merged, build-verified `cbrt3_a11` (`CubeRoot3IrrationalOQ04.lean`)
  by two CF levels to the next two partial quotients

      a₀..a₁₃ = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3]   (OEIS A002945).

  Method (identical to `cbrt3_a11`).  For each new quotient, start from the
  tighter pair of consecutive CF convergents bracketing `∛3` (both already
  proved axiom-free in `Cbrt3Helpers`) and propagate the rational interval
  through the CF maps `x ↦ 1/(x - aᵢ)`; the endpoints stay small rationals
  (ratios of convergent numerators/denominators), and the tail floor pins the
  next quotient.

  * `cbrt3_a12 = 8`: sandwich `597449/414248 < ∛3 < 1865358/1293367` (12th/13th
    convergents), propagated through `a₀..a₁₁ = [1,2,3,1,4,1,5,1,1,6,2,5]`:
        x₁₂ ∈ (3/25, 1/8)   ⟹   1/x₁₂ ∈ (8, 25/3) ⊂ (8, 9)   ⟹   ⌊1/x₁₂⌋ = 8.
  * `cbrt3_a13 = 3`: sandwich `6193523/4294349 < ∛3 < 1865358/1293367`
    (14th/13th convergents), propagated through
    `a₀..a₁₂ = [1,2,3,1,4,1,5,1,1,6,2,5,8]`:
        x₁₃ ∈ (3/10, 1/3)   ⟹   1/x₁₃ ∈ (3, 10/3) ⊂ (3, 4)   ⟹   ⌊1/x₁₃⌋ = 3.

  Each intermediate bound is the exact image of a sandwich endpoint under the
  (monotone-decreasing) maps; every step discharges by `linarith` exactly as in
  the merged `cbrt3_a11`, so there is no new tactic/API surface.

  Off-line certification (this session).  Both interval propagations were checked
  with exact Python `fractions.Fraction` arithmetic (`verify_a12_floor.py`,
  `verify_a13_floor.py`): the sandwich cubes verify `lo³ < 3 < hi³`, every `x_k`
  stays strictly positive, and the final reciprocal intervals `(8, 25/3)` /
  `(3, 10/3)` are strictly inside `(8, 9)` / `(3, 4)`, forcing the floors to
  `8` / `3`.

  NOTE: BUILD-PENDING — written under a Docker blackout (host Docker socket
  unreachable: `docker run` rc=124, `docker image inspect` connect error).
  Deliberately UNREGISTERED in `Proofs.lean` and placed in a separate orphan
  file so it cannot affect the registered gallery build.  A post-blackout
  session should confirm via
  `./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04A12`
  and then fold `cbrt3_a12`, `cbrt3_a13` into `CubeRoot3IrrationalOQ04.lean`
  (immediately after `cbrt3_a11`), bumping the prefix from a₁₁ to a₁₃.
-/

import Proofs.CubeRoot3IrrationalOQ04
import Proofs.CubeRoot3IrrationalOQ04Helpers
import Mathlib

namespace CubeRoot3IrrationalOQ04

open CubeRoot3Irrational

-- The two deepest-quotient proofs propagate the largest convergent sandwiches
-- (numerators/denominators ≈ 10⁶) through eleven/twelve nested CF reciprocals;
-- the resulting `linarith` goals exceed the default 200000-heartbeat budget.
set_option maxHeartbeats 1600000

/-- **Thirteenth partial quotient `a₁₂ = 8`.**  The next term of the simple
continued fraction of `∛3` (OEIS A002945, 0-indexed prefix
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, …]`).  Extends `cbrt3_a11` by one
CF level, started from the tighter convergent sandwich
`597449/414248 < ∛3 < 1865358/1293367` (`Cbrt3Helpers`, the 12th/13th
convergents).  Propagating that interval through the eleven CF maps
`x ↦ 1/(x - aᵢ)` for `a₀..a₁₁ = [1,2,3,1,4,1,5,1,1,6,2,5]` lands the twelfth
tail in `1/x₁₂ ∈ (8, 25/3) ⊂ (8, 9)`, forcing the floor to be `8`. -/
theorem cbrt3_a12 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5)⌋ = (8 : ℤ) := by
  -- Step 1: `cbrt3 - 1 > 0` (from the S3 bound `4/3 < cbrt3`).
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  -- S13/S14a cubing bounds: the 12th & 13th convergents bracket `∛3`.
  have h_lo : (597449/414248 : ℝ) < cbrt3 :=
    Cbrt3Helpers.five_nine_seven_four_four_nine_over_four_one_four_two_four_eight_lt_cbrt3
  have h_hi : cbrt3 < (1865358/1293367 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_one_eight_six_five_three_five_eight_over_one_two_nine_three_three_six_seven
  -- Step 2: `y₁ := 1/(cbrt3-1)` satisfies `1293367/571991 < y₁ < 414248/183201`.
  have hy1_gt : (1293367/571991 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    linarith [h_hi]
  have hy1_lt : 1 / (cbrt3 - 1) < (414248/183201 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    linarith [h_lo]
  -- `x2 := y1 - 2` satisfies `149385/571991 < x2 < 47846/183201`.
  have hx2_gt : (149385/571991 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (47846/183201 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- `y2 := 1/x2` satisfies `183201/47846 < y2 < 571991/149385`.
  have hy2_gt : (183201/47846 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (571991/149385 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    linarith [hx2_gt]
  -- `x3 := y2 - 3` satisfies `39663/47846 < x3 < 123836/149385`.
  have hx3_gt : (39663/47846 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (123836/149385 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- `y3 := 1/x3` satisfies `149385/123836 < y3 < 47846/39663`.
  have hy3_gt : (149385/123836 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (47846/39663 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    linarith [hx3_gt]
  -- `x4 := y3 - 1` satisfies `25549/123836 < x4 < 8183/39663`.
  have hx4_gt : (25549/123836 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (8183/39663 : ℝ) := by linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- `y4 := 1/x4` satisfies `39663/8183 < y4 < 123836/25549`.
  have hy4_gt : (39663/8183 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
    rw [lt_div_iff₀ hpos4]
    linarith [hx4_lt]
  have hy4_lt : 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (123836/25549 : ℝ) := by
    rw [div_lt_iff₀ hpos4]
    linarith [hx4_gt]
  -- `x5 := y4 - 4` satisfies `6931/8183 < x5 < 21640/25549`.
  have hx5_gt : (6931/8183 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  have hx5_lt : 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 < (21640/25549 : ℝ) := by linarith
  have hpos5 : (0 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  -- `y5 := 1/x5` satisfies `25549/21640 < y5 < 8183/6931`.
  have hy5_gt : (25549/21640 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) := by
    rw [lt_div_iff₀ hpos5]
    linarith [hx5_lt]
  have hy5_lt : 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) < (8183/6931 : ℝ) := by
    rw [div_lt_iff₀ hpos5]
    linarith [hx5_gt]
  -- `x6 := y5 - 1` satisfies `3909/21640 < x6 < 1252/6931`.
  have hx6_gt : (3909/21640 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by linarith
  have hx6_lt : 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 < (1252/6931 : ℝ) := by linarith
  have hpos6 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by linarith
  -- `y6 := 1/x6` satisfies `6931/1252 < y6 < 21640/3909`.
  have hy6_gt : (6931/1252 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) := by
    rw [lt_div_iff₀ hpos6]
    linarith [hx6_lt]
  have hy6_lt : 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) < (21640/3909 : ℝ) := by
    rw [div_lt_iff₀ hpos6]
    linarith [hx6_gt]
  -- `x7 := y6 - 5` satisfies `671/1252 < x7 < 2095/3909`.
  have hx7_gt : (671/1252 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by linarith
  have hx7_lt : 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 < (2095/3909 : ℝ) := by linarith
  have hpos7 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by linarith
  -- `y7 := 1/x7` satisfies `3909/2095 < y7 < 1252/671`.
  have hy7_gt : (3909/2095 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) := by
    rw [lt_div_iff₀ hpos7]
    linarith [hx7_lt]
  have hy7_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) < (1252/671 : ℝ) := by
    rw [div_lt_iff₀ hpos7]
    linarith [hx7_gt]
  -- `x8 := y7 - 1` satisfies `1814/2095 < x8 < 581/671`.
  have hx8_gt : (1814/2095 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by linarith
  have hx8_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 < (581/671 : ℝ) := by linarith
  have hpos8 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by linarith
  -- `y8 := 1/x8` satisfies `671/581 < y8 < 2095/1814`.
  have hy8_gt : (671/581 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) := by
    rw [lt_div_iff₀ hpos8]
    linarith [hx8_lt]
  have hy8_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) < (2095/1814 : ℝ) := by
    rw [div_lt_iff₀ hpos8]
    linarith [hx8_gt]
  -- `x9 := y8 - 1` satisfies `90/581 < x9 < 281/1814`.
  have hx9_gt : (90/581 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by linarith
  have hx9_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 < (281/1814 : ℝ) := by linarith
  have hpos9 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by linarith
  -- `y9 := 1/x9` satisfies `1814/281 < y9 < 581/90`.
  have hy9_gt : (1814/281 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) := by
    rw [lt_div_iff₀ hpos9]
    linarith [hx9_lt]
  have hy9_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) < (581/90 : ℝ) := by
    rw [div_lt_iff₀ hpos9]
    linarith [hx9_gt]
  -- `x10 := y9 - 6` satisfies `128/281 < x10 < 41/90`.
  have hx10_gt : (128/281 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 := by linarith
  have hx10_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 < (41/90 : ℝ) := by linarith
  have hpos10 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 := by linarith
  -- `y10 := 1/x10` satisfies `90/41 < y10 < 281/128`.
  have hy10_gt : (90/41 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) := by
    rw [lt_div_iff₀ hpos10]
    linarith [hx10_lt]
  have hy10_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) < (281/128 : ℝ) := by
    rw [div_lt_iff₀ hpos10]
    linarith [hx10_gt]
  -- `x11 := y10 - 2` satisfies `8/41 < x11 < 25/128`.
  have hx11_gt : (8/41 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2 := by linarith
  have hx11_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2 < (25/128 : ℝ) := by linarith
  have hpos11 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2 := by linarith
  -- `y11 := 1/x11` satisfies `128/25 < y11 < 41/8`.
  have hy11_gt : (128/25 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) := by
    rw [lt_div_iff₀ hpos11]
    linarith [hx11_lt]
  have hy11_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) < (41/8 : ℝ) := by
    rw [div_lt_iff₀ hpos11]
    linarith [hx11_gt]
  -- `x12 := y11 - 5` satisfies `3/25 < x12 < 1/8`.
  have hx12_gt : (3/25 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5 := by linarith
  have hx12_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5 < (1/8 : ℝ) := by linarith
  have hpos12 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5 := by linarith
  -- Abbreviate the 12-deep tail `x₁₂` so the floor reasoning below operates on a
  -- single opaque variable rather than re-normalising the giant nested-reciprocal
  -- term (which otherwise blows the heartbeat budget). All three bounds above are
  -- already stated in terms of this expression, so `set` folds them automatically.
  set x12 := 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5 with hx12def
  -- Floor antisymmetry on `1/x₁₂ ∈ (8, 25/3) ⊂ (8, 9)`.
  apply le_antisymm
  · -- `⌊1/x₁₂⌋ ≤ 8`: from `1/x₁₂ < 9`.
    have hlt : 1 / x12 < (9 : ℝ) := by
      rw [div_lt_iff₀ hpos12]
      linarith [hx12_gt]
    have hflt : ⌊1 / x12⌋ < (9 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · -- `8 ≤ ⌊1/x₁₂⌋`: from `8 ≤ 1/x₁₂`.
    have hge : (8 : ℝ) ≤ 1 / x12 := by
      rw [le_div_iff₀ hpos12]
      linarith [hx12_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

/-- **Fourteenth partial quotient `a₁₃ = 3`.**  The next term of the simple
continued fraction of `∛3` after `cbrt3_a12` (OEIS A002945, 0-indexed prefix
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, …]`).  Same recipe as `cbrt3_a12`,
started from the tighter convergent sandwich
`6193523/4294349 < ∛3 < 1865358/1293367` (`Cbrt3Helpers`, the 14th/13th
convergents).  Propagating that interval through the twelve CF maps
`x ↦ 1/(x - aᵢ)` for `a₀..a₁₂ = [1,2,3,1,4,1,5,1,1,6,2,5,8]` lands the
thirteenth tail in `1/x₁₃ ∈ (3, 10/3) ⊂ (3, 4)`, forcing the floor to be `3`. -/
theorem cbrt3_a13 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5) - 8)⌋ = (3 : ℤ) := by
  have hpos1 : (0 : ℝ) < cbrt3 - 1 := by linarith [four_thirds_lt_cbrt3]
  have h_lo : (6193523/4294349 : ℝ) < cbrt3 :=
    Cbrt3Helpers.six_one_nine_three_five_two_three_over_four_two_nine_four_three_four_nine_lt_cbrt3
  have h_hi : cbrt3 < (1865358/1293367 : ℝ) :=
    Cbrt3Helpers.cbrt3_lt_one_eight_six_five_three_five_eight_over_one_two_nine_three_three_six_seven
  -- `y₁ := 1/(cbrt3-1)` satisfies `1293367/571991 < y₁ < 4294349/1899174`.
  have hy1_gt : (1293367/571991 : ℝ) < 1 / (cbrt3 - 1) := by
    rw [lt_div_iff₀ hpos1]
    linarith [h_hi]
  have hy1_lt : 1 / (cbrt3 - 1) < (4294349/1899174 : ℝ) := by
    rw [div_lt_iff₀ hpos1]
    linarith [h_lo]
  -- `x2 := y1 - 2` satisfies `149385/571991 < x2 < 496001/1899174`.
  have hx2_gt : (149385/571991 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  have hx2_lt : 1 / (cbrt3 - 1) - 2 < (496001/1899174 : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 1 / (cbrt3 - 1) - 2 := by linarith
  -- `y2 := 1/x2` satisfies `1899174/496001 < y2 < 571991/149385`.
  have hy2_gt : (1899174/496001 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) := by
    rw [lt_div_iff₀ hpos2]
    linarith [hx2_lt]
  have hy2_lt : 1 / (1 / (cbrt3 - 1) - 2) < (571991/149385 : ℝ) := by
    rw [div_lt_iff₀ hpos2]
    linarith [hx2_gt]
  -- `x3 := y2 - 3` satisfies `411171/496001 < x3 < 123836/149385`.
  have hx3_gt : (411171/496001 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  have hx3_lt : 1 / (1 / (cbrt3 - 1) - 2) - 3 < (123836/149385 : ℝ) := by linarith
  have hpos3 : (0 : ℝ) < 1 / (1 / (cbrt3 - 1) - 2) - 3 := by linarith
  -- `y3 := 1/x3` satisfies `149385/123836 < y3 < 496001/411171`.
  have hy3_gt : (149385/123836 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) := by
    rw [lt_div_iff₀ hpos3]
    linarith [hx3_lt]
  have hy3_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) < (496001/411171 : ℝ) := by
    rw [div_lt_iff₀ hpos3]
    linarith [hx3_gt]
  -- `x4 := y3 - 1` satisfies `25549/123836 < x4 < 84830/411171`.
  have hx4_gt : (25549/123836 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  have hx4_lt : 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 < (84830/411171 : ℝ) := by linarith
  have hpos4 : (0 : ℝ) < 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1 := by linarith
  -- `y4 := 1/x4` satisfies `411171/84830 < y4 < 123836/25549`.
  have hy4_gt : (411171/84830 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) := by
    rw [lt_div_iff₀ hpos4]
    linarith [hx4_lt]
  have hy4_lt : 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) < (123836/25549 : ℝ) := by
    rw [div_lt_iff₀ hpos4]
    linarith [hx4_gt]
  -- `x5 := y4 - 4` satisfies `71851/84830 < x5 < 21640/25549`.
  have hx5_gt : (71851/84830 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  have hx5_lt : 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 < (21640/25549 : ℝ) := by linarith
  have hpos5 : (0 : ℝ) < 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4 := by linarith
  -- `y5 := 1/x5` satisfies `25549/21640 < y5 < 84830/71851`.
  have hy5_gt : (25549/21640 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) := by
    rw [lt_div_iff₀ hpos5]
    linarith [hx5_lt]
  have hy5_lt : 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) < (84830/71851 : ℝ) := by
    rw [div_lt_iff₀ hpos5]
    linarith [hx5_gt]
  -- `x6 := y5 - 1` satisfies `3909/21640 < x6 < 12979/71851`.
  have hx6_gt : (3909/21640 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by linarith
  have hx6_lt : 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 < (12979/71851 : ℝ) := by linarith
  have hpos6 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1 := by linarith
  -- `y6 := 1/x6` satisfies `71851/12979 < y6 < 21640/3909`.
  have hy6_gt : (71851/12979 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) := by
    rw [lt_div_iff₀ hpos6]
    linarith [hx6_lt]
  have hy6_lt : 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) < (21640/3909 : ℝ) := by
    rw [div_lt_iff₀ hpos6]
    linarith [hx6_gt]
  -- `x7 := y6 - 5` satisfies `6956/12979 < x7 < 2095/3909`.
  have hx7_gt : (6956/12979 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by linarith
  have hx7_lt : 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 < (2095/3909 : ℝ) := by linarith
  have hpos7 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5 := by linarith
  -- `y7 := 1/x7` satisfies `3909/2095 < y7 < 12979/6956`.
  have hy7_gt : (3909/2095 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) := by
    rw [lt_div_iff₀ hpos7]
    linarith [hx7_lt]
  have hy7_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) < (12979/6956 : ℝ) := by
    rw [div_lt_iff₀ hpos7]
    linarith [hx7_gt]
  -- `x8 := y7 - 1` satisfies `1814/2095 < x8 < 6023/6956`.
  have hx8_gt : (1814/2095 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by linarith
  have hx8_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 < (6023/6956 : ℝ) := by linarith
  have hpos8 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1 := by linarith
  -- `y8 := 1/x8` satisfies `6956/6023 < y8 < 2095/1814`.
  have hy8_gt : (6956/6023 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) := by
    rw [lt_div_iff₀ hpos8]
    linarith [hx8_lt]
  have hy8_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) < (2095/1814 : ℝ) := by
    rw [div_lt_iff₀ hpos8]
    linarith [hx8_gt]
  -- `x9 := y8 - 1` satisfies `933/6023 < x9 < 281/1814`.
  have hx9_gt : (933/6023 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by linarith
  have hx9_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 < (281/1814 : ℝ) := by linarith
  have hpos9 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1 := by linarith
  -- `y9 := 1/x9` satisfies `1814/281 < y9 < 6023/933`.
  have hy9_gt : (1814/281 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) := by
    rw [lt_div_iff₀ hpos9]
    linarith [hx9_lt]
  have hy9_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) < (6023/933 : ℝ) := by
    rw [div_lt_iff₀ hpos9]
    linarith [hx9_gt]
  -- `x10 := y9 - 6` satisfies `128/281 < x10 < 425/933`.
  have hx10_gt : (128/281 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 := by linarith
  have hx10_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 < (425/933 : ℝ) := by linarith
  have hpos10 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6 := by linarith
  -- `y10 := 1/x10` satisfies `933/425 < y10 < 281/128`.
  have hy10_gt : (933/425 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) := by
    rw [lt_div_iff₀ hpos10]
    linarith [hx10_lt]
  have hy10_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) < (281/128 : ℝ) := by
    rw [div_lt_iff₀ hpos10]
    linarith [hx10_gt]
  -- `x11 := y10 - 2` satisfies `83/425 < x11 < 25/128`.
  have hx11_gt : (83/425 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2 := by linarith
  have hx11_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2 < (25/128 : ℝ) := by linarith
  have hpos11 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2 := by linarith
  -- `y11 := 1/x11` satisfies `128/25 < y11 < 425/83`.
  have hy11_gt : (128/25 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) := by
    rw [lt_div_iff₀ hpos11]
    linarith [hx11_lt]
  have hy11_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) < (425/83 : ℝ) := by
    rw [div_lt_iff₀ hpos11]
    linarith [hx11_gt]
  -- `x12 := y11 - 5` satisfies `3/25 < x12 < 10/83`.
  have hx12_gt : (3/25 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5 := by linarith
  have hx12_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5 < (10/83 : ℝ) := by linarith
  have hpos12 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5 := by linarith
  -- `y12 := 1/x12` satisfies `83/10 < y12 < 25/3`.
  have hy12_gt : (83/10 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5) := by
    rw [lt_div_iff₀ hpos12]
    linarith [hx12_lt]
  have hy12_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5) < (25/3 : ℝ) := by
    rw [div_lt_iff₀ hpos12]
    linarith [hx12_gt]
  -- `x13 := y12 - 8` satisfies `3/10 < x13 < 1/3`.
  have hx13_gt : (3/10 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5) - 8 := by linarith
  have hx13_lt : 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5) - 8 < (1/3 : ℝ) := by linarith
  have hpos13 : (0 : ℝ) < 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5) - 8 := by linarith
  -- Abbreviate the 13-deep tail `x₁₃` so the floor reasoning below operates on a
  -- single opaque variable rather than re-normalising the giant nested-reciprocal
  -- term (which otherwise blows the heartbeat budget). All three bounds above are
  -- already stated in terms of this expression, so `set` folds them automatically.
  set x13 := 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) - 5) - 8 with hx13def
  -- Floor antisymmetry on `1/x₁₃ ∈ (3, 10/3) ⊂ (3, 4)`.
  apply le_antisymm
  · have hlt : 1 / x13 < (4 : ℝ) := by
      rw [div_lt_iff₀ hpos13]
      linarith [hx13_gt]
    have hflt : ⌊1 / x13⌋ < (4 : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast hlt
    omega
  · have hge : (3 : ℝ) ≤ 1 / x13 := by
      rw [le_div_iff₀ hpos13]
      linarith [hx13_lt]
    rw [Int.le_floor]
    exact_mod_cast hge

end CubeRoot3IrrationalOQ04
