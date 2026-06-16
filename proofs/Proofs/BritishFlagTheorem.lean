import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-
# The British Flag Theorem

## What This Proves
For a rectangle `ABCD` and **any** point `P` in the plane,
  `PA² + PC² = PB² + PD²`,
i.e. the sums of squared distances to opposite corners are equal.

The name comes from the Union-Jack-like figure of the four segments drawn from
an interior point to the corners.

## Key Mathematical Content
The identity is **not** true for a general parallelogram — it characterises the
right angle. Writing the rectangle as `A`, `B = A + u`, `C = A + u + v`,
`D = A + v`, a direct expansion gives

  (PA² + PC²) − (PB² + PD²) = 2 ⟪u, v⟫,

so the two sums agree **exactly when** `u ⊥ v`, i.e. when `ABCD` is a rectangle.
The perpendicularity hypothesis is therefore the whole substance of the theorem,
and the proof is a single `linear_combination` against it.

## Approach
1. `british_flag_coords`: the real-coordinate identity, proved by
   `linear_combination 2 * hperp` (the `2⟪u,v⟫` defect cancels against `hperp`).
2. `british_flag`: the complex-number / metric-distance statement, obtained by
   feeding the real and imaginary parts of the points into the coordinate lemma.

## Status
- [x] Coordinate identity (over ℝ)
- [x] Complex / `dist` form
- [x] Sharpness witness (parallelogram counterexample)
- [x] Complete — 0 sorries, 0 axioms

## Mathlib Dependencies
- `Complex.dist_eq_re_im` : `dist z w = Real.sqrt ((z.re-w.re)² + (z.im-w.im)²)`
- `Real.sq_sqrt`          : `0 ≤ a → Real.sqrt a ^ 2 = a`
- `Complex.sub_re`, `Complex.sub_im`, `Complex.add_re`, `Complex.add_im`
-/

set_option linter.unusedVariables false

namespace BritishFlag

-- ============================================================
-- PART 1: The Coordinate Identity (the heart of the theorem)
-- ============================================================

/-- **British Flag Theorem (coordinate form).**

The rectangle has corners `A = (ax, ay)`, `B = A + u`, `C = A + u + v`,
`D = A + v`, with edge vectors `u = (ux, uy)` and `v = (vx, vy)`. The
hypothesis `hperp : ux*vx + uy*vy = 0` says `u ⊥ v` (the right angle that makes
`ABCD` a rectangle). For any point `P = (px, py)`:

  `PA² + PC² = PB² + PD²`.

The difference of the two sides expands to exactly `2 (ux*vx + uy*vy)`, so the
proof is `linear_combination 2 * hperp`. -/
theorem british_flag_coords (px py ax ay ux uy vx vy : ℝ)
    (hperp : ux * vx + uy * vy = 0) :
    ((px - ax) ^ 2 + (py - ay) ^ 2)
        + ((px - (ax + ux + vx)) ^ 2 + (py - (ay + uy + vy)) ^ 2)
      = ((px - (ax + ux)) ^ 2 + (py - (ay + uy)) ^ 2)
        + ((px - (ax + vx)) ^ 2 + (py - (ay + vy)) ^ 2) := by
  linear_combination 2 * hperp

-- ============================================================
-- PART 2: The Complex / Metric-Distance Form
-- ============================================================

/-- **British Flag Theorem** in the complex plane with metric distance.

The rectangle `ABCD` is encoded by
* `hrect : C = B + D - A` (so `ABCD` is a parallelogram), and
* `hperp` : the edges `B - A` and `D - A` are orthogonal as vectors in `ℝ²`,
  i.e. `(B-A)·(D-A) = 0`.

Then for any point `P : ℂ`:

  `dist P A ^ 2 + dist P C ^ 2 = dist P B ^ 2 + dist P D ^ 2`.

Reduces to `british_flag_coords` on the real and imaginary parts. -/
theorem british_flag (A B C D P : ℂ)
    (hrect : C = B + D - A)
    (hperp : (B - A).re * (D - A).re + (B - A).im * (D - A).im = 0) :
    dist P A ^ 2 + dist P C ^ 2 = dist P B ^ 2 + dist P D ^ 2 := by
  have hsq : ∀ z w : ℂ, dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
    intro z w
    rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]
  have key := british_flag_coords P.re P.im A.re A.im
    (B - A).re (B - A).im (D - A).re (D - A).im hperp
  rw [hsq, hsq, hsq, hsq]
  subst hrect
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im] at key ⊢
  linear_combination key

-- ============================================================
-- PART 3: Sharpness — the right angle is necessary
-- ============================================================

/-- The identity fails for a non-rectangular parallelogram, confirming that the
perpendicularity hypothesis is essential.

Take edges `u = (2, 0)`, `v = (1, 1)` (so `u·v = 2 ≠ 0`, a non-right angle) with
`A = P = 0`. Then `PA² + PC² = 0 + 10 = 10` while `PB² + PD² = 4 + 2 = 6`. The
defect is exactly `2 (u·v) = 4`. -/
theorem british_flag_needs_right_angle :
    ∃ (px py ax ay ux uy vx vy : ℝ), ux * vx + uy * vy ≠ 0 ∧
      ((px - ax) ^ 2 + (py - ay) ^ 2)
          + ((px - (ax + ux + vx)) ^ 2 + (py - (ay + uy + vy)) ^ 2)
        ≠ ((px - (ax + ux)) ^ 2 + (py - (ay + uy)) ^ 2)
          + ((px - (ax + vx)) ^ 2 + (py - (ay + vy)) ^ 2) := by
  exact ⟨0, 0, 0, 0, 2, 0, 1, 1, by norm_num, by norm_num⟩

-- ============================================================
-- Export main results
-- ============================================================

#check @british_flag_coords
#check @british_flag
#check @british_flag_needs_right_angle

end BritishFlag
